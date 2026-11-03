import ProphetSecretary.Statistics.PlannerPrimitiveHeight
import ProphetSecretary.Statistics.ScalarPlannerWork
import ProphetSecretary.Analysis.MultilevelSeedMap

/-!
# Rational height of the counted scalar recursion

Each child horizon multiplies by one grid fraction. Its height grows by at
most the grid precision along an edge. The payoff scan has additive height
growth in its recursive argument, so the bound follows the actual finite
tree rather than multiplying the row size at every level.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ}

lemma rationalHeight_unitClamp {q : ℚ} {B : ℕ} (hq : RationalHeight q B) :
    RationalHeight (max 0 (min 1 q)) B :=
  ((rationalHeight_zero.mono (Nat.zero_le B)).max
    ((rationalHeight_one.mono (Nat.zero_le B)).min hq)).mono (by simp)

lemma rationalHeight_durationClamp {q : ℚ} {B : ℕ} (hB : 2 ≤ B) (hq : RationalHeight q B) :
    RationalHeight (max 0 (min 4 q)) B :=
  ((rationalHeight_zero.mono (Nat.zero_le B)).max
    ((rationalHeight_four.mono hB).min hq)).mono (by simp)

def plannerPrimitiveHeight (n m Y P Pp U Z b R : ℕ) : ℕ :=
  Z+U+R*b+2*(n*(Pp+3))+m*(Y+1)+2*P+5

lemma countedScalarPlannerFrame_height (p : Fin n → ℚ) (Pp U Z : ℕ)
    (hp : ∀ i, RationalHeight (p i) Pp) (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup)
    (hu : RationalHeight x.2.1 U) (hz : RationalHeight x.2.2 Z) (hZ : 2 ≤ Z) :
    let q := (countedScalarPlannerFrame p x).1
    RationalHeight q.time U ∧ RationalHeight q.durationWeight Z ∧
      RationalHeight q.weight (n*(Pp+3)) ∧ RationalHeight q.emptyValue (Z+U) ∧
      RationalHeight q.offset (Z+U+n*(Pp+3)) ∧ RationalHeight q.coefficient (2*(n*(Pp+3))+3) := by
  let w := n*(Pp+3)
  have hβ := countedPlannerWeight_active_height p Pp hp x.1 hx
  have hu' := rationalHeight_unitClamp hu
  have hz' := rationalHeight_durationClamp hZ hz
  have hWait := hz'.mul hu'
  refine ⟨hu',hz',hβ,hWait,hWait.div hβ,?_⟩
  have hk := (hβ.sub rationalHeight_one).div (rationalHeight_four.mul hβ)
  exact hk.mono (by omega)

/-- The executable counted evaluator uses rational integers of polynomial
length in its finite tree size and stored-input length. This conclusion is
about the normalized numerator and denominator of each recursive output. -/
theorem countedScalarPlannerRecursion_height {Seed : Type*}
    (rows : Vector (List ℚ) n) (p : Fin n → ℚ) (F : Seed → PlannerFieldSeed n ℚ)
    (m Y P Pp U Z b R : ℕ)
    (hm : ∀ i, (rows.get i).length ≤ m) (hP : m ≤ 2^P)
    (hY : ∀ i q, q ∈ rows.get i → RationalHeight q Y) (hp : ∀ i, RationalHeight (p i) Pp)
    (hZ : 2 ≤ Z) (hF : ∀ s i, RationalHeight ((F s).2.2.1 i) b)
    (r : ℕ) (hr : r ≤ R) (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup)
    (hu : RationalHeight x.2.1 (U+(R-r)*b)) (hz : RationalHeight x.2.2 Z)
    (t : MultilevelTree Seed r) :
    RationalHeight ((countedScalarPlannerRecursion rows p).estimate r x (multilevelTreeMap F r t)).1
      (16*(plannerPrimitiveHeight n m Y P Pp U Z b R+R+1)*multilevelTreeWork r t) := by
  let D := (countedScalarPlannerRecursion rows p).toRecursion.mapSeed F
  let B := plannerPrimitiveHeight n m Y P Pp U Z b R
  let G := fun (j : ℕ) (q : ScalarPlannerListState n ℚ) =>
    q.1.Nodup ∧ RationalHeight q.2.1 (U+(R-j)*b) ∧ RationalHeight q.2.2 Z
  have hframe (j : ℕ) (q : ScalarPlannerListState n ℚ) (hq : G j q) :=
    countedScalarPlannerFrame_height p Pp _ Z hp q hq.1 hq.2.1 hq.2.2 hZ
  have hSample (j : ℕ) (q : ScalarPlannerListState n ℚ) (hq : G j q) (s : Seed) :
      (D.sample q s).2.2.Nodup ∧ RationalHeight (D.sample q s).2.1 b := by
    let frame := (countedScalarPlannerFrame p q).1
    change (countedPlannerUniformSampler frame.active p (F s)).1.2.2.Nodup ∧
      RationalHeight (countedPlannerUniformSampler frame.active p (F s)).1.2.1 b
    exact ⟨countedPlannerUniformSampler_nodup frame.active
      (countedScalarPlannerFrame_active_nodup p q hq.1) p (F s),
      countedPlannerUniformSampler_fraction_height frame.active p (F s) b (hF s)⟩
  have hBase (j : ℕ) (q : ScalarPlannerListState n ℚ) (_ : j ≤ R) (hq : G j q) :
      RationalHeight (D.emptyValue q) B ∧ RationalHeight (D.offset q) B ∧ RationalHeight (D.coefficient q) B := by
    have h := hframe j q hq
    have hM := Nat.mul_le_mul_right b (Nat.sub_le R j)
    refine ⟨h.2.2.2.1.mono ?_, h.2.2.2.2.1.mono ?_, h.2.2.2.2.2.mono ?_⟩ <;>
      dsimp [B, plannerPrimitiveHeight] <;> omega
  have hPay (j : ℕ) (q : ScalarPlannerListState n ℚ) (s : Seed) (a : ℚ) (A : ℕ) (_ : j ≤ R)
      (hq : G j q) (ha : RationalHeight a A) : RationalHeight (D.payoff q (D.sample q s) a) (B+A) := by
    have ho := (hSample j q hq s).1
    have h := countedScalarPlannerPayoff_height rows p (D.sample q s) a m Y P Pp A hm hP hY hp ho ha
    exact h.mono (by dsimp [B, plannerPrimitiveHeight]; omega)
  have hChild (j : ℕ) (q : ScalarPlannerListState n ℚ) (s : Seed) (l : ℕ) (hjr : j ≤ R)
      (hq : G j q) (_ : D.isEmpty q = false) (hl : l < j) : G l (D.child q (D.sample q s)) := by
    have hs := hSample j q hq s
    have h := hframe j q hq
    have hU := h.1.mul (rationalHeight_unitClamp hs.2)
    have hM := Nat.mul_le_mul_right b (show R-j+1 ≤ R-l by omega)
    rw [Nat.add_mul, Nat.one_mul] at hM
    exact ⟨hs.1,hU.mono (by omega),h.2.1⟩
  rw [CountedPlannerRecursion.estimate_value, ← multilevelEstimate_mapSeed]
  exact multilevelEstimate_rationalHeight D G R B hBase hPay hChild r hr x ⟨hx,hu,hz⟩ t

/-- The fair-bit dyadic reservoir meets the seed-height hypothesis for the
actual rational sampler. -/
theorem countedScalarPlannerRecursion_fair_height (rows : Vector (List ℚ) n) (p : Fin n → ℚ)
    (m Y P Pp U Z b r : ℕ)
    (hm : ∀ i, (rows.get i).length ≤ m) (hP : m ≤ 2^P)
    (hY : ∀ i q, q ∈ rows.get i → RationalHeight q Y) (hp : ∀ i, RationalHeight (p i) Pp)
    (hZ : 2 ≤ Z) (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup)
    (hu : RationalHeight x.2.1 U) (hz : RationalHeight x.2.2 Z)
    (t : MultilevelTree (PlannerFairSeed n b) r) :
    RationalHeight ((countedScalarPlannerRecursion rows p).estimate r x
      (multilevelTreeMap (fun s => (countedPlannerFairSeed b s).1) r t)).1
      (64*(plannerPrimitiveHeight n m Y P Pp U Z b r+r+1)*16^r) := by
  have h := countedScalarPlannerRecursion_height rows p (fun s => (countedPlannerFairSeed b s).1)
    m Y P Pp U Z b r hm hP hY hp hZ (countedPlannerFairSeed_fraction_height b) r le_rfl x hx
    (by simpa only [Nat.sub_self, zero_mul, Nat.add_zero] using hu) hz t
  have hw : multilevelTreeWork r t ≤ 4*16^r := by exact_mod_cast multilevelTreeWork_le r t
  exact h.mono ((Nat.mul_le_mul_left _ hw).trans_eq (by ring))

end ProphetSecretary.Statistics
