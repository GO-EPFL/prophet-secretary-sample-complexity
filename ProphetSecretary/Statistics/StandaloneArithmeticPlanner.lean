import ProphetSecretary.Statistics.CalibratedPolynomialWork
import ProphetSecretary.Statistics.ArithmeticCalibrationTapes

/-!
# Standalone arithmetic planning

The selected recursive level uses the last slice of a finite tape.
Every primitive uniform is independent; the address tables and the
allocation of all tape slots are included in the work bound.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Model ProphetSecretary.Probability
open ProphetSecretary.Statistics.Calibration

variable {n : ℕ} {k : Fin n → ℕ}

noncomputable def arithmeticStandaloneTapeLaw (n C r : ℕ) :
    Measure (ArithmeticPlannerUniformTape n C r) :=
  Measure.pi fun _ => Measure.pi fun _ => Instance.uniformClock

def countedArithmeticStandaloneQuery {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (rows : Vector (List K) n)
    (x : ScalarPlannerListState n K) (h p : K)
    (Hlevel : ∃ j : ℕ, (1/4 : K)^j≤scalarPlannerPrecisionRatio (storedScalarPlannerWeight rows x) h)
    (Hconf : ∃ j : ℕ, (1/4 : K)^j≤p)
    (t : Fin (multilevelBankSlots (confidenceCopyCount p Hconf)
      (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1) → Fin (3*n+2) → K) :
    MedianCopiesResult K :=
  let C := confidenceCopyCount p Hconf
  let r := (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1
  let tape := countedMultilevelBankFromTape C r (fun j => plannerSeedFromCoordinates n (t j))
  let q := countedScalarPlannerQuery rows x h p Hlevel Hconf (tape.1 (Fin.last r))
  {q with work := q.work+tape.2+multilevelBankSlots C r*(arithmeticTransitionSeedWork n+3*n+5)+4}

private lemma arithmeticStandaloneQuery_work (rows : Vector (List ℝ) n) (m : ℕ)
    (hRows : ∀ i, (rows.get i).length≤m) (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup)
    (h p : ℝ)
    (Hlevel : ∃ j : ℕ, (1/4 : ℝ)^j≤scalarPlannerPrecisionRatio (storedScalarPlannerWeight rows x) h)
    (Hconf : ∃ j : ℕ, (1/4 : ℝ)^j≤p)
    (t : ArithmeticPlannerUniformTape n (confidenceCopyCount p Hconf)
      (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1) :
    let C := confidenceCopyCount p Hconf
    let r := (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1
    (countedArithmeticStandaloneQuery rows x h p Hlevel Hconf t).work≤
      20*calibrationFullQueryBound n m r C := by
  let C := confidenceCopyCount p Hconf
  let r := (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hlevel).1
  let tape := countedMultilevelBankFromTape C r (fun j => plannerSeedFromCoordinates n (t j))
  let q := countedScalarPlannerQuery rows x h p Hlevel Hconf (tape.1 (Fin.last r))
  have hq : q.work≤calibrationBankCallBound n m r C := by
    have e := countedScalarPlannerQuery_work rows m hRows x hx h p Hlevel Hconf (tape.1 (Fin.last r))
    dsimp only at e
    unfold calibrationBankCallBound
    have hnm : 40*(n+1)*(m+1)≤46*(n+1)*(m+1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
    change q.work≤_
    change q.work≤40*(n+1)*(m+1)+80*(n+1)+
      C*(400*scalarPlannerPrimitiveBound n m*16^r+3)+10*(C+1)^2+(3*r+28) at e
    omega
  have ht : tape.2≤360*(r+1)^4 := countedMultilevelBankFromTape_work C r _
  have hSeed : arithmeticTransitionSeedWork n+3*n+5≤15*(3*n+2) := by
    unfold arithmeticTransitionSeedWork
    omega
  have hSlots : multilevelBankSlots C r*(arithmeticTransitionSeedWork n+3*n+5)≤
      15*(5*C*16^r*(3*n+2)) := by
    calc
      _ ≤ (5*C*16^r)*(15*(3*n+2)) := Nat.mul_le_mul (multilevelBankSlots_le C r) hSeed
      _ = _ := by ring
  change q.work+tape.2+multilevelBankSlots C r*(arithmeticTransitionSeedWork n+3*n+5)+4≤_
  change _≤20*calibrationFullQueryBound n m r C
  unfold calibrationFullQueryBound
  omega

set_option maxHeartbeats 260000 in
/-- Paper label `thm:scalar-planner`, arithmetic implementation. The
depth and copy certificates are consequences of the stated parameter
ranges. The cost covers the whole finite tape on every outcome. -/
theorem standaloneArithmeticScalarPlanner [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0≤y i j) (hcap : ∀ i j, y i j≤1)
    (m : ℕ) (hk : ∀ i, k i≤m) (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup)
    (hu : x.2.1∈Icc (0:ℝ) 1) (hz : x.2.2∈Icc (0:ℝ) 4)
    (h p : ℝ) (hh : h∈Ioo (0:ℝ) 1) (hp : p∈Ioo (0:ℝ) (1/2)) :
    ∃ (HL : ∃ j : ℕ, (1/4 : ℝ)^j≤scalarPlannerPrecisionRatio
        (storedScalarPlannerWeight (plannerStoredRows y) x) h)
      (HC : ∃ j : ℕ, (1/4 : ℝ)^j≤p),
      let C := confidenceCopyCount p HC
      let r := (countedScalarPlannerLevel (storedScalarPlannerWeight (plannerStoredRows y) x) h HL).1
      let f := countedArithmeticStandaloneQuery (plannerStoredRows y) x h p HL HC
      let Q := empiricalPlannerInstance y hy
      Measurable (fun t => (f t).value) ∧
      (arithmeticStandaloneTapeLaw n C r).real
        {t | h < |(f t).value-Q.continuationValue x.1.toFinset x.2.1 1 x.2.2|}≤p ∧
      ∀ t, ((f t).work : ℝ)≤
        (32000000000:ℝ)*6400^4*((n:ℝ)+m+2)^3*(1+Real.log (1/p)/Real.log 4)^2*
          Real.exp (32*Q.positiveCount)/h^8 := by
  let rows := plannerStoredRows y
  have hβ : 1≤storedScalarPlannerWeight rows x := by
    rw [storedScalarPlannerWeight_value y x hx]
    exact scalarPlannerWeight_ge_one _ _
  let HL := scalarPlannerPrecision_exists hβ hh
  let HC := exists_confidence_level hp.1 (hp.2.trans (by norm_num))
  refine ⟨HL,HC,?_⟩
  dsimp only
  let C := confidenceCopyCount p HC
  let r := (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h HL).1
  let call := countedScalarPlannerQuery rows x h p HL HC
  let v := (empiricalPlannerInstance y hy).continuationValue x.1.toFinset x.2.1 1 x.2.2
  let decode : ArithmeticPlannerUniformTape n C r → Fin C → MultilevelTree (PlannerFieldSeed n ℝ) r :=
    fun t => arithmeticPlannerBankFromUniformTape n C r t (Fin.last r)
  have hM : MeasurePreserving decode (arithmeticStandaloneTapeLaw n C r)
      (Measure.pi fun _ : Fin C => multilevelTreeLaw (plannerUniformSeedLaw n) r) := (measurePreserving_eval (μ := fun l : Fin (r+1) => Measure.pi fun _ : Fin C =>
    multilevelTreeLaw (plannerUniformSeedLaw n) l.val) (Fin.last r)).comp
      (measurePreserving_arithmeticPlannerBankFromUniformTape n C r)
  have hC := countedScalarPlannerQuery_correct y hy hcap m hk x hx h p hh hp HL HC
  dsimp only at hC
  have hv : scalarPlannerValue y hy (scalarPlannerListInterpret x)=v :=
    scalarPlannerValue_eq_continuation y hy x.1.toFinset hu hz
  rw [hv] at hC
  change Measurable (fun t => (call (decode t)).value) ∧
    (arithmeticStandaloneTapeLaw n C r).real {t | h < |(call (decode t)).value-v|}≤p ∧ _
  refine ⟨hC.1.comp hM.measurable,?_,?_⟩
  · let E := {s | h < |(call s).value-v|}
    have hE : MeasurableSet E := measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (hC.1.sub_const v))
    change (arithmeticStandaloneTapeLaw n C r).real (decode ⁻¹' E)≤_
    rw [← map_measureReal_apply hM.measurable hE,hM.map_eq]
    exact hC.2.1
  · intro t
    have hW := (arithmeticStandaloneQuery_work rows m (fun i => by simpa [rows] using hk i)
      x hx h p HL HC t).trans (Nat.mul_le_mul_left _ (calibrationFullQueryBound_poly n m r C))
    have hW' : ((countedArithmeticStandaloneQuery rows x h p HL HC t).work : ℝ)≤
        (2000000000:ℝ)*((n:ℝ)+m+2)^3*((C:ℝ)+1)^2*(16:ℝ)^r := by
      have hw : (countedArithmeticStandaloneQuery rows x h p HL HC t).work≤
          2000000000*(n+m+2)^3*(C+1)^2*16^r := by
        rw [show (2000000000:ℕ)=20*100000000 by decide]
        simpa only [Nat.mul_assoc] using hW
      exact_mod_cast hw
    let P := Real.log (1/p)/Real.log 4
    have hP : 0≤P := div_nonneg (Real.log_nonneg ((one_le_div hp.1).2 (hp.2.trans (by norm_num)).le))
      (Real.log_nonneg (by norm_num))
    have hC' : (C:ℝ)<2*P+3 := hC.2.2.2.1
    have hCP : (C:ℝ)+1≤4*(1+P) := by linarith only [hP,hC']
    have hR := countedScalarPlannerLevel_tree_factor_exp y hy x hx h hh HL
    change _≤(32000000000:ℝ)*6400^4*((n:ℝ)+m+2)^3*(1+P)^2*
      Real.exp (32*(empiricalPlannerInstance y hy).positiveCount)/h^8
    calc
      _ ≤ _ := hW'
      _ ≤ (2000000000:ℝ)*((n:ℝ)+m+2)^3*(4*(1+P))^2*
          ((6400:ℝ)^4*Real.exp (32*(empiricalPlannerInstance y hy).positiveCount)/h^8) := by
        have hc2 := pow_le_pow_left₀ (by positivity : 0≤(C:ℝ)+1) hCP 2
        exact mul_le_mul (mul_le_mul_of_nonneg_left hc2 (by positivity)) hR
          (by positivity) (by positivity)
      _ = _ := by ring

end ProphetSecretary.Statistics
