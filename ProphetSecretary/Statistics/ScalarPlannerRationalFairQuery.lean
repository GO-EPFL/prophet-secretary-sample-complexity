import ProphetSecretary.Statistics.PlannerRationalDecode
import ProphetSecretary.Statistics.ScalarPlannerFairQuery

/-!
# The rational scalar query driven by fair bits

The rounded operator analysis applies to the rational computation
because decoding, recursive evaluation, and median selection agree
pointwise with the real interpretation.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ} {k : Fin n → ℕ}

def countedRationalFairQueryAtLevel (rows : Vector (List ℚ) n) (x : ScalarPlannerListState n ℚ)
    (r : ℕ) (p : ℚ) (H : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p) (b : ℕ)
    (bits : Fin (confidenceCopyCount p H) → MultilevelTree (PlannerFairSeed n b) r) :
    MedianCopiesResult ℚ :=
  let t := fun j => multilevelTreeMap (fun s => (countedStoredPlannerFairSeed b s).1) r (bits j)
  let q := countedScalarPlannerQueryAtLevel rows x r p H t
  let C := confidenceCopyCount p H
  let lim := countedBitGridSize (4*r)
  { q with work := q.work + 4*C*lim.1*(plannerFairDecodeBound n b+40) + lim.2+4*C+20 }

theorem countedRationalFairQueryAtLevel_work (rows : Vector (List ℚ) n) (m : ℕ)
    (hRows : ∀ i, (rows.get i).length ≤ m) (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup)
    (r : ℕ) (p : ℚ) (H : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p) (b : ℕ)
    (bits : Fin (confidenceCopyCount p H) → MultilevelTree (PlannerFairSeed n b) r) :
    let C := confidenceCopyCount p H
    (countedRationalFairQueryAtLevel rows x r p H b bits).work ≤
      20*(n+1)*(m+1)+40*(n+1)+
        C*(400*scalarPlannerPrimitiveBound n m*16^r+3)+10*(C+1)^2+45 +
        4*C*16^r*(plannerFairDecodeBound n b+40)+8*r+4*C+21 := by
  dsimp only
  have hLim : (countedBitGridSize (4*r)).1 = 16^r := by
    rw [countedBitGridSize_value, pow_mul]
    norm_num
  have hw := countedScalarPlannerQueryAtLevel_work rows m hRows x hx r p H
    (fun j => multilevelTreeMap (fun s => (countedStoredPlannerFairSeed b s).1) r (bits j))
  simp only [countedRationalFairQueryAtLevel, hLim, countedBitGridSize_work]
  omega

theorem countedRationalFairQueryAtLevel_value (y : (i : Fin n) → Fin (k i) → ℚ)
    (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup) (r : ℕ) (p : ℚ)
    (Hq : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p) (Hr : ∃ j : ℕ, (1/4 : ℝ)^j ≤ (p : ℝ)) (b : ℕ)
    (bits : Fin (confidenceCopyCount p Hq) → MultilevelTree (PlannerFairSeed n b) r) :
    ((countedRationalFairQueryAtLevel (plannerStoredRows y) x r p Hq b bits).value : ℝ) =
      (scalarPlannerFairQuery (fun i j => (y i j : ℝ)) b
        (scalarPlannerListInterpret (scalarPlannerStateRatCast x)) r (p : ℝ) Hr
        (fun j => bits (Fin.cast (confidenceCopyCount_ratCast p Hq Hr) j))).value := by
  let ts := fun j => multilevelTreeMap (fun s => (countedStoredPlannerFairSeed b s).1) r (bits j)
  change ((countedScalarPlannerQueryAtLevel (plannerStoredRows y) x r p Hq ts).value : ℝ) = _
  rw [← countedScalarPlannerQueryAtLevel_ratCast _ x r p Hq Hr ts, plannerRowsRatCast_ofFn]
  rw [countedScalarPlannerQueryAtLevel_value _ _ hx]
  unfold scalarPlannerFairQuery
  apply congrArg (fun a : MedianCopiesResult ℝ => a.value)
  apply congrArg (scalarPlannerQueryAtLevel (fun i j => (y i j : ℝ))
    (scalarPlannerListInterpret (scalarPlannerStateRatCast x)) r (p : ℝ) Hr)
  funext j
  simp only [ts, multilevelTreeMap_comp, Function.comp_def, countedStoredPlannerFairSeed_ratCast]

variable [∀ i, NeZero (k i)]

/-- The actual rational query has the scalar planner's error guarantee
under the fair-bit tree law. The bound is over the complete random
reservoir, with the empirical rows and current state fixed. -/
theorem countedRationalFairQueryAtLevel_correct (y : (i : Fin n) → Fin (k i) → ℚ)
    (hy : ∀ i j, 0 ≤ (y i j : ℝ)) (hcap : ∀ i j, (y i j : ℝ) ≤ 1)
    (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup) (r : ℕ) (h : ℝ) (p : ℚ)
    (hh : 0 < h) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (Hq : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p) (b : ℕ)
    (hprec : 25 * (scalarPlannerWeight (fun i j => (y i j : ℝ)) x.1.toFinset)^2 *
      (1/2 : ℝ)^r ≤ (h/2)^2/64)
    (hgrid : scalarPlannerWeight (fun i j => (y i j : ℝ)) x.1.toFinset *
      ((10*(n:ℝ)+4)/(3*((2^b : ℕ):ℝ))) ≤ h/4) :
    let C := confidenceCopyCount p Hq
    let μ := Measure.pi (fun _ : Fin C => multilevelTreeLaw (plannerFairSeedLaw n b) r)
    let Q := countedRationalFairQueryAtLevel (plannerStoredRows y) x r p Hq b
    let v := scalarPlannerValue (fun i j => (y i j : ℝ)) hy
      (scalarPlannerListInterpret (scalarPlannerStateRatCast x))
    Measurable (fun bits => ((Q bits).value : ℝ)) ∧
      μ.real {bits | h < |((Q bits).value : ℝ) - v|} ≤ (p : ℝ) := by
  dsimp only
  let Hr := (exists_quarter_pow_le_ratCast p).mpr Hq
  let μ := multilevelTreeLaw (plannerFairSeedLaw n b) r
  let C := confidenceCopyCount p Hq
  let C' := confidenceCopyCount (p : ℝ) Hr
  let mapBits : (Fin C → MultilevelTree (PlannerFairSeed n b) r) →
      (Fin C' → MultilevelTree (PlannerFairSeed n b) r) :=
    fun a j => a (Fin.cast (confidenceCopyCount_ratCast p Hq Hr) j)
  have hm : MeasurePreserving mapBits (Measure.pi (fun _ : Fin C => μ))
      (Measure.pi (fun _ : Fin C' => μ)) :=
    (measurePreserving_piCongrLeft (fun _ : Fin C => μ)
      (finCongr (confidenceCopyCount_ratCast p Hq Hr))).symm
  have hc := scalarPlannerFairQuery_correct (fun i j => (y i j : ℝ)) hy hcap b
    (scalarPlannerListInterpret (scalarPlannerStateRatCast x)) r h (p : ℝ) hh hp hp1 Hr hprec hgrid
  let Q := scalarPlannerFairQuery (fun i j => (y i j : ℝ)) b
    (scalarPlannerListInterpret (scalarPlannerStateRatCast x)) r (p : ℝ) Hr
  let v := scalarPlannerValue (fun i j => (y i j : ℝ)) hy
    (scalarPlannerListInterpret (scalarPlannerStateRatCast x))
  have he (bits : Fin C → MultilevelTree (PlannerFairSeed n b) r) :
      ((countedRationalFairQueryAtLevel (plannerStoredRows y) x r p Hq b bits).value : ℝ) =
        (Q (mapBits bits)).value := countedRationalFairQueryAtLevel_value y x hx r p Hq Hr b bits
  simp_rw [he]
  refine ⟨hc.1.comp hm.measurable, ?_⟩
  have hSet : MeasurableSet {bits | h < |(Q bits).value-v|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hc.1.sub measurable_const))
  change (Measure.pi (fun _ : Fin C => μ)).real (mapBits ⁻¹' {bits | h < |(Q bits).value-v|}) ≤ _
  rw [Measure.real, ← Measure.map_apply hm.measurable hSet, hm.map_eq]
  exact hc.2.1

end ProphetSecretary.Statistics
