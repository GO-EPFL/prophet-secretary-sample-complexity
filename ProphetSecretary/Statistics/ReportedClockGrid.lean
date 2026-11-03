import ProphetSecretary.Statistics.CalibratedClockRounding
import ProphetSecretary.Statistics.ReportedValidation
import ProphetSecretary.Probability.DyadicUniform

/-!
# Agreement with the finite-clock rank execution

A validation profile's reported duration is exactly the timestamp of the
first accepted rank in the finite-grid policy. Equal grid timestamps leave
the identities and rank order of the observed prefix unchanged.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {PSeed : Type} [NeZero m]

lemma uniformGridRound_monotone (N : ℕ) (hN : 0<N) : Monotone (uniformGridRound N hN) := by
  intro a b hab
  have h : (N : ℝ)*a≤(N : ℝ)*b := mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg N)
  have hf := Nat.floor_mono h
  have hm : min (N-1) ⌊(N : ℝ)*a⌋₊≤min (N-1) ⌊(N : ℝ)*b⌋₊ := min_le_min le_rfl hf
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hm) (Nat.cast_nonneg N)

lemma uniformGridReport_approx (N : ℕ) (hN : 0<N) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    terminalClockReport (uniformGridRound N hN) t∈Icc (0 : ℝ) t ∧
      t-terminalClockReport (uniformGridRound N hN) t≤1/(N : ℝ) :=
  terminalClockReport_range ht (by positivity) (fun _ => uniformGridRound_bounds N hN)

lemma uniformGridReport_monotoneOn (N : ℕ) (hN : 0<N) :
    MonotoneOn (terminalClockReport (uniformGridRound N hN)) (Icc (0 : ℝ) 1) :=
  terminalClockReport_monotoneOn ((uniformGridRound_monotone N hN).monotoneOn _)
    (fun _ h => (uniformGridRound_bounds N hN h).2.1.trans h.2)

theorem reportedValidationDuration_eq_rank {zlo zhi : ℝ} (h0 : 0≤zlo) (hz : zlo≤zhi)
    (f : ℝ → ℝ) (hf : ∀ t∈Icc (0 : ℝ) 1, f t∈Icc (0 : ℝ) t)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (j : Fin (J+1)) (r : PolicyQueryArray n J PSeed)
    (s : Fin n → ℝ) (hs : StrictMono s) (hS : ∀ k,s k∈Ico (0 : ℝ) 1)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    let u := Instance.reconstructClocks (s,p)
    let π := frozenFamilyPolicy zlo zhi estimate q j
    reportedValidationDuration (terminalClockReport f) zlo zhi (clockRoundedEstimate f estimate) q (x,u,r) j =
      π.clockToRank.reportedDuration (f ∘ s,r) p x (f ∘ s) := by
  let u := Instance.reconstructClocks (s,p)
  let π := frozenFamilyPolicy zlo zhi estimate q j
  let Q := frozenFamilyPolicy zlo zhi (clockRoundedEstimate f estimate) q j
  have hu (i : Fin n) : u i∈Icc (0 : ℝ) 1 := ⟨(hS (p.symm i)).1,(hS (p.symm i)).2.le⟩
  have hTime : Q.stoppingTime r Finset.univ x u=(π.withClockAnnotations f).stoppingTime r Finset.univ x u := by
    apply (Policy.outcomes_eq_of_actions_eq Q (π.withClockAnnotations f) r r Finset.univ x u ?_).2
    intro i
    exact numericalFamilyPolicy_clockRounded h0 hz f estimate j (q,r) (hu i) (hf _ (hu i)) i (x i)
      (history Finset.univ x u (u i))
  change terminalClockReport f (validationDuration zlo zhi (clockRoundedEstimate f estimate) q (x,u,r) j)=_
  rw [validationDuration_eq_actual zlo zhi (clockRoundedEstimate f estimate) q (x,u,r) j hu]
  change terminalClockReport f (Q.stoppingTime r Finset.univ x u)=_
  rw [hTime]
  exact π.withClockAnnotations_report_eq_rank f r s hs (fun k => (hS k).2) p x

/-- The same pathwise action identity applies to the selected policy on the online run. -/
lemma preparedPolicy_clockRounded_action {zlo zhi : ℝ} (h0 : 0≤zlo) (hz : zlo≤zhi)
    (f : ℝ → ℝ) (hf : ∀ t∈Icc (0 : ℝ) 1, f t∈Icc (0 : ℝ) t)
    (estimate : ContinuationEstimator n m PSeed) (a : PreparedCalibration n m)
    (r : PolicyQueryArray n J PSeed) (c : ℝ)
    (s : Fin n → ℝ) (hs : StrictMono s) (hS : ∀ k,s k∈Icc (0 : ℝ) 1)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    (preparedPolicy zlo zhi (clockRoundedEstimate f estimate) a).action (r,c) Finset.univ x
      (Instance.reconstructClocks (s,p)) i =
        (preparedPolicy zlo zhi estimate a).clockToRank.action (f ∘ s,(r,c)) p x i := by
  let u := Instance.reconstructClocks (s,p)
  let π := preparedPolicy (J := J) zlo zhi estimate a
  have hi : u i∈Icc (0 : ℝ) 1 := hS (p.symm i)
  apply Eq.trans _ (π.withClockAnnotations_action f (r,c) s hs p x i)
  change (preparedPolicy zlo zhi (clockRoundedEstimate f estimate) a).decide (r,c) (u i) i (x i)
      (history Finset.univ x u (u i)) =
    (preparedPolicy zlo zhi estimate a).decide (r,c) (f (u i)) i (x i)
      (annotateClockHistory f (history Finset.univ x u (u i)))
  rw [preparedPolicy_decide,preparedPolicy_decide]
  exact numericalFamilyPolicy_clockRounded h0 hz f estimate _ (a.1,r) hi (hf _ hi) i (x i)
    (history Finset.univ x u (u i))

end ProphetSecretary.Statistics.Calibration
