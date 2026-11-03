import ProphetSecretary.Statistics.CalibratedDurationCurve

/-!
# The computed calibration point and the least empirical root

The finite first-crossing scan and one interpolation fraction produce the
smallest root of the continuous duration curve. The selected pair is kept
intact: on endpoint extensions its fraction still affects the surrogate
curve even though both output-policy indices coincide.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration

noncomputable def selectionParameter (N : ℕ) (v : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ((calibrationCrossing v ρ N-1 : ℕ)+calibrationMixingFraction v ρ N)/(N : ℝ)

lemma measurable_calibrationCrossing {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ) (v : Ω → ℕ → ℝ) (ρ : Ω → ℝ)
    (hv : ∀ k, Measurable (fun ω => v ω k)) (hρ : Measurable ρ) :
    Measurable (fun ω => calibrationCrossing (v ω) (ρ ω) N) := by
  induction N generalizing v with
  | zero => exact measurable_const
  | succ N ih =>
    simp only [calibrationCrossing]
    exact Measurable.ite (measurableSet_le hρ (hv 1)) measurable_const
      ((measurable_of_countable (fun k : ℕ => k+1)).comp
        (ih (fun ω k => v ω (k+1)) (fun k => hv (k+1))))

lemma measurable_calibrationMixingFraction {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ) (v : Ω → ℕ → ℝ) (ρ : Ω → ℝ)
    (hv : ∀ k, Measurable (fun ω => v ω k)) (hρ : Measurable ρ) :
    Measurable (fun ω => calibrationMixingFraction (v ω) (ρ ω) N) := by
  have hk := measurable_calibrationCrossing N v ρ hv hρ
  have hkPrev := (measurable_of_countable (fun k : ℕ => k-1)).comp hk
  have hVec : Measurable v := measurable_pi_lambda _ hv
  have hEval : Measurable (fun p : (ℕ → ℝ) × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left (fun k => measurable_pi_apply k)
  have hLo := hEval.comp (hVec.prodMk hkPrev)
  have hHi := hEval.comp (hVec.prodMk hk)
  exact (hρ.sub hLo).div (hHi.sub hLo)

lemma measurable_selectionParameter {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ) (v : Ω → ℕ → ℝ) (ρ : Ω → ℝ)
    (hv : ∀ k, Measurable (fun ω => v ω k)) (hρ : Measurable ρ) :
    Measurable (fun ω => selectionParameter N (v ω) (ρ ω)) := by
  have hk := measurable_calibrationCrossing N v ρ hv hρ
  have hPrev : Measurable (fun ω => ((calibrationCrossing (v ω) (ρ ω) N-1 : ℕ) : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => ((k-1 : ℕ) : ℝ))).comp hk
  exact (hPrev.add (measurable_calibrationMixingFraction N v ρ hv hρ)).div_const _

/-- The finite scan realizes the paper's smallest-root convention exactly. -/
theorem selectionParameter_eq_leastRoot (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (hv : Monotone v) (h0 : v 0=0) (h1 : v N=1) {ρ : ℝ} (hρ : ρ ∈ Ioc (0 : ℝ) 1) :
    selectionParameter N v ρ=durationCalibrationRoot (durationCurve N v) ρ := by
  let k := calibrationCrossing v ρ N
  let j := k-1
  let α := calibrationMixingFraction v ρ N
  let θ := ((j : ℝ)+α)/(N : ℝ)
  let r := durationCalibrationRoot (durationCurve N v) ρ
  have hLow : v 0 < ρ := by rw [h0]; exact hρ.1
  have hHigh : ρ ≤ v N := by rw [h1]; exact hρ.2
  obtain ⟨hk1, hkN, hlo, hhi⟩ := calibrationCrossing_bounds v ρ N hLow hHigh
  have hj : j < N := by dsimp [j, k]; omega
  have hjk : j+1=k := by dsimp [j, k]; omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNRne : (N : ℝ) ≠ 0 := hNR.ne'
  have hα := calibrationMixingFraction_mem_unit v ρ N hLow hHigh
  have hα01 : α ∈ Icc (0 : ℝ) 1 := ⟨hα.1.le,hα.2⟩
  have hθRange : θ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg j) hα01.1) hNR.le
    · apply (div_le_one hNR).mpr
      have hjR : (j : ℝ)+1 ≤ N := by exact_mod_cast Nat.succ_le_iff.mpr hj
      linarith [hα.2]
  have hθEquation : durationCurve N v θ=ρ := by
    rw [durationCurve_on_segment N hN v j hj hα01, hjk]
    exact calibrationMixingFraction_equation v ρ N hLow hHigh
  have hRoot := durationCalibrationRoot_isLeast (durationCurve N v) (durationCurve_continuous N v)
    (by rw [durationCurve_zero,h0]) (by rw [durationCurve_one,h1]) ⟨hρ.1.le,hρ.2⟩
  have hrθ : r ≤ θ := hRoot.2 ⟨hθRange,hθEquation⟩
  have hLeft : durationCurve N v ((j : ℝ)/(N : ℝ))=v j := by
    simpa only [add_zero, sub_zero, one_mul, zero_mul] using
      durationCurve_on_segment N hN v j hj (α := 0) (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have hLeftR : (j : ℝ)/(N : ℝ) < r := by
    by_contra hn
    have hVal := durationCurve_monotone N v hv (le_of_not_gt hn)
    rw [hRoot.1.2,hLeft] at hVal
    change ρ ≤ v (k-1) at hVal
    exact not_le_of_gt hlo hVal
  let β := (N : ℝ)*r-(j : ℝ)
  have hβ0 : 0 ≤ β := by
    have h := (div_lt_iff₀ hNR).mp hLeftR
    dsimp [β]
    nlinarith
  have hβα : β ≤ α := by
    have h := (le_div_iff₀ hNR).mp hrθ
    dsimp [β]
    nlinarith
  have hβ1 : β ≤ 1 := hβα.trans hα.2
  have hrParam : r=((j : ℝ)+β)/(N : ℝ) := by
    dsimp [β]
    field_simp [hNRne]
    ring
  have hβEquation : (1-β)*v j+β*v (j+1)=ρ := by
    have h := durationCurve_on_segment N hN v j hj ⟨hβ0,hβ1⟩
    rw [← hrParam] at h
    exact h.symm.trans hRoot.1.2
  have hαEquation : (1-α)*v j+α*v (j+1)=ρ := by
    rw [hjk]
    exact calibrationMixingFraction_equation v ρ N hLow hHigh
  have hD : 0 < v (j+1)-v j := by
    change v (k-1) < ρ at hlo
    rw [hjk]
    change ρ ≤ v k at hhi
    dsimp [j]
    linarith
  have hProd : (v (j+1)-v j)*(α-β)=0 := by nlinarith [hαEquation,hβEquation]
  have hEq : α=β := sub_eq_zero.mp ((mul_eq_zero.mp hProd).resolve_left hD.ne')
  change θ=r
  rw [hrParam,← hEq]

end ProphetSecretary.Statistics.Calibration
