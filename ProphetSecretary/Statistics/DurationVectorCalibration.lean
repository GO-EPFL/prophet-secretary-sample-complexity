import ProphetSecretary.Statistics.CalibratedValidationSelection

/-!
# Calibration of ordered reported durations

Only the ordered duration vector of each independently drawn profile is
needed for interpolation and its statistical bounds. In particular, the
same argument applies to timestamps reported on a finite clock grid.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration

variable {Y : Type*} {J m : ℕ}

noncomputable def durationVectorCurve (τ : Y → Fin (J+1) → ℝ) (θ : ℝ) (y : Y) : ℝ :=
  durationCurve (J+2) (durationKnots (τ y)) θ

noncomputable def durationVectorAverage (τ : Y → Fin (J+1) → ℝ) (w : Fin m → Y) (k : ℕ) : ℝ :=
  (m : ℝ)⁻¹*∑ j, durationKnots (τ (w j)) k

noncomputable def durationVectorSelection (τ : Y → Fin (J+1) → ℝ) (w : Fin m → Y) (ρ : ℝ) : ℕ × ℝ :=
  let v := durationVectorAverage τ w
  let k := calibrationCrossing v ρ (J+2)
  (k,(ρ-v (k-1))/(v k-v (k-1)))

noncomputable def durationVectorParameter (τ : Y → Fin (J+1) → ℝ) (w : Fin m → Y) (ρ : ℝ) : ℝ :=
  selectionParameter (J+2) (durationVectorAverage τ w) ρ

lemma durationVectorAverage_zero (τ : Y → Fin (J+1) → ℝ) (w : Fin m → Y) :
    durationVectorAverage τ w 0=0 := by simp [durationVectorAverage]

lemma durationVectorAverage_last [NeZero m] (τ : Y → Fin (J+1) → ℝ) (w : Fin m → Y) :
    durationVectorAverage τ w (J+2)=1 := by
  simp only [durationVectorAverage,durationKnots_last,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast NeZero.ne m)

lemma durationVectorSelection_bounds [NeZero m] (τ : Y → Fin (J+1) → ℝ) (w : Fin m → Y)
    {ρ : ℝ} (hρ : ρ∈Ioc (0 : ℝ) 1) :
    let p := durationVectorSelection τ w ρ
    1≤p.1 ∧ p.1≤J+2 ∧ p.2∈Ioc (0 : ℝ) 1 := by
  let v := durationVectorAverage τ w
  have h0 : v 0<ρ := by simpa only [v,durationVectorAverage_zero] using hρ.1
  have h1 : ρ≤v (J+2) := by simpa only [v,durationVectorAverage_last] using hρ.2
  have h := calibrationCrossing_bounds v ρ (J+2) h0 h1
  exact ⟨h.1,h.2.1,calibrationMixingFraction_mem_unit v ρ (J+2) h0 h1⟩

lemma durationVectorParameter_eq_leastRoot [NeZero m] (τ : Y → Fin (J+1) → ℝ)
    (hτ : ∀ y, Monotone (τ y)) (hR : ∀ y j, τ y j∈Icc (0 : ℝ) 1)
    (w : Fin m → Y) {ρ : ℝ} (hρ : ρ∈Ioc (0 : ℝ) 1) :
    durationVectorParameter τ w ρ=parameter (durationVectorCurve τ) ρ w := by
  let v := durationVectorAverage τ w
  have hv : Monotone v := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ =>
      durationKnots_monotone _ (hτ (w k)) (hR (w k)) hij)) (by positivity)
  have h := selectionParameter_eq_leastRoot (J+2) (by omega) v hv
    (durationVectorAverage_zero τ w) (durationVectorAverage_last τ w) hρ
  have hEq : durationCurve (J+2) v = empiricalCurve (durationVectorCurve τ) w := by
    funext θ
    exact durationCurve_average (J+2) m (fun j => durationKnots (τ (w j))) θ
  rw [hEq] at h
  exact h

lemma measurable_durationVectorSelection {Ω : Type*} [MeasurableSpace Ω]
    {a : Ω → Fin m → Fin (J+1) → ℝ} {ρ : Ω → ℝ}
    (ha : ∀ i j, Measurable (fun d => a d i j)) (hρ : Measurable ρ) :
    Measurable (fun d => durationVectorSelection (a d) id (ρ d)) := by
  have hv (k : ℕ) : Measurable (fun d => durationVectorAverage (a d) id k) := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    exact measurable_durationKnots (ha i) k
  exact (measurable_calibrationCrossing _ _ _ hv hρ).prodMk
    (measurable_calibrationMixingFraction _ _ _ hv hρ)

variable [MeasurableSpace Y]

noncomputable def durationVectorError (μ : Measure Y) (τ : Y → Fin (J+1) → ℝ) (ρ : ℝ)
    (w : Fin m → Y) : ℝ :=
  (∫ y,durationVectorCurve τ (durationVectorParameter τ w ρ) y ∂μ)-ρ

theorem durationVectorError_moments [NeZero m] (μ : Measure Y) [IsProbabilityMeasure μ]
    (τ : Y → Fin (J+1) → ℝ) (hm : ∀ j, Measurable (fun y => τ y j))
    (hτ : ∀ y, Monotone (τ y)) (hR : ∀ y j, τ y j∈Icc (0 : ℝ) 1)
    {ρ : ℝ} (hρ : ρ∈Ioc (0 : ℝ) 1) :
    |∫ w,durationVectorError μ τ ρ w ∂Measure.pi (fun _ : Fin m => μ)|≤1/((m : ℝ)+1) ∧
    (∫ w,(durationVectorError μ τ ρ w)^2 ∂Measure.pi (fun _ : Fin m => μ))≤4/(m : ℝ) := by
  let f := durationVectorCurve τ
  have hfm : Measurable (Function.uncurry f) :=
    measurable_durationCurve (J+2)
      (fun k => measurable_durationKnots (fun j => (hm j).comp measurable_snd) k) measurable_fst
  have hc (y : Y) : Continuous (fun θ => f θ y) := durationCurve_continuous _ _
  have hmono (y : Y) : Monotone (fun θ => f θ y) :=
    durationCurve_monotone _ _ (durationKnots_monotone _ (hτ y) (hR y))
  have hf0 (y : Y) : f 0 y=0 := (durationCurve_zero _ _).trans (durationKnots_zero _)
  have hf1 (y : Y) : f 1 y=1 := (durationCurve_one _ _).trans (durationKnots_last _)
  have hfR (θ : ℝ) (y : Y) : f θ y∈Icc (0 : ℝ) 1 :=
    durationCurve_range _ _ (durationKnots_monotone _ (hτ y) (hR y))
      (durationKnots_zero _) (durationKnots_last _) θ
  have he : durationVectorError (m := m) μ τ ρ=error μ f ρ := by
    funext w
    unfold durationVectorError error populationCurve
    rw [durationVectorParameter_eq_leastRoot τ hτ hR w hρ]
  rw [he]
  exact ⟨integral_error_abs_le μ f hfm hc hmono hfR hf0 hf1 ⟨hρ.1.le,hρ.2⟩,
    integral_error_sq_le μ f hfm hc hmono hfR hf0 hf1 ⟨hρ.1.le,hρ.2⟩⟩

end ProphetSecretary.Statistics.Calibration
