import ProphetSecretary.Limiting.PositiveRestrictionRareDesign

/-!
# Weak finite-hybrid values from continuous full mark laws

One common virtual multiplicity is chosen before passing to the weak law
limit. The two quantitative Poisson errors are uniform over bounded reward
weights and every nonnegative duration weight. The finite middle comparison
optimizes over all admissible policies, with no optimizer convergence premise.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

/-- Actual scalar-value continuity, uniform over the indicated weights.
The full analytical mark laws may have zero atoms. Their positive restrictions
are the actual intensities, so these restrictions themselves need not converge
weakly. This supporting theorem keeps that representation equality explicit. -/
theorem optimalScalarValue_uniform_weak_full_mark_laws
    (Bs : ℕ → FiniteIntensityHybridInstance n) (B : FiniteIntensityHybridInstance n)
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (H W : ℝ≥0) (hCaps : ∀ m, (Bs m).cap ≤ H) (hCap : B.cap ≤ H)
    (hTerms : ∀ m, (Bs m).terminal = 0) (hTerm : B.terminal = 0)
    (hsupps : ∀ m, ∀ᵐ x ∂(μs m : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hsupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hFulls : ∀ m, (Bs m).intensity = (μs m).restrict (Ioi 0))
    (hFull : B.intensity = μ.restrict (Ioi 0))
    (hIndividual : ∀ i, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hIntensity : Tendsto μs atTop (𝓝 μ)) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop, ∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c →
      |(Bs m).optimalScalarValue w c-B.optimalScalarValue w c| < ε := by
  obtain ⟨R,hR,hRs⟩ := exists_uniform_mass_bound_of_tendsto μs μ hIntensity
  have hpCaps (m : ℕ) : ∀ i, ∀ᵐ x ∂(Bs m).individuals.law i, x ≤ (H : ℝ) := fun i =>
    ((Bs m).individual_bounded i).mono fun _ hx => hx.trans (by exact_mod_cast hCaps m)
  have hpCap : ∀ i, ∀ᵐ x ∂B.individuals.law i, x ≤ (H : ℝ) := fun i =>
    (B.individual_bounded i).mono fun _ hx => hx.trans (by exact_mod_cast hCap)
  intro ε hε
  obtain ⟨j,hj⟩ := ((tendsto_order.mp (rareDesignError_tendsto_zero H W R)).2 (ε/3) (by positivity)).exists
  let k := bernoulliMultiplicity (R : ℝ) j
  have hk : 0 < k := bernoulliMultiplicity_positive _ _
  have hkR : R ≤ (k : ℝ≥0) := by
    have hceil := Nat.le_ceil (R : ℝ)
    have hnat : Nat.ceil (R : ℝ) ≤ k := by dsimp [k,bernoulliMultiplicity]; omega
    exact_mod_cast hceil.trans (Nat.cast_le.mpr hnat)
  let Qs : ℕ → Model.Instance (n+k) := fun m => rareDesign (Bs m).individuals (μs m) H (hsupps m) k hk ((hRs m).trans hkR)
  let Q : Model.Instance (n+k) := rareDesign B.individuals μ H hsupp k hk (hR.trans hkR)
  have hQweak : ∀ i, Tendsto (fun m => (Qs m).marginalProbabilityLaw i) atTop (𝓝 (Q.marginalProbabilityLaw i)) :=
    rareDesign_coordinatewise_weak (fun m => (Bs m).individuals) B.individuals
      μs μ H hsupps hsupp k hk
      (fun m => (hRs m).trans hkR) (hR.trans hkR) hIndividual hIntensity
  have hQsCap (m : ℕ) : ∀ i, ∀ᵐ x ∂(Qs m).law i, x ≤ (H : ℝ) :=
    rareDesign_bounded _ _ H (hpCaps m) (hsupps m) k hk ((hRs m).trans hkR)
  have hQCap : ∀ i, ∀ᵐ x ∂Q.law i, x ≤ (H : ℝ) := rareDesign_bounded _ _ H hpCap hsupp k hk (hR.trans hkR)
  filter_upwards [Model.optimalScalarValue_uniform_weak_law_error Qs Q H W hQsCap hQCap hQweak (ε/3) (by positivity)] with m hm
  intro w c hw hwW hc
  have hleft : |Model.optimalScalarValue (Qs m) w c-(Bs m).optimalScalarValue w c| ≤ rareDesignError H W R k := by
    exact (Bs m).rareDesign_full_mark_error (hTerms m) (μs m) H W R (hCaps m) (hsupps m)
      (hFulls m) (hRs m) k hk hkR hw hwW hc
  have hright : |Model.optimalScalarValue Q w c-B.optimalScalarValue w c| ≤ rareDesignError H W R k :=
    B.rareDesign_full_mark_error hTerm μ H W R hCap hsupp hFull hR k hk hkR hw hwW hc
  have hmid := hm w c hw hwW hc
  have htri : |(Bs m).optimalScalarValue w c-B.optimalScalarValue w c| ≤
      |(Bs m).optimalScalarValue w c-Model.optimalScalarValue (Qs m) w c|+
        |Model.optimalScalarValue (Qs m) w c-Model.optimalScalarValue Q w c|+
          |Model.optimalScalarValue Q w c-B.optimalScalarValue w c| := by
    calc
      _ = |((Bs m).optimalScalarValue w c-Model.optimalScalarValue (Qs m) w c)+
        (Model.optimalScalarValue (Qs m) w c-Model.optimalScalarValue Q w c)+
          (Model.optimalScalarValue Q w c-B.optimalScalarValue w c)| := by congr 1; ring
      _ ≤ _ := (abs_add_le
        (((Bs m).optimalScalarValue w c-Model.optimalScalarValue (Qs m) w c)+
          (Model.optimalScalarValue (Qs m) w c-Model.optimalScalarValue Q w c))
        (Model.optimalScalarValue Q w c-B.optimalScalarValue w c)).trans
          (add_le_add (abs_add_le ((Bs m).optimalScalarValue w c-Model.optimalScalarValue (Qs m) w c)
            (Model.optimalScalarValue (Qs m) w c-Model.optimalScalarValue Q w c)) le_rfl)
  rw [abs_sub_comm] at hleft
  dsimp [k] at hleft hright
  linarith [htri]

end ProphetSecretary.Limiting
