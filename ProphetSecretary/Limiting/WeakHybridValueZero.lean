import ProphetSecretary.Limiting.WeakRareDesign

/-!
# Weak continuity of finite-hybrid values at zero terminal reward

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
All laws may have atoms, the retained dimension may be zero, and limiting
intensity may vanish. -/
theorem optimalScalarValue_uniform_weak_zero_terminal
    (Bs : ℕ → FiniteIntensityHybridInstance n) (B : FiniteIntensityHybridInstance n)
    (H W : ℝ≥0) (hCaps : ∀ m, (Bs m).cap ≤ H) (hCap : B.cap ≤ H)
    (hTerms : ∀ m, (Bs m).terminal = 0) (hTerm : B.terminal = 0)
    (hIndividual : ∀ i, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hIntensity : Tendsto (fun m => (Bs m).intensity) atTop (𝓝 B.intensity)) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop, ∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c →
      |(Bs m).optimalScalarValue w c-B.optimalScalarValue w c| < ε := by
  obtain ⟨R,hR,hRs⟩ := exists_uniform_mass_bound_of_tendsto (fun m => (Bs m).intensity) B.intensity hIntensity
  have hsupps (m : ℕ) : ∀ᵐ x ∂((Bs m).intensity : Measure ℝ), x ∈ Icc (0 : ℝ) H :=
    (Bs m).intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2.trans (by exact_mod_cast hCaps m)⟩
  have hsupp : ∀ᵐ x ∂(B.intensity : Measure ℝ), x ∈ Icc (0 : ℝ) H :=
    B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2.trans (by exact_mod_cast hCap)⟩
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
  let Qs : ℕ → Model.Instance (n+k) := fun m => rareDesign (Bs m).individuals (Bs m).intensity H (hsupps m) k hk ((hRs m).trans hkR)
  let Q : Model.Instance (n+k) := rareDesign B.individuals B.intensity H hsupp k hk (hR.trans hkR)
  have hQweak : ∀ i, Tendsto (fun m => (Qs m).marginalProbabilityLaw i) atTop (𝓝 (Q.marginalProbabilityLaw i)) :=
    rareDesign_coordinatewise_weak (fun m => (Bs m).individuals) B.individuals
      (fun m => (Bs m).intensity) B.intensity H hsupps hsupp k hk
      (fun m => (hRs m).trans hkR) (hR.trans hkR) hIndividual hIntensity
  have hQsCap (m : ℕ) : ∀ i, ∀ᵐ x ∂(Qs m).law i, x ≤ (H : ℝ) :=
    rareDesign_bounded _ _ H (hpCaps m) (hsupps m) k hk ((hRs m).trans hkR)
  have hQCap : ∀ i, ∀ᵐ x ∂Q.law i, x ≤ (H : ℝ) := rareDesign_bounded _ _ H hpCap hsupp k hk (hR.trans hkR)
  filter_upwards [Model.optimalScalarValue_uniform_weak_law_error Qs Q H W hQsCap hQCap hQweak (ε/3) (by positivity)] with m hm
  intro w c hw hwW hc
  have hleft : |Model.optimalScalarValue (Qs m) w c-(Bs m).optimalScalarValue w c| ≤ rareDesignError H W R k := by
    exact ((Bs m).rareDesign_value_uniform_error (hTerms m) W R (hRs m) k hk hkR hw hwW hc).trans
      (rareDesignError_mono_cap (hCaps m) W R k)
  have hright : |Model.optimalScalarValue Q w c-B.optimalScalarValue w c| ≤ rareDesignError H W R k :=
    (B.rareDesign_value_uniform_error hTerm W R hR k hk hkR hw hwW hc).trans
      (rareDesignError_mono_cap hCap W R k)
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
