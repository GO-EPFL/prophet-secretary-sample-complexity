import ProphetSecretary.Limiting.WeakRareDesign
import ProphetSecretary.Limiting.WeakHybridBenchmark
import ProphetSecretary.Probability.BoundedCDFOrder

/-!
# Prophet comparison between finite rare designs and the Poisson law

The Bernoulli void probability is at most the corresponding Poisson void
probability. Its proof uses the actual product CDFs, so every retained zero
identity is present in the finite design. No policy comparison is used here.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

lemma rareProbabilityLaw_real_Ioi (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q)
    {t : ℝ} (ht : 0 ≤ t) :
    (rareProbabilityLaw μ q hq hm : Measure ℝ).real (Ioi t) = (q : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t) := by
  change ((1-q⁻¹*μ.mass) • Measure.dirac 0+q⁻¹ • (μ : Measure ℝ)).real (Ioi t) = _
  rw [Measure.real,Measure.add_apply,ENNReal.toReal_add (by finiteness) (by finiteness)]
  change ((1-q⁻¹*μ.mass) • Measure.dirac (0 : ℝ)).real (Ioi t)+
    (q⁻¹ • (μ : Measure ℝ)).real (Ioi t) = _
  simp only [measureReal_nnreal_smul_apply,NNReal.coe_inv]
  have hz : (Measure.dirac (0 : ℝ)).real (Ioi t) = 0 := by
    simp [Measure.real,Measure.dirac_apply',not_lt.mpr ht]
  rw [hz,mul_zero,zero_add]

lemma rareProbabilityLaw_real_Iic (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q)
    {t : ℝ} (ht : 0 ≤ t) :
    (rareProbabilityLaw μ q hq hm : Measure ℝ).real (Iic t) = 1-(q : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t) := by
  have h := probReal_gt_eq_one_sub_le (rareProbabilityLaw μ q hq hm : Measure ℝ) measurable_id t
  change (rareProbabilityLaw μ q hq hm : Measure ℝ).real (Ioi t) =
    1-(rareProbabilityLaw μ q hq hm : Measure ℝ).real (Iic t) at h
  rw [rareProbabilityLaw_real_Ioi μ q hq hm ht] at h
  linarith

lemma finite_maximum_real_Iic {m : ℕ} (P : Model.Instance m) {t : ℝ} (ht : 0 ≤ t) :
    P.valuesLaw.real {v | Model.Instance.maximum v ≤ t} = ∏ i, (P.law i).real (Iic t) := by
  have he : {v : Fin m → ℝ | Model.Instance.maximum v ≤ t} = univ.pi (fun _ => Iic t) := by
    ext v
    change Model.Instance.maximum v ≤ t ↔ ∀ i ∈ (univ : Set (Fin m)), v i ∈ Iic t
    constructor
    · intro h i _
      exact (Model.Instance.le_maximum v i).trans h
    · intro h
      exact Model.Instance.maximum_le v ht (fun i => h i (mem_univ i))
  rw [Measure.real,he,Model.Instance.valuesLaw,Measure.pi_pi,ENNReal.toReal_prod]
  rfl

lemma rareDesign_maximum_real_Iic (P : Model.Instance n) (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0 < k) (hm : μ.mass ≤ (k : ℝ≥0)) {t : ℝ} (ht : 0 ≤ t) :
    (rareDesign P μ H hμ k hk hm).valuesLaw.real {v | Model.Instance.maximum v ≤ t} =
      (∏ i, (P.law i).real (Iic t))*(1-(k : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t))^k := by
  rw [finite_maximum_real_Iic _ ht,Fin.prod_univ_add]
  simp only [rareDesign,appendIID,Fin.addCases_left,Fin.addCases_right,
    rareProbabilityLaw_real_Iic μ (k : ℝ≥0) (by exact_mod_cast hk) hm ht,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,NNReal.coe_natCast]

lemma rareDesign_cdf_le_Poisson (P : Model.Instance n) (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0 < k) (hm : μ.mass ≤ (k : ℝ≥0)) {t : ℝ} (ht : 0 ≤ t) :
    (rareDesign P μ H hμ k hk hm).valuesLaw.real {v | Model.Instance.maximum v ≤ t} ≤
      (hybridValueLaw P μ).real {v | hybridMaximum 0 v ≤ t} := by
  rw [rareDesign_maximum_real_Iic _ _ _ _ _ _ _ ht,hybridMaximum_real_Iic _ _ ht ht]
  have hbase : 0 ≤ 1-(k : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t) := by
    have hb : 0 ≤ (rareProbabilityLaw μ (k : ℝ≥0) (by exact_mod_cast hk) hm : Measure ℝ).real (Iic t) := measureReal_nonneg
    rw [rareProbabilityLaw_real_Iic μ (k : ℝ≥0) (by exact_mod_cast hk) hm ht] at hb
    simpa only [NNReal.coe_natCast] using hb
  have hle : 1-(k : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t) ≤
      Real.exp (-((k : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t))) := by
    linarith [Real.add_one_le_exp (-((k : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t)))]
  have hpower : (1-(k : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t))^k ≤ Real.exp (-(μ : Measure ℝ).real (Ioi t)) := by
    calc
      _ ≤ (Real.exp (-((k : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t))))^k := pow_le_pow_left₀ hbase hle k
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        have hkR : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
        field_simp
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpower
    (Finset.prod_nonneg (fun _ _ => measureReal_nonneg) : 0 ≤ ∏ i, (P.law i).real (Iic t))

/-- Each finite rare design has a prophet benchmark at least as large as the
actual Poisson benchmark at the same total intensity. -/
theorem FiniteIntensityHybridInstance.expectedMaximum_le_rareDesign
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (k : ℕ) (hk : 0 < k) (hm : B.intensity.mass ≤ (k : ℝ≥0)) :
    B.expectedMaximum ≤ (rareDesign B.individuals B.intensity B.cap
      (B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩) k hk hm).expectedMaximum := by
  let hμ : ∀ᵐ x ∂(B.intensity : Measure ℝ), x ∈ Icc (0 : ℝ) B.cap :=
    B.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)
  let Q := rareDesign B.individuals B.intensity B.cap hμ k hk hm
  have hQ := rareDesign_bounded B.individuals B.intensity B.cap B.individual_bounded hμ k hk hm
  have hQr : ∀ᵐ x ∂Q.valuesLaw, Model.Instance.maximum x ∈ Icc (0 : ℝ) B.cap := by
    have hx : ∀ᵐ x ∂Q.valuesLaw, ∀ i, x i ≤ (B.cap : ℝ) :=
      ae_all_iff.mpr (fun i => (measurePreserving_eval Q.law i).quasiMeasurePreserving.ae (hQ i))
    exact hx.mono fun x h => ⟨Model.Instance.maximum_nonnegative x,Model.Instance.maximum_le x B.cap.property h⟩
  have hBr : ∀ᵐ v ∂hybridValueLaw B.individuals B.intensity, hybridMaximum 0 v ∈ Icc (0 : ℝ) B.cap := by
    filter_upwards [hybridValueLaw_values_bounds B.individuals B.intensity B.individual_bounded B.intensity_supported] with v hv
    exact ⟨hybridMaximum_nonnegative _ _,hybridMaximum_le B.cap.property B.cap.property v (fun i => (hv i).2)⟩
  change (∫ v, hybridMaximum B.terminal v ∂hybridValueLaw B.individuals B.intensity) ≤
    ∫ x, Model.Instance.maximum x ∂Q.valuesLaw
  rw [ha]
  exact integral_le_of_bounded_cdf_le Q.valuesLaw (hybridValueLaw B.individuals B.intensity)
    Model.Instance.measurable_maximum (measurable_hybridMaximum 0) B.cap hQr hBr
    (fun t ht => rareDesign_cdf_le_Poisson B.individuals B.intensity B.cap hμ k hk hm ht.1.le)

end ProphetSecretary.Limiting
