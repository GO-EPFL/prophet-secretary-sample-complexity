import ProphetSecretary.Limiting.HybridOutcomeError
import ProphetSecretary.Limiting.HybridValueBandProbability

/-!
# Explicit finite-hybrid outcome-stability estimate

The first-disagreement event is charged to actual scalar regret or an
unconditioned positive boundary event. The terminal-window maximum includes
all offers. All constants are independent of retained dimension and total
anonymous intensity near zero.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma HybridRule.measurableSet_earlyValueDifference (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (window : ℝ) :
    MeasurableSet (π.earlyValueDifference B w c window) := by
  apply measurableSet_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := by fun_prop
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) := by fun_prop
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  have hX (k : Fin (n+N)) := measurable_combinedValues_family _ hx _ hv k
  have hU (k : Fin (n+N)) := measurable_combinedClocks_family _ hu _ hv k
  exact (π.asFinitePolicy N).measurableSet_earlyOutcomeDifference (π.asFinitePolicy_isMeasurable hπ N)
    ((B.valueRule w c).asFinitePolicy N)
    ((B.valueRule w c).asFinitePolicy_isMeasurable (B.valueRule_isMeasurable hw hc) N)
    hr measurable_const hX hU measurable_const

theorem RandomizedHybridPolicy.earlyValueDifference_probability (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {w c b e : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (he0 : 0 < e) (he : e ≤ w*b/4) :
    (B.law π.seedLaw).real (π.rule.earlyValueDifference B w c (2*w*b/c)) ≤
      (B.optimalScalarValue w c-π.scalarObjective B w c)/e+
        (B.law π.seedLaw).real (B.positiveValueBand w c b e) := by
  let μ := B.law π.seedLaw
  let L : Set (HybridWorld n π.Seed) := {v | e ≤ π.rule.reachedValueLoss B w c v}
  let G : Set (HybridWorld n π.Seed) := B.positiveValueBand w c b e
  have hsub : ∀ᵐ v ∂μ, v ∈ π.rule.earlyValueDifference B w c (2*w*b/c) → v ∈ L ∪ G := by
    filter_upwards [hybrid_combined_clocks_regular B.individuals B.intensity π.seedLaw] with v hv hE
    exact π.rule.earlyValueDifference_loss_or_boundary B hw hc hb he v hv.1 hE
  have hmono : μ.real (π.rule.earlyValueDifference B w c (2*w*b/c)) ≤ μ.real (L ∪ G) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  calc
    _ ≤ μ.real L+μ.real G := hmono.trans (measureReal_union_le L G)
    _ ≤ _ := add_le_add (π.valueLossLevel_probability_le_regret B ha hw hc.le he0) le_rfl

lemma RandomizedHybridPolicy.expectedValueOutcomeError_nonnegative (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) : 0 ≤ π.expectedValueOutcomeError B w c :=
  integral_nonneg (π.rule.coupledValueOutcomeError_nonnegative B w c)

lemma RandomizedHybridPolicy.expectedValueOutcomeError_le_bound (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) {H w c : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.expectedValueOutcomeError B w c ≤ H+1 := by
  have h := integral_mono_ae (π.rule.integrable_coupledValueOutcomeError π.measurable_rule B π.seedLaw hw hc)
    (integrable_const (H+1)) (by
      filter_upwards [realized_values_bounds B.individuals B.intensity π.seedLaw B.individual_bounded B.intensity_supported,
        hybrid_combined_clocks_regular B.individuals B.intensity π.seedLaw] with v hx ht
      exact π.rule.coupledValueOutcomeError_le_bound B w c v hH (fun k => (hx k).1)
        (fun k => ((hx k).2).trans hCap) (fun k => (ht.2 k).1.le))
  simpa only [RandomizedHybridPolicy.expectedValueOutcomeError,integral_const,probReal_univ,one_smul] using h

/-- Explicit cap/weight/window estimate before choosing a uniform modulus. -/
theorem RandomizedHybridPolicy.expectedValueOutcomeError_le_window (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {H w c b d e : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hw : 0 < w) (hc : 0 < c)
    (hb : 0 < b) (hd : 0 ≤ d) (he0 : 0 < e) (he : e ≤ w*b/4) (hwindow : 2*w*b/c ≤ 1) :
    π.expectedValueOutcomeError B w c ≤ 2*w*b/c+
      (H+1)*((B.optimalScalarValue w c-π.scalarObjective B w c)/e+
        (B.law π.seedLaw).real (B.positiveValueBand w c b e))+
      d+H*(2*w*b/c)*B.tailCount d := by
  let μ := B.law π.seedLaw
  let window := 2*w*b/c
  let E := π.rule.earlyValueDifference B w c window
  let I : HybridWorld n π.Seed → ℝ := E.indicator (fun _ => 1)
  have hw0 : 0 ≤ window := by dsimp only [window]; positivity
  have hE : MeasurableSet E := π.rule.measurableSet_earlyValueDifference π.measurable_rule B hw.le hc.le window
  have hI : Integrable I μ := (integrable_const (1 : ℝ)).indicator hE
  have hIeq : (∫ v, I v ∂μ) = μ.real E := integral_indicator_one hE
  have hLate := B.integrable_hybridLateMaximum π.seedLaw (1-window)
  have hRHS : Integrable (fun v => window+(H+1)*I v+hybridLateMaximum (1-window) v) μ :=
    ((integrable_const window).add (hI.const_mul (H+1))).add hLate
  have hPoint : ∀ᵐ v ∂μ, π.rule.coupledValueOutcomeError B w c v ≤
      window+(H+1)*I v+hybridLateMaximum (1-window) v := by
    filter_upwards [realized_values_bounds B.individuals B.intensity π.seedLaw B.individual_bounded B.intensity_supported,
      hybrid_combined_clocks_regular B.individuals B.intensity π.seedLaw] with v hx ht
    simpa only [I,Set.indicator_apply,Pi.one_apply] using
      π.rule.coupledValueOutcomeError_le_window B w c v hH hw0 (fun k => (hx k).1)
        (fun k => ((hx k).2).trans hCap) (fun k => (ht.2 k).1.le)
  have h := integral_mono_ae (π.rule.integrable_coupledValueOutcomeError π.measurable_rule B π.seedLaw hw.le hc.le) hRHS hPoint
  rw [integral_add (μ := μ) (f := fun v => window+(H+1)*I v)
      (g := hybridLateMaximum (1-window)) ((integrable_const window).add (hI.const_mul (H+1))) hLate,
    integral_add (μ := μ) (f := fun _ => window) (g := fun v => (H+1)*I v)
      (integrable_const window) (hI.const_mul (H+1)),integral_const_mul,hIeq] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  have hEarly := π.earlyValueDifference_probability B ha hw hc hb he0 he
  have hMul := mul_le_mul_of_nonneg_left hEarly (show 0 ≤ H+1 by linarith)
  have hTerminal := B.integral_hybridLateMaximum_le π.seedLaw hH hCap hd hw0 hwindow
  change π.expectedValueOutcomeError B w c ≤ _ at h
  dsimp only [E,window] at h
  nlinarith only [h,hMul,hTerminal]

end ProphetSecretary.Limiting
