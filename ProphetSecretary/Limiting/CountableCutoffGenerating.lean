import ProphetSecretary.Limiting.BandGeneratingFunctional
import ProphetSecretary.Limiting.CountablePoissonIndependence

/-!
# Joint generating tests for the actual cutoff counting measure

The measurable test regions may overlap. Their product of point factors is
handled by the full generating functional, avoiding any assumption of
independence for overlapping counts.
-/

open MeasureTheory ProbabilityTheory Set Filter Complex
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance) {ι : Type*} [Fintype ι]

lemma intensityAbove_configuration_marks {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    ∀ᵐ ω ∂configurationLaw (B.intensityAbove b hb), ∀ j : Fin ω.1, b < (ω.2 j).2 := by
  have hm : ∀ᵐ x ∂(B.intensityAbove b hb : Measure ℝ), b < x := ae_restrict_mem measurableSet_Ioi
  have hp : ∀ᵐ p : Point ∂ProphetSecretary.Limiting.intensity (B.intensityAbove b hb), p.2 ∈ Ioi b :=
    (Measure.quasiMeasurePreserving_snd (μ := Model.Instance.uniformClock)
      (ν := (B.intensityAbove b hb : Measure ℝ))).ae hm
  exact all_points_in_of_intensity_compl_null (B.intensityAbove b hb)
    ((measurableSet_Ioi (a := b)).preimage measurable_snd) (ae_iff.mp hp)

theorem cutoff_counts_joint_generating {b : ℝ} (hb : (B.terminal : ℝ) < b)
    (S : ι → Set Point) (hS : ∀ i, MeasurableSet (S i))
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∫ ω, ∏ i, z i ^ bandPointCount (S i ∩ (univ ×ˢ Ioi b)) ω ∂B.bandConfigurationsLaw) =
      (∫ ω, ∏ i, z i ^ pointCount (S i) ω ∂configurationLaw (B.intensityAbove b hb)) := by
  let R := fun i => S i ∩ (univ ×ˢ Ioi b)
  let g := fun p => ∏ i, pointFactor (R i) (z i) p
  have hR i : MeasurableSet (R i) := (hS i).inter (MeasurableSet.univ.prod measurableSet_Ioi)
  have hg : Measurable g := Finset.measurable_fun_prod _ (fun i _ => measurable_pointFactor (hR i) (z i))
  have hn (p : Point) : ‖g p‖ ≤ 1 := by
    dsimp only [g]
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => pointFactor_norm_le_one (R i) (hz i) p)
  have hbelow (p : Point) (hp : p.2 ≤ b) : g p = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have hpR : p ∉ R i := fun h => (not_lt_of_ge hp) h.2.2
    simp only [pointFactor,if_neg hpR]
  obtain ⟨K,hK⟩ := B.eventually_bands_below hb
  have heq : ∀ᵐ ω ∂B.bandConfigurationsLaw, ∀ i,
      bandPointCount (R i) ω = ∑ k : Fin (K+1), pointCount (R i) (ω k) := by
    filter_upwards [ae_all_iff.mpr (fun i => B.bandPointCount_region_eq_sum (hR i) (fun _ h => h.2) hK)] with ω hω
    intro i
    exact (hω i).trans (Finset.sum_range (n := K+1) (fun k : ℕ => pointCount (R i) (ω k)))
  have hpoint (ω : BandConfigurations) :
      (∏ i, z i ^ (∑ k : Fin (K+1), pointCount (R i) (ω k))) =
        ∏ k : Fin (K+1), pointProd g (ω k) := by
    calc
      _ = ∏ i, ∏ k : Fin (K+1), z i ^ pointCount (R i) (ω k) := by
        apply Finset.prod_congr rfl
        intro i _
        exact (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ = ∏ k : Fin (K+1), ∏ i, z i ^ pointCount (R i) (ω k) := Finset.prod_comm
      _ = _ := Finset.prod_congr rfl (fun k _ => (pointProd_prod_pointFactor R z (ω k)).symm)
  calc
    _ = ∫ ω, ∏ k : Fin (K+1), pointProd g (ω k) ∂B.bandConfigurationsLaw := by
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      change (∏ i, z i ^ bandPointCount (R i) ω) = _
      simp_rw [hω]
      exact hpoint ω
    _ = ∫ ω, pointProd g ω ∂configurationLaw (B.intensityAbove b hb) :=
      B.finiteBands_generating_above hb hK g hg hn hbelow
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [B.intensityAbove_configuration_marks hb] with ω hω
      have hc (i) : pointCount (R i) ω = pointCount (S i) ω := by
        unfold pointCount
        apply Finset.sum_congr rfl
        intro j _
        simp only [R,mem_inter_iff,mem_prod,mem_univ,mem_Ioi,hω j,and_true]
      change pointProd (fun p => ∏ i, pointFactor (R i) (z i) p) ω = _
      rw [pointProd_prod_pointFactor]
      simp only [hc]

end ProphetSecretary.Limiting.CountableInstance
