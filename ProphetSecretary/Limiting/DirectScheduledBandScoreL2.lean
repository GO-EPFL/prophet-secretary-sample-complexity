import ProphetSecretary.Limiting.DirectScheduledCloudProperties
import ProphetSecretary.Model.Restriction

/-!
# The zero-atom score and its actual centered count

Once the deterministic cutoff lies below the scored set, its marginal mass
is exactly the limiting intensity divided by the same base virtual count.
The complete score then differs from the centered virtual band count by an
explicit squared-mean error at most `2 * intensity ^ 2 / count`. Restricting
the actual product values proves this on the full original offer vector.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

lemma directVirtualOfferLaw_set_mass_of_cutoff_le (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    (m : ℕ) (hm : B.markCutoff m≤b) :
    (B.directVirtualOfferLaw hZero m:Measure ℝ).real S=B.intensity.real S/(B.directVirtualCount hZero m:ℝ) := by
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  rw [B.directVirtualOfferLaw_positive_set_mass hZero m hS hS0]
  have hSub' : S⊆Ioi (B.markCutoff m) := fun _ hx => hm.trans_lt (hSub hx)
  change ((B.intensity.restrict (Ioi (B.markCutoff m))).real S)/_= _
  rw [Measure.real,Measure.restrict_apply hS,inter_eq_left.mpr hSub']
  rfl

lemma directScheduled_bandScore_count_error_measurable (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b) (m : ℕ) :
    Measurable (fun x : Fin (m+B.directVirtualCount hZero m) → ℝ =>
      completeScore (B.directScheduledCloudScore hZero S m) x-
        (countIn S (fun j => x (j.natAdd m))-B.intensity.real S)) := by
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  have hZ := measurable_completeScore (B.directScheduledCloudScore_properties hZero hS hS0 m).1
  have hCount : Measurable (fun x : Fin (m+B.directVirtualCount hZero m) → ℝ => countIn S (fun j => x (j.natAdd m))) := by
    apply Finset.measurable_sum
    intro j _
    exact (measurable_const.indicator hS).comp (measurable_pi_apply (j.natAdd m))
  exact hZ.sub (hCount.sub_const _)

lemma directScheduled_bandScore_count_error_integrable_sq (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b) (m : ℕ) :
    Integrable (fun x => (completeScore (B.directScheduledCloudScore hZero S m) x-
      (countIn S (fun j => x (j.natAdd m))-B.intensity.real S))^2)
      (B.directFiniteApproximation hZero m).valuesLaw := by
  let N := B.directVirtualCount hZero m
  let κ := (B.directVirtualOfferLaw hZero m:Measure ℝ)
  let P := B.directFiniteApproximation hZero m
  let Q := B.directVirtualOfferInstance hZero m
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  let F : (Fin N → ℝ) → ℝ := fun x =>
    (completeScore (fun _ : Fin N => ProphetSecretary.Probability.bandScore κ S) x-(countIn S x-B.intensity.real S))^2
  have hInt : Integrable F Q.valuesLaw :=
    completeBandScore_centeredCount_integrable_sq κ hS hS0 (B.directVirtualOfferLaw_zero_mass_ge_half hZero m) N _
  have hQ : P.restrictBy (Fin.natAddEmb m)=Q := by
    rw [show P=B.directFiniteApproximation hZero m from rfl,B.directFiniteApproximation_eq_appendVirtual hZero m]
    apply Instance.eq_of_law_eq
    funext j
    change ((B.individualPrefix m).appendIndependent Q).law (j.natAdd m)=Q.law j
    exact (B.individualPrefix m).appendIndependent_law_right Q j
  have hMP := P.restrictValues_measurePreserving (Fin.natAddEmb m)
  rw [hQ] at hMP
  apply (hMP.integrable_comp_of_integrable hInt).congr
  exact Eventually.of_forall (fun x => by
    dsimp only [Function.comp_apply]
    rw [directScheduledCloudScore,directCloudScore_complete]
    rfl)

 theorem directScheduled_bandScore_count_error_le (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    (m : ℕ) (hm : B.markCutoff m≤b) :
    (∫ x, (completeScore (B.directScheduledCloudScore hZero S m) x-
      (countIn S (fun j => x (j.natAdd m))-B.intensity.real S))^2
      ∂(B.directFiniteApproximation hZero m).valuesLaw)≤2*(B.intensity.real S)^2/(B.directVirtualCount hZero m:ℝ) := by
  let N := B.directVirtualCount hZero m
  let κ := (B.directVirtualOfferLaw hZero m:Measure ℝ)
  let P := B.directFiniteApproximation hZero m
  let Q := B.directVirtualOfferInstance hZero m
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  let F : (Fin N → ℝ) → ℝ := fun x =>
    (completeScore (fun _ : Fin N => ProphetSecretary.Probability.bandScore κ S) x-(countIn S x-B.intensity.real S))^2
  have hInt : Integrable F Q.valuesLaw :=
    completeBandScore_centeredCount_integrable_sq κ hS hS0 (B.directVirtualOfferLaw_zero_mass_ge_half hZero m) N _
  have hQ : P.restrictBy (Fin.natAddEmb m)=Q := by
    rw [show P=B.directFiniteApproximation hZero m from rfl,B.directFiniteApproximation_eq_appendVirtual hZero m]
    apply Instance.eq_of_law_eq
    funext j
    change ((B.individualPrefix m).appendIndependent Q).law (j.natAdd m)=Q.law j
    exact (B.individualPrefix m).appendIndependent_law_right Q j
  have hMP := P.restrictValues_measurePreserving (Fin.natAddEmb m)
  rw [hQ] at hMP
  have hEq := hMP.hasLaw.integral_comp hInt.aestronglyMeasurable
  have hRep : (∫ x, (completeScore (B.directScheduledCloudScore hZero S m) x-
      (countIn S (fun j => x (j.natAdd m))-B.intensity.real S))^2 ∂P.valuesLaw)=∫ x, F x ∂Q.valuesLaw := by
    convert hEq using 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      dsimp only
      rw [directScheduledCloudScore,directCloudScore_complete]
      rfl)
  rw [hRep]
  exact completeBandScore_centeredCount_L2 κ hS hS0 (B.directVirtualOfferLaw_zero_mass_ge_half hZero m) N
    (B.directVirtualCount_positive hZero m) (B.directVirtualOfferLaw_set_mass_of_cutoff_le hZero hS hb hSub m hm)

 theorem directScheduled_bandScore_count_error_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b) :
    Tendsto (fun m => ∫ x, (completeScore (B.directScheduledCloudScore hZero S m) x-
      (countIn S (fun j => x (j.natAdd m))-B.intensity.real S))^2
      ∂(B.directFiniteApproximation hZero m).valuesLaw) atTop (𝓝 (0:ℝ)) := by
  have hRate : Tendsto (fun m => 2*(B.intensity.real S)^2/(B.directVirtualCount hZero m:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (B.directVirtualCount_tendsto hZero))
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) _ hRate
  filter_upwards [B.markCutoff_tendsto.eventually (gt_mem_nhds hb)] with m hm
  exact B.directScheduled_bandScore_count_error_le hZero hS hb hSub m hm.le
end ProphetSecretary.Limiting.CountableInstance
