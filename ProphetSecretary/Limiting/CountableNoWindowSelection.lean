import ProphetSecretary.Limiting.CountableCanonicalPositiveWindow
import ProphetSecretary.Limiting.IntensityClockNull

/-!
# Zero duration response excludes selected Poisson window points

With zero complete-window duration score, an independent inserted point has
the original base duration. Its fresh uniform clock almost surely differs
from that duration. The Mecke kernel testing equality of the inserted
infimum and the point's clock therefore has zero integral. Any actual
selected window point would contribute one to its Mecke sum, a contradiction.
No first-attainment hypothesis is imposed on an inserted-point slice.
-/
open MeasureTheory Set Filter
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def CountableRule.insertionDurationMatchKernel (π : CountableRule Seed) (k : ℕ)
    (S : Set ℝ) (z : Point × CompleteWorld Seed) : ℝ≥0∞ :=
  if z.1.2 ∈ S ∧ π.insertionInfimumKernel k z=z.1.1 then 1 else 0

lemma CountableRule.measurable_insertionDurationMatchKernel (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (k : ℕ) {S : Set ℝ} (hS : MeasurableSet S) : Measurable (π.insertionDurationMatchKernel k S) :=
  Measurable.ite ((hS.preimage (measurable_snd.comp measurable_fst)).inter
    (measurableSet_eq_fun (π.measurable_insertionInfimumKernel hπ k) (measurable_fst.comp measurable_fst)))
    measurable_const measurable_const

theorem valueRule_no_selected_poisson_window (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S ⊆ Ioi b)
    (hZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
      ∂B.completeWorldLaw (Measure.dirac ()))=0) (k : ℕ) :
    ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ j : Fin (v.1 k).1, ((v.1 k).2 j).2 ∈ S →
        ¬FirstAcceptance.Earliest (B.valueRule w c).codeAccepted codeTime v
          (candidateEnumeration (Sum.inr (k,j.val))) := by
  let π := B.valueRule w c
  let F := π.insertionDurationMatchKernel k S
  have hπ : π.IsMeasurable := B.valueRule_isMeasurable hw.le hc.le
  have hF : Measurable F := π.measurable_insertionDurationMatchKernel hπ k hS
  have hInserted := B.valueRule_positiveWindow_insertion_eq_actual_of_durationScore_zero hw hc hS hb hSub hZero k
  have hClock := intensity_time_ne_measurable_ae (B.bandIntensity k) (B.completeWorldLaw (Measure.dirac ()))
    π.realizedDuration (π.measurable_realizedDuration hπ)
  have hKernelZero : F =ᵐ[(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod
      (B.completeWorldLaw (Measure.dirac ()))] (fun _ => 0) := by
    filter_upwards [hInserted,hClock] with z hz hTime
    change (if z.1.2 ∈ S ∧ π.insertionInfimumKernel k z=z.1.1 then (1 : ℝ≥0∞) else 0)=0
    apply if_neg
    rintro ⟨hMark,hEq⟩
    exact hTime (hEq.symm.trans (hz hMark))
  have hRight : (∫⁻ z, F z ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod
      (B.completeWorldLaw (Measure.dirac ())))=0 := by
    rw [lintegral_congr_ae hKernelZero,lintegral_zero]
  have hLeft := (B.band_mecke (Measure.dirac ()) k F hF).trans hRight
  have hSumZero := (lintegral_eq_zero_iff' (measurable_bandMeckeSum k F hF).aemeasurable).mp hLeft
  filter_upwards [hSumZero] with v hv j hMark hSelected
  have hInf : π.infimumDuration v=((v.1 k).2 j).1 := by
    have h := FirstAcceptance.infimumTime_of_earliest
      (A := π.codeAccepted) (u := codeTime) (ω := v) (fun _ h => h.2.1) hSelected
    change π.infimumDuration v=codeTime v (candidateEnumeration (Sum.inr (k,j.val))) at h
    rw [codeTime,poisson_candidate_point] at h
    exact h
  have hRecovery : π.insertionInfimumKernel k (((v.1 k).2 j),eraseAnonymousPoint k v j)=π.infimumDuration v :=
    B.valueRule_infimumDuration_append_erased w c k v j
  have hTerm : F (((v.1 k).2 j),eraseAnonymousPoint k v j)=1 := by
    change (if ((v.1 k).2 j).2 ∈ S ∧ π.insertionInfimumKernel k (((v.1 k).2 j),eraseAnonymousPoint k v j)=
      ((v.1 k).2 j).1 then (1 : ℝ≥0∞) else 0)=1
    exact if_pos ⟨hMark,hRecovery.trans hInf⟩
  have hOne : (1 : ℝ≥0∞) ≤ bandMeckeSum k F v := by
    rw [bandMeckeSum_eq]
    calc
      _ = F (((v.1 k).2 j),eraseAnonymousPoint k v j) := hTerm.symm
      _ ≤ ∑ l : Fin (v.1 k).1, F (((v.1 k).2 l),eraseAnonymousPoint k v l) :=
        Finset.single_le_sum (f := fun l : Fin (v.1 k).1 => F (((v.1 k).2 l),eraseAnonymousPoint k v l))
          (fun l _ => bot_le) (Finset.mem_univ j)
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ≥0∞)<1)) (hOne.trans_eq hv)

end ProphetSecretary.Limiting.CountableInstance
