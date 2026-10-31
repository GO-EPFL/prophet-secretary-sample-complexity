import ProphetSecretary.Model.OuterTaggedMaximum
import ProphetSecretary.Statistics.OuterTaggedTraining

/-!
# The causal outer cutoff statistic

For a nonempty instance the cutoff is the smallest tagged maximum in m full
training rounds. The empty instance is totalized at (0,0). Only the independent
uniform tags and the observed training transcript enter the statistic.
Paper correspondence: T_cut in `upouter:construction`.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def outerCutoffTaggedRows (m : ℕ) (hm : 1≤m) (a : Fin m → Fin n → ℝ × ℝ) : TaggedValue :=
  if hn : 0<n then Finset.univ.inf' (outerOfferIndices_nonempty (show 0<m by omega))
    (fun r => outerTaggedMaximum hn (a r)) else toLex (0,0)

lemma measurable_outerCutoffTaggedRows (m : ℕ) (hm : 1≤m) :
    Measurable (outerCutoffTaggedRows (n:=n) m hm) := by
  by_cases hn : 0<n
  · have hEach (r : Fin m) : Measurable (fun a : Fin m → Fin n → ℝ × ℝ => outerTaggedMaximum hn (a r)) :=
      (measurable_outerTaggedMaximum hn).comp (measurable_pi_apply r)
    have hInf : Measurable (Finset.univ.inf' (outerOfferIndices_nonempty (show 0<m by omega))
        (fun r (a : Fin m → Fin n → ℝ × ℝ) => outerTaggedMaximum hn (a r))) :=
      Finset.inf'_induction (outerOfferIndices_nonempty (show 0<m by omega)) _
        (fun _f hf _g hg => hf.inf hg) (fun r _ => hEach r)
    convert hInf using 1
    funext a
    simp only [outerCutoffTaggedRows,dif_pos hn,Finset.inf'_apply]
  · unfold outerCutoffTaggedRows
    simp only [dif_neg hn]
    exact measurable_const

noncomputable def outerCutoff (m : ℕ) (hm : 1≤m)
    (p : Reservoir n m × (Fin m → Fin n → ℝ)) : ℝ × ℝ :=
  ofLex (outerCutoffTaggedRows m hm (taggedTrainingRows p.1 p.2))

lemma measurable_outerCutoff (m : ℕ) (hm : 1≤m) : Measurable (outerCutoff (n:=n) m hm) := by
  have hTagged := (measurable_outerCutoffTaggedRows (n:=n) m hm).comp (measurable_taggedTrainingRows (n:=n) (q:=m))
  convert measurable_ofTaggedValue.comp hTagged using 1
  funext p
  rfl

noncomputable def outerCutoffFromTranscript (m : ℕ) (hm : 1≤m)
    (tags : Fin m → Fin n → ℝ) (T : Transcript n) : ℝ × ℝ :=
  outerCutoff m hm (decodedReservoir T,tags)

lemma measurable_outerCutoffFromTranscript (m : ℕ) (hm : 1≤m) :
    Measurable (fun p : (Fin m → Fin n → ℝ) × Transcript n => outerCutoffFromTranscript m hm p.1 p.2) := by
  have hInput : Measurable (fun p : (Fin m → Fin n → ℝ) × Transcript n =>
      ((decodedReservoir p.2 : Reservoir n m),p.1)) :=
    (measurable_decodedReservoir.comp measurable_snd).prodMk measurable_fst
  convert (measurable_outerCutoff (n:=n) m hm).comp hInput using 1
  funext p
  rfl

lemma outerCutoffFromTranscript_actual (m : ℕ) (hm : 1≤m)
    (tags : Fin m → Fin n → ℝ) (y : Reservoir n m) :
    outerCutoffFromTranscript m hm tags (trainingTranscript (requestAll m) tags y)=outerCutoff m hm (y,tags) := by
  unfold outerCutoffFromTranscript
  rw [decodedReservoir_trainingTranscript]

lemma outerCutoff_hardBudget (m : ℕ) (tags : Fin m → Fin n → ℝ) (y : Reservoir n m) (i : Fin n) :
    requests (trainingTranscript (requestAll m) tags y) i≤m := trainingTranscript_budget _ _ _ _

/-- Monotonicity of the true tagged CDF commutes with the finite cutoff minimum. -/
lemma outerCutoff_score_eq_inf (P : Instance n) (hn : 0<n) (m : ℕ) (hm : 1≤m)
    (a : Fin m → Fin n → ℝ × ℝ) :
    P.taggedVoidProbability (ofLex (outerCutoffTaggedRows m hm a))=
      Finset.univ.inf' (outerOfferIndices_nonempty (show 0<m by omega))
        (fun r => P.taggedVoidProbability (ofLex (outerTaggedMaximum hn (a r)))) := by
  simp_rw [←P.outerTaggedMaximum_cdf_eq_void hn]
  rw [outerCutoffTaggedRows,dif_pos hn]
  exact Finset.apply_inf'_eq_inf'_comp (outerOfferIndices_nonempty (show 0<m by omega))
    (orderCDF (P.outerTaggedMaximumLaw hn)) (fun x y => (orderCDF_monotone (P.outerTaggedMaximumLaw hn)).map_inf x y)

end ProphetSecretary.Statistics
