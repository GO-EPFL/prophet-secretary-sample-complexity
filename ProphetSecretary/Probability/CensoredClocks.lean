import ProphetSecretary.Model.FirstArrival
import ProphetSecretary.Probability.ProductConditioning
import Mathlib.Probability.Process.Filtration

/-!
# Censored independent uniform clocks

At elapsed time `t`, the clock history records `min(U_i,t)` for each identity.
Thus every arrival before `t`, including a zero-valued offer's identity, is retained.
Refreshing only pending clocks with independent uniform residual clocks preserves
the original product law. The history sigma algebras increase with elapsed time.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Probability

variable {n : ℕ}

def censorClocks (t : ℝ) (u : Fin n → ℝ) : Fin n → ℝ := fun i => min (u i) t

lemma measurable_censorClocks (t : ℝ) : Measurable (censorClocks (n := n) t) :=
  measurable_pi_lambda _ (fun i => (measurable_pi_apply i).min measurable_const)

lemma censorClocks_comp {s t : ℝ} (hst : s ≤ t) (u : Fin n → ℝ) :
    censorClocks s (censorClocks t u) = censorClocks s u := by
  funext i
  simp only [censorClocks, min_assoc, min_eq_right hst]

abbrev clockHistorySigma (n : ℕ) (t : ℝ) : MeasurableSpace (Fin n → ℝ) :=
  (MeasurableSpace.pi : MeasurableSpace (Fin n → ℝ)).comap (censorClocks t)

lemma clockHistorySigma_le (n : ℕ) (t : ℝ) :
    clockHistorySigma n t ≤ (MeasurableSpace.pi : MeasurableSpace (Fin n → ℝ)) :=
  (measurable_censorClocks t).comap_le

lemma clockHistorySigma_mono {s t : ℝ} (hst : s ≤ t) : clockHistorySigma n s ≤ clockHistorySigma n t := by
  have ht : @Measurable (Fin n → ℝ) (Fin n → ℝ) (clockHistorySigma n t) MeasurableSpace.pi
      (censorClocks t) := Measurable.of_comap_le le_rfl
  have h := (measurable_censorClocks s).comp ht
  have hs : @Measurable (Fin n → ℝ) (Fin n → ℝ) (clockHistorySigma n t) MeasurableSpace.pi
      (censorClocks s) := by
    convert h using 1
    funext u
    exact (censorClocks_comp hst u).symm
  exact hs.comap_le

def clockHistoryFiltration (n : ℕ) : Filtration ℝ (MeasurableSpace.pi : MeasurableSpace (Fin n → ℝ)) where
  seq t := clockHistorySigma n t
  mono' _ _ h := clockHistorySigma_mono h
  le' t := clockHistorySigma_le n t

noncomputable def refreshClock (t : ℝ) (q : ℝ × ℝ) : ℝ :=
  if q.1 < t then q.1 else Model.Instance.tailClock t q.2

lemma measurable_refreshClock (t : ℝ) : Measurable (refreshClock t) :=
  Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_fst
    (measurable_const.add (measurable_const.mul measurable_snd))

/-- Resampling a uniform clock only when it is still pending preserves its law. -/
lemma refreshClock_measurePreserving {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    MeasurePreserving (refreshClock t) (Model.Instance.uniformClock.prod Model.Instance.uniformClock)
      Model.Instance.uniformClock := by
  refine ⟨measurable_refreshClock t, ?_⟩
  apply Measure.ext
  intro s hs
  have htail : Measurable (Model.Instance.tailClock t) :=
    measurable_const.add (measurable_const.mul measurable_id)
  have hpre : refreshClock t ⁻¹' s =
      ((s ∩ Iio t) ×ˢ (Set.univ : Set ℝ)) ∪ ((Ici t) ×ˢ (Model.Instance.tailClock t ⁻¹' s)) := by
    ext q
    by_cases hq : q.1 < t
    · simp [refreshClock, hq, not_le_of_gt hq]
    · simp [refreshClock, hq, le_of_not_gt hq]
  have hdis : Disjoint ((s ∩ Iio t) ×ˢ (Set.univ : Set ℝ))
      ((Ici t) ×ˢ (Model.Instance.tailClock t ⁻¹' s)) := by
    apply Set.disjoint_left.mpr
    intro q hq hq'
    exact (not_le_of_gt (show q.1 < t from hq.1.2)) (show t ≤ q.1 from hq'.1)
  have hm : MeasurableSet ((Ici t) ×ˢ (Model.Instance.tailClock t ⁻¹' s)) :=
    measurableSet_Ici.prod (htail hs)
  have hrestrict := Model.Instance.uniformClock_restrict_Ici ht0 ht1
  have hmass : Model.Instance.uniformClock (Ici t) = ENNReal.ofReal (1 - t) := by
    have h := congrArg (fun μ : Measure ℝ => μ Set.univ) hrestrict
    simpa [Measure.map_apply htail MeasurableSet.univ] using h
  have htailMass : Model.Instance.uniformClock (Ici t) *
      Model.Instance.uniformClock (Model.Instance.tailClock t ⁻¹' s) =
      Model.Instance.uniformClock (s ∩ Ici t) := by
    have h := congrArg (fun μ : Measure ℝ => μ s) hrestrict
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.map_apply htail hs] at h
    rw [hmass]
    exact h.symm
  rw [Measure.map_apply (measurable_refreshClock t) hs, hpre, measure_union hdis hm,
    Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, htailMass]
  simpa only [Set.sdiff_eq, compl_Iio] using
    (measure_inter_add_sdiff (μ := Model.Instance.uniformClock) s (show MeasurableSet (Iio t) from measurableSet_Iio))

noncomputable def refreshClocks (t : ℝ) (q : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  fun i => refreshClock t (q.1 i, q.2 i)

lemma measurable_refreshClocks (t : ℝ) : Measurable (refreshClocks (n := n) t) :=
  measurable_pi_lambda _ (fun i => (measurable_refreshClock t).comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)))

lemma refreshClocks_measurePreserving {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    MeasurePreserving (refreshClocks (n := n) t) ((Model.Instance.clocksLaw n).prod (Model.Instance.clocksLaw n))
      (Model.Instance.clocksLaw n) := by
  have hpair := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => Model.Instance.uniformClock) (fun _ => Model.Instance.uniformClock)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
  exact (measurePreserving_pi (fun _ : Fin n => Model.Instance.uniformClock.prod Model.Instance.uniformClock)
    (fun _ => Model.Instance.uniformClock) (fun _ => refreshClock_measurePreserving ht0 ht1)).comp hpair

lemma censor_refreshClock {t x v : ℝ} (ht1 : t ≤ 1) (hv : 0 ≤ v) :
    min (refreshClock t (x, v)) t = min x t := by
  by_cases hx : x < t
  · simp only [refreshClock, hx, ite_true]
  · have hxt : t ≤ x := le_of_not_gt hx
    have htv : t ≤ Model.Instance.tailClock t v := by
      dsimp [Model.Instance.tailClock]
      nlinarith
    simp only [refreshClock, hx, ite_false, min_eq_right hxt, min_eq_right htv]

lemma censor_refreshClocks {t : ℝ} (ht1 : t ≤ 1) (u v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    censorClocks t (refreshClocks t (u, v)) = censorClocks t u := by
  funext i
  exact censor_refreshClock ht1 (hv i)

end ProphetSecretary.Probability
