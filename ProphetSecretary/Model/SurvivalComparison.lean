import ProphetSecretary.Model.PrefixSurvival
import ProphetSecretary.Model.BellmanOptimal
import ProphetSecretary.Model.Reindex

/-!
# Continuation duration after prefix survival

A fresh child has fewer unseen options than the pending execution. Its canonical
threshold is therefore lower. The comparison uses the actual unseen histories,
including every zero-valued observation in the prefix.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- Independent auxiliary randomness may appear in an observable prefix multiplier,
while the deterministic canonical rule ignores that extra seed. -/
def Policy.withAuxiliarySeed {Seed : Type*} (π : Policy Unit n) : Policy Seed n where
  decide _ := π.decide ()

lemma Policy.withAuxiliarySeed_pendingTime {Seed : Type*} (π : Policy Unit n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) :
    π.withAuxiliarySeed.pendingTime r x u i = π.pendingTime () x u i := rfl

lemma Policy.withAuxiliarySeed_isMeasurable {Seed : Type*} [MeasurableSpace Seed]
    (π : Policy Unit n) (hπ : π.IsMeasurable) : (π.withAuxiliarySeed (Seed := Seed)).IsMeasurable := by
  exact hπ.comp (measurable_const.prodMk measurable_snd)

lemma splitClocks_stateEmbedding (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A)
    (t : ℝ) (v : Fin n → ℝ) (j : Fin A.card) :
    splitClocks A i t v (stateEmbedding A j) = t + (1 - t) * v (stateEmbedding A j) := by
  have hj : stateEmbedding A j ∈ A := A.orderEmbOfFin_mem rfl j
  have hji : stateEmbedding A j ≠ i := by rintro h; exact hAi (h ▸ hj)
  simp [splitClocks, splitClock, hji, hj, Instance.tailClock]

lemma unseen_fresh_subset_pending (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A)
    {t : ℝ} (ht : t ≤ 1) (x v : Fin n → ℝ) (k : Fin A.card) :
    (unseen (history Finset.univ (x ∘ stateEmbedding A) (v ∘ stateEmbedding A)
      (v (stateEmbedding A k)))).map (stateEmbedding A) ⊆
      unseen (history (Finset.univ.erase i) x (splitClocks A i t v)
        (splitClocks A i t v (stateEmbedding A k))) := by
  intro j hj
  obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hj
  have hkl : v (stateEmbedding A k) ≤ v (stateEmbedding A l) := by
    simpa [unseen, history, Function.comp_apply] using hl
  have hclock : splitClocks A i t v (stateEmbedding A k) ≤ splitClocks A i t v (stateEmbedding A l) := by
    rw [splitClocks_stateEmbedding A i hAi, splitClocks_stateEmbedding A i hAi]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hkl (sub_nonneg.mpr ht))
  simp only [unseen, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold history
  rw [if_neg (fun h => (not_lt_of_ge hclock) h.2)]

lemma Instance.canonical_child_accepts_of_pending (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A)
    {w c t : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (ht : t ≤ 1) (x v : Fin n → ℝ)
    (k : Fin A.card)
    (ha : (P.valuePolicy hP hw.le hc).rule.action () (Finset.univ.erase i)
      x (splitClocks A i t v) (stateEmbedding A k) = true) :
    ((P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP)
      hw.le (mul_nonneg hc (sub_nonneg.mpr ht))).rule.action () Finset.univ
        (x ∘ stateEmbedding A) (v ∘ stateEmbedding A) k = true := by
  simp only [Policy.action, Instance.valuePolicy, thresholdPolicy, decide_eq_true_eq] at ha ⊢
  let B := unseen (history Finset.univ (x ∘ stateEmbedding A) (v ∘ stateEmbedding A)
    (v (stateEmbedding A k)))
  have hk : k ∈ B := by simp [B, unseen, history]
  have hsub := unseen_fresh_subset_pending A i hAi ht x v k
  have hthreshold := P.valueThreshold_monotone hP hw hc ()
    (splitClocks A i t v (stateEmbedding A k)) (stateEmbedding A k)
    (B.map (stateEmbedding A)) _ (Finset.mem_map.mpr ⟨k, hk, rfl⟩) hsub
  have htransport := P.valueThreshold_restrictBy (A.orderEmbOfFin rfl) B k hP hw.le
    (mul_nonneg hc (sub_nonneg.mpr ht)) (v (stateEmbedding A k))
  change (P.restrictTo A).valueThreshold w (c * (1 - t)) B (v (stateEmbedding A k)) k ≤ x (stateEmbedding A k)
  rw [show (P.restrictTo A).valueThreshold w (c * (1 - t)) B (v (stateEmbedding A k)) k =
    P.valueThreshold w c (B.map (stateEmbedding A)) (splitClocks A i t v (stateEmbedding A k)) (stateEmbedding A k) by
      rw [splitClocks_stateEmbedding A i hAi, P.valueThreshold_after_elapsed _ _ _ _ _ _ ht]
      exact htransport]
  exact hthreshold.trans ha

/-- On survival to a fixed time, canonical pending duration dominates the
actual canonical child duration after the remaining-horizon rescaling. -/
lemma Instance.pendingTime_ge_rescaled_child (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A)
    {w c t : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (ht0 : 0 < t) (ht1 : t < 1)
    (x v : Fin n → ℝ) (hv : ∀ j, v j < 1)
    (hsurvive : t ≤ (P.valuePolicy hP hw.le hc).rule.pendingTime () x (splitClocks A i t v) i) :
    t + (1 - t) * ((P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP)
      hw.le (mul_nonneg hc (sub_nonneg.mpr ht1.le))).rule.stoppingTime () Finset.univ
        (x ∘ stateEmbedding A) (v ∘ stateEmbedding A) ≤
      (P.valuePolicy hP hw.le hc).rule.pendingTime () x (splitClocks A i t v) i := by
  let π := (P.valuePolicy hP hw.le hc).rule
  let ψ := ((P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP)
      hw.le (mul_nonneg hc (sub_nonneg.mpr ht1.le))).rule
  change t + (1 - t) * ψ.stoppingTime () Finset.univ (x ∘ stateEmbedding A) (v ∘ stateEmbedding A) ≤
    π.stoppingTime () (Finset.univ.erase i) x (splitClocks A i t v)
  apply (π.le_stoppingTime_iff _ _ _ _ _).mpr
  refine ⟨?_, ?_⟩
  · have hstop := ψ.stoppingTime_le_one () Finset.univ (x ∘ stateEmbedding A) (v ∘ stateEmbedding A)
    nlinarith
  · intro j hj
    obtain ⟨hjD, hact⟩ := (π.mem_accepted _ _ _ _ _).mp hj
    have hji : j ≠ i := (Finset.mem_erase.mp hjD).1
    have hjA : j ∈ A := by
      by_contra hjA
      have hclock : splitClocks A i t v j = t * v j := by simp [splitClocks, splitClock, hji, hjA]
      have htime := π.stoppingTime_le_of_accepted () (Finset.univ.erase i) x (splitClocks A i t v) j hj
      rw [hclock] at htime
      have hless : t * v j < t := by nlinarith [hv j]
      exact (not_lt_of_ge (hsurvive.trans htime)) hless
    let k := stateIndex A j hjA
    have he : stateEmbedding A k = j := stateEmbedding_stateIndex A j hjA
    have hchild := P.canonical_child_accepts_of_pending hP A i hAi hw hc ht1.le x v k (by simpa [he] using hact)
    have hchildtime := ψ.stoppingTime_le_of_accepted () Finset.univ (x ∘ stateEmbedding A) (v ∘ stateEmbedding A) k
      ((ψ.mem_accepted _ _ _ _ _).mpr ⟨Finset.mem_univ _, hchild⟩)
    rw [← he, splitClocks_stateEmbedding A i hAi]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hchildtime (sub_nonneg.mpr ht1.le))

end ProphetSecretary.Model
