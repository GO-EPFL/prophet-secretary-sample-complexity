import ProphetSecretary.Model.ZeroSimulationProbability
import ProphetSecretary.Model.Reindex
import ProphetSecretary.Model.ContinuationTransport
import Mathlib.Logic.Equiv.Set

/-!
# Removing known zero variables from the scalar value

A general policy may use every zero-valued arrival identity. The reverse inequality
uses the constructed causal zero simulation, which preserves reward and increases
duration. Reindexing then removes arbitrary zero identities and sorted unseen states.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.restrictBy_appendZeros_castAdd (P : Instance n) (m : ℕ) :
    (P.appendZeros m).restrictBy (Fin.castAddEmb m) = P := by
  apply Instance.eq_of_law_eq
  funext i
  change (Fin.addCases P.law (fun _ : Fin m => Measure.dirac (0 : ℝ)) : Fin (n + m) → Measure ℝ) (i.castAdd m) = P.law i
  dsimp only
  simp only [Fin.addCases_left]

lemma Instance.optimalScalarValue_appendZeros (P : Instance n) (m : ℕ)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue (P.appendZeros m) w c = optimalScalarValue P w c := by
  apply le_antisymm
  · apply csSup_le (scalarValues_nonempty (P.appendZeros m) w c)
    rintro _ ⟨π, rfl⟩
    exact (RandomizedPolicy.scalarObjective_le_simulateZeros π P hP hc).trans
      (scalarObjective_le_optimal (RandomizedPolicy.simulateZeros π) P hP hw hc)
  · have h := optimalScalarValue_restrictBy_le (P.appendZeros m) (Fin.castAddEmb m)
      (P.appendZeros_integrable_maximum m hP) hw hc
    rwa [P.restrictBy_appendZeros_castAdd m] at h

/-- Keep exactly `A`; the independent zero histories outside `A` remain available
through the causal simulator used in the value comparison. -/
lemma Instance.optimalScalarValue_eq_restrictTo_of_zero_outside (P : Instance n) (A : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw) (hz : ∀ i ∉ A, P.law i = Measure.dirac 0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P w c = optimalScalarValue (P.restrictTo A) w c := by
  let D : Finset (Fin n) := Finset.univ \ A
  let eA : Fin A.card ≃ {i : Fin n // i ∈ A} := (A.orderIsoOfFin rfl).toEquiv
  let eD : Fin D.card ≃ {i : Fin n // i ∉ A} :=
    (D.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight (fun i => by simp [D]))
  let e : Fin (A.card + D.card) ≃ Fin n :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr eA eD).trans (Equiv.sumCompl (fun i : Fin n => i ∈ A)))
  have he : ∀ k, ((P.restrictTo A).appendZeros D.card).law k = P.law (e k) := by
    intro k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · change (Fin.addCases (P.restrictTo A).law (fun _ : Fin D.card => Measure.dirac (0 : ℝ)) : Fin (A.card + D.card) → Measure ℝ) (j.castAdd D.card) = _
      dsimp only
      rw [Fin.addCases_left]
      change P.law (stateEmbedding A j) = P.law (e (j.castAdd D.card))
      dsimp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    · change (Fin.addCases (P.restrictTo A).law (fun _ : Fin D.card => Measure.dirac (0 : ℝ)) : Fin (A.card + D.card) → Measure ℝ) (j.natAdd A.card) = _
      dsimp only
      rw [Fin.addCases_right]
      have heD : e (j.natAdd A.card) = (eD j).1 := by
        dsimp only [e, Equiv.trans_apply]
        rw [finSumFinEquiv_symm_apply_natAdd]
        rfl
      rw [heD, hz _ (eD j).2]
  have hr := P.optimalScalarValue_eq_of_law_equiv ((P.restrictTo A).appendZeros D.card) e he hP hw hc
  exact hr.symm.trans ((P.restrictTo A).optimalScalarValue_appendZeros D.card (P.restrictTo_integrable_maximum A hP) hw hc)

lemma Instance.optimalScalarValue_remove_zero (P : Instance n) (i : Fin n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hi : P.law i = Measure.dirac 0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P w c = optimalScalarValue (P.restrictTo (Finset.univ.erase i)) w c := by
  apply P.optimalScalarValue_eq_restrictTo_of_zero_outside _ hP _ hw hc
  intro j hj
  have hji : j = i := by
    by_contra hne
    exact hj (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
  simpa only [hji] using hi

/-- The same removal identity holds in every sorted continuation state. -/
lemma Instance.optimalScalarValue_restrictTo_erase_zero (P : Instance n) (A : Finset (Fin n)) (i : Fin n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hi : P.law i = Measure.dirac 0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue (P.restrictTo A) w c = optimalScalarValue (P.restrictTo (A.erase i)) w c := by
  by_cases hiA : i ∈ A
  · let k := stateIndex A i hiA
    have hek : stateEmbedding A k = i := stateEmbedding_stateIndex A i hiA
    have hki : (P.restrictTo A).law k = Measure.dirac 0 := by
      change P.law (stateEmbedding A k) = _
      rw [hek, hi]
    have hzero := (P.restrictTo A).optimalScalarValue_remove_zero k (P.restrictTo_integrable_maximum A hP) hki hw hc
    have hmap : (Finset.univ.erase k).map (stateEmbedding A) = A.erase i := by
      rw [Finset.map_erase]
      change (Finset.univ.map (A.orderEmbOfFin rfl).toEmbedding).erase (stateEmbedding A k) = _
      rw [A.map_orderEmbOfFin_univ rfl, hek]
    have hr := P.optimalScalarValue_restrictTo_map (A.orderEmbOfFin rfl) (Finset.univ.erase k) hP hw hc
    change optimalScalarValue ((P.restrictTo A).restrictTo (Finset.univ.erase k)) w c =
      optimalScalarValue (P.restrictTo ((Finset.univ.erase k).map (stateEmbedding A))) w c at hr
    rw [hmap] at hr
    exact hzero.trans hr
  · rw [Finset.erase_eq_of_notMem hiA]

end ProphetSecretary.Model
