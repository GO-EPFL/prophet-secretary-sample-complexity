import ProphetSecretary.Model.ZeroVariableValue

/-!
# Continuation states with appended zero identities

Deleting identities whose distributions are deterministic zero preserves the
optimal scalar value, although their actual observations remain part of a policy
history. In particular, an appended zero block cannot reveal an anonymous count
through the continuation potential.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n m : ℕ}

lemma Instance.optimalScalarValue_restrictTo_inter_of_zero (P : Instance n)
    (A D : Finset (Fin n)) (hP : Integrable Instance.maximum P.valuesLaw)
    (hz : ∀ i ∉ D, P.law i = Measure.dirac 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue (P.restrictTo A) w c = optimalScalarValue (P.restrictTo (A ∩ D)) w c := by
  refine Finset.strongInductionOn A ?_
  intro A ih
  by_cases hAD : A ⊆ D
  · rw [Finset.inter_eq_left.mpr hAD]
  · have hex : ∃ i ∈ A, i ∉ D := by
      by_contra h
      apply hAD
      intro i hi
      by_contra hiD
      exact h ⟨i, hi, hiD⟩
    obtain ⟨i, hiA, hiD⟩ := hex
    have he : (A.erase i) ∩ D = A ∩ D := by
      ext j
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · exact fun h => ⟨h.1.2, h.2⟩
      · intro h
        exact ⟨⟨fun hji => hiD (hji ▸ h.2), h.1⟩, h.2⟩
    calc
      _ = optimalScalarValue (P.restrictTo (A.erase i)) w c :=
        P.optimalScalarValue_restrictTo_erase_zero A i hP (hz i hiD) hw hc
      _ = _ := by rw [ih (A.erase i) (Finset.erase_ssubset hiA), he]

def retainedSet (m : ℕ) (A : Finset (Fin (n + m))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Fin.castAdd m i ∈ A)

lemma retainedSet_map_eq_inter (m : ℕ) (A : Finset (Fin (n + m))) :
    (retainedSet m A).map (Fin.castAddEmb m) = A ∩ Finset.univ.map (Fin.castAddEmb m) := by
  ext j
  simp only [Finset.mem_map, Finset.mem_inter, Finset.mem_univ, true_and,
    retainedSet, Finset.mem_filter, Fin.castAddEmb_apply]
  constructor
  · rintro ⟨i, hiA, rfl⟩
    exact ⟨hiA, ⟨i, rfl⟩⟩
  · rintro ⟨hjA, i, rfl⟩
    exact ⟨i, hjA, rfl⟩

lemma Instance.optimalScalarValue_appendZeros_restrictTo (P : Instance n) (m : ℕ)
    (A : Finset (Fin (n + m))) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue ((P.appendZeros m).restrictTo A) w c =
      optimalScalarValue (P.restrictTo (retainedSet m A)) w c := by
  let D : Finset (Fin (n + m)) := (Finset.univ : Finset (Fin n)).map (Fin.castAddEmb m)
  have hz : ∀ i ∉ D, (P.appendZeros m).law i = Measure.dirac 0 := by
    intro i hiD
    induction i using Fin.addCases with
    | left i => exact False.elim (hiD (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    | right j => simp [Instance.appendZeros]
  let e : Fin n ↪o Fin (n + m) := ⟨Fin.castAddEmb m, by intro a b; rfl⟩
  have hmap := (P.appendZeros m).optimalScalarValue_restrictTo_map e (retainedSet m A)
    (P.appendZeros_integrable_maximum m hP) hw hc
  have hemb : e.toEmbedding = Fin.castAddEmb m := rfl
  rw [hemb, P.restrictBy_appendZeros_castAdd m, retainedSet_map_eq_inter] at hmap
  exact ((P.appendZeros m).optimalScalarValue_restrictTo_inter_of_zero A D
    (P.appendZeros_integrable_maximum m hP) hz hw hc).trans hmap.symm

end ProphetSecretary.Model
