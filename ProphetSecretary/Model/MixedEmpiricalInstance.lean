import ProphetSecretary.Model.EmpiricalTotalization
import ProphetSecretary.Model.BellmanResidualBasic

/-!
# Empirical laws with some marginals known exactly

The identities in `known` retain their supplied true laws. Every other identity
uses its empirical law from the stored samples. All identities remain present,
including zero-valued arrivals. Dependence on the supplied true instance is
restricted to the declared known marginals.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def mixedEmpiricalInstance (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) : Instance n where
  law i := if i∈known then P.law i else (totalEmpiricalInstance y).law i
  probability i := by
    split
    · exact P.probability i
    · exact (totalEmpiricalInstance y).probability i
  nonnegative i := by
    split
    · exact P.nonnegative i
    · exact (totalEmpiricalInstance y).nonnegative i

lemma mixedEmpiricalInstance_law_known (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) {i : Fin n} (hi : i∈known) :
    (mixedEmpiricalInstance P known y).law i = P.law i := by
  simp only [mixedEmpiricalInstance,if_pos hi]

lemma mixedEmpiricalInstance_law_unknown (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) {i : Fin n} (hi : i∉known) :
    (mixedEmpiricalInstance P known y).law i = (totalEmpiricalInstance y).law i := by
  simp only [mixedEmpiricalInstance,if_neg hi]

lemma mixedEmpiricalInstance_empty (P : Instance n) (y : Reservoir n k) :
    mixedEmpiricalInstance P ∅ y = totalEmpiricalInstance y := by
  apply Instance.eq_of_law_eq
  funext i
  simp [mixedEmpiricalInstance]

lemma mixedEmpiricalInstance_univ (P : Instance n) (y : Reservoir n k) :
    mixedEmpiricalInstance P Finset.univ y = P := by
  apply Instance.eq_of_law_eq
  funext i
  simp only [mixedEmpiricalInstance,Finset.mem_univ,if_true]

/-- Unknown true laws are not inputs to the mixed design instance. -/
lemma mixedEmpiricalInstance_congr_known {P Q : Instance n} (known : Finset (Fin n))
    (hknown : ∀ i∈known, P.law i=Q.law i) (y : Reservoir n k) :
    mixedEmpiricalInstance P known y = mixedEmpiricalInstance Q known y := by
  apply Instance.eq_of_law_eq
  funext i
  by_cases hi : i∈known
  · simp only [mixedEmpiricalInstance,if_pos hi,hknown i hi]
  · simp only [mixedEmpiricalInstance,if_neg hi]

/-- Known labels in the increasing enumeration of an unseen state. -/
def knownInState (known A : Finset (Fin n)) : Finset (Fin A.card) :=
  Finset.univ.filter fun j => stateEmbedding A j∈known

lemma mem_knownInState (known A : Finset (Fin n)) (j : Fin A.card) :
    j∈knownInState known A ↔ stateEmbedding A j∈known := by simp [knownInState]

lemma mixedEmpiricalInstance_restrictTo (P : Instance n) (known A : Finset (Fin n))
    (y : Reservoir n k) :
    (mixedEmpiricalInstance P known y).restrictTo A =
      mixedEmpiricalInstance (P.restrictTo A) (knownInState known A)
        (fun j l => y (stateEmbedding A j) l) := by
  apply Instance.eq_of_law_eq
  funext j
  change (if stateEmbedding A j∈known then P.law (stateEmbedding A j)
    else (totalEmpiricalInstance y).law (stateEmbedding A j)) =
      (if j∈knownInState known A then (P.restrictTo A).law j
        else (totalEmpiricalInstance (fun j l => y (stateEmbedding A j) l)).law j)
  simp only [mem_knownInState]
  rfl

lemma mixedEmpiricalInstance_integrable (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (y : Reservoir n k) :
    Integrable Instance.maximum (mixedEmpiricalInstance P known y).valuesLaw := by
  apply (mixedEmpiricalInstance P known y).integrable_maximum_iff.mpr
  intro i
  by_cases hi : i∈known
  · rw [mixedEmpiricalInstance_law_known P known y hi]
    exact P.integrable_maximum_iff.mp hP i
  · rw [mixedEmpiricalInstance_law_unknown P known y hi]
    exact (totalEmpiricalInstance y).integrable_maximum_iff.mp (totalEmpiricalInstance_integrable y) i

lemma mixedEmpiricalInstance_bounded (P : Instance n) (known : Finset (Fin n)) (y : Reservoir n k)
    {H : ℝ} (hH : 0≤H) (hP : ∀ i, ∀ᵐ x ∂P.law i, x≤H) (hy : ∀ i l, y i l≤H) :
    ∀ i, ∀ᵐ x ∂(mixedEmpiricalInstance P known y).law i, x≤H := by
  intro i
  by_cases hi : i∈known
  · rw [mixedEmpiricalInstance_law_known P known y hi]
    exact hP i
  · rw [mixedEmpiricalInstance_law_unknown P known y hi]
    exact totalEmpiricalInstance_bounded y hH hy i

lemma mixedEmpiricalInstance_integral_known (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) {i : Fin n} (hi : i∈known) (f : ℝ → ℝ) :
    (∫ x, f x ∂(mixedEmpiricalInstance P known y).law i) = ∫ x, f x ∂P.law i := by
  rw [mixedEmpiricalInstance_law_known P known y hi]

lemma mixedEmpiricalInstance_integral_unknown (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) {i : Fin n} (hi : i∉known) (f : ℝ → ℝ) :
    (∫ x, f x ∂(mixedEmpiricalInstance P known y).law i) = (k:ℝ)⁻¹*∑ l : Fin k, f (max 0 (y i l)) := by
  rw [mixedEmpiricalInstance_law_unknown P known y hi]
  exact totalEmpiricalInstance_integral y i f

end ProphetSecretary.Model
