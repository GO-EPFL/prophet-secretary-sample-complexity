import ProphetSecretary.Limiting.AppendIIDState

/-!
# A retained state with every virtual identity still present

The finite label set contains exactly the specified original identities and
the full virtual iid block. Its retained and virtual projections are proved
explicitly, before comparing the corresponding optimal values.
-/
open Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n q : ℕ}

noncomputable def completeVirtualState (q : ℕ) (A : Finset (Fin n)) : Finset (Fin (n+q)) :=
  A.map (Fin.castAddEmb q) ∪ Finset.univ.map (Fin.natAddEmb n)

lemma mem_completeVirtualState_left (A : Finset (Fin n)) (i : Fin n) :
    i.castAdd q ∈ completeVirtualState q A ↔ i ∈ A := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hA | hQ
    · obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hA
      have he : j = i := Fin.castAdd_inj.mp hji
      simpa only [he] using hj
    · obtain ⟨j,_,hji⟩ := Finset.mem_map.mp hQ
      have hh := congrArg Fin.val hji
      simp only [Fin.natAddEmb_apply,Fin.val_natAdd,Fin.val_castAdd] at hh
      omega
  · intro hi
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨i,hi,rfl⟩))

lemma mem_completeVirtualState_right (A : Finset (Fin n)) (j : Fin q) :
    j.natAdd n ∈ completeVirtualState q A :=
  Finset.mem_union.mpr (Or.inr (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩))

lemma completeVirtualState_retained (A : Finset (Fin n)) :
    Model.retainedSet q (completeVirtualState q A) = A := by
  ext i
  simp only [Model.retainedSet,Finset.mem_filter,Finset.mem_univ,true_and,mem_completeVirtualState_left]

lemma completeVirtualState_virtual (A : Finset (Fin n)) :
    virtualSet n (completeVirtualState q A) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro j
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem_completeVirtualState_right A j⟩

lemma completeVirtualState_mono {A D : Finset (Fin n)} (h : A ⊆ D) :
    completeVirtualState q A ⊆ completeVirtualState q D := by
  intro k hk
  rcases Finset.mem_union.mp hk with hA | hQ
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hA
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨i,h hi,rfl⟩))
  · exact Finset.mem_union.mpr (Or.inr hQ)

end ProphetSecretary.Limiting
