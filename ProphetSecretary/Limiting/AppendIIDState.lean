import ProphetSecretary.Limiting.FiniteArrayEvaluation
import ProphetSecretary.Model.ZeroAppendContinuation
import ProphetSecretary.Model.Reindex

/-!
# Relabeling retained and iid coordinates of an actual finite state

A subset of an appended independent family consists of its retained subset
and its selected iid labels. The equivalence below preserves every label and
its marginal law before applying the proved general-policy value invariance.
No zero-valued history is deleted by this relabeling.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n N : ℕ}

noncomputable def virtualSet (n : ℕ) (A : Finset (Fin (n+N))) : Finset (Fin N) :=
  Finset.univ.filter fun j => j.natAdd n ∈ A

noncomputable def appendStateSumLabel (A : Finset (Fin (n+N))) :
    Fin (Model.retainedSet N A).card ⊕ Fin (virtualSet n A).card → A
  | Sum.inl i => ⟨(Model.stateEmbedding (Model.retainedSet N A) i).castAdd N,
      (Finset.mem_filter.mp ((Model.retainedSet N A).orderEmbOfFin_mem rfl i)).2⟩
  | Sum.inr j => ⟨(Model.stateEmbedding (virtualSet n A) j).natAdd n,
      (Finset.mem_filter.mp ((virtualSet n A).orderEmbOfFin_mem rfl j)).2⟩

lemma appendStateSumLabel_injective (A : Finset (Fin (n+N))) : Function.Injective (appendStateSumLabel A) := by
  intro a b h
  have hv := congrArg (fun z : A => (z : Fin (n+N))) h
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have he : Model.stateEmbedding (Model.retainedSet N A) i = Model.stateEmbedding (Model.retainedSet N A) j := by
        simpa only [appendStateSumLabel,Fin.castAdd_inj] using hv
      exact congrArg Sum.inl ((Model.stateEmbedding _).injective he)
    | inr j =>
      have hh := congrArg Fin.val hv
      simp only [appendStateSumLabel,Fin.val_castAdd,Fin.val_natAdd] at hh
      have hi := (Model.stateEmbedding (Model.retainedSet N A) i).isLt
      omega
  | inr i =>
    cases b with
    | inl j =>
      have hh := congrArg Fin.val hv
      simp only [appendStateSumLabel,Fin.val_castAdd,Fin.val_natAdd] at hh
      have hj := (Model.stateEmbedding (Model.retainedSet N A) j).isLt
      omega
    | inr j =>
      have he : Model.stateEmbedding (virtualSet n A) i = Model.stateEmbedding (virtualSet n A) j := by
        simpa only [appendStateSumLabel,Fin.natAdd_inj] using hv
      exact congrArg Sum.inr ((Model.stateEmbedding _).injective he)

lemma appendStateSumLabel_surjective (A : Finset (Fin (n+N))) : Function.Surjective (appendStateSumLabel A) := by
  intro a
  rcases a with ⟨a,ha⟩
  revert ha
  induction a using Fin.addCases with
  | left i =>
    intro ha
    have hi : i ∈ Model.retainedSet N A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
    let k := ((Model.retainedSet N A).orderIsoOfFin rfl).symm ⟨i,hi⟩
    have hk : Model.stateEmbedding (Model.retainedSet N A) k = i := by
      change (((Model.retainedSet N A).orderIsoOfFin rfl)
        (((Model.retainedSet N A).orderIsoOfFin rfl).symm ⟨i,hi⟩) : Fin n) = i
      rw [OrderIso.apply_symm_apply]
    refine ⟨Sum.inl k,Subtype.ext ?_⟩
    change (Model.stateEmbedding (Model.retainedSet N A) k).castAdd N = i.castAdd N
    rw [hk]
  | right j =>
    intro ha
    have hj : j ∈ virtualSet n A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
    let k := ((virtualSet n A).orderIsoOfFin rfl).symm ⟨j,hj⟩
    have hk : Model.stateEmbedding (virtualSet n A) k = j := by
      change (((virtualSet n A).orderIsoOfFin rfl)
        (((virtualSet n A).orderIsoOfFin rfl).symm ⟨j,hj⟩) : Fin N) = j
      rw [OrderIso.apply_symm_apply]
    refine ⟨Sum.inr k,Subtype.ext ?_⟩
    change (Model.stateEmbedding (virtualSet n A) k).natAdd n = j.natAdd n
    rw [hk]

noncomputable def appendStateEquiv (A : Finset (Fin (n+N))) :
    Fin ((Model.retainedSet N A).card+(virtualSet n A).card) ≃ Fin A.card :=
  (finSumFinEquiv.symm.trans (Equiv.ofBijective (appendStateSumLabel A)
    ⟨appendStateSumLabel_injective A,appendStateSumLabel_surjective A⟩)).trans (A.orderIsoOfFin rfl).toEquiv.symm

lemma appendStateEquiv_left (A : Finset (Fin (n+N))) (i : Fin (Model.retainedSet N A).card) :
    Model.stateEmbedding A (appendStateEquiv A (i.castAdd (virtualSet n A).card)) =
      (Model.stateEmbedding (Model.retainedSet N A) i).castAdd N := by
  unfold appendStateEquiv
  simp only [Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd]
  change ((A.orderIsoOfFin rfl) ((A.orderIsoOfFin rfl).symm (appendStateSumLabel A (Sum.inl i))) : Fin (n+N)) = _
  rw [OrderIso.apply_symm_apply]
  rfl

lemma appendStateEquiv_right (A : Finset (Fin (n+N))) (j : Fin (virtualSet n A).card) :
    Model.stateEmbedding A (appendStateEquiv A (j.natAdd (Model.retainedSet N A).card)) =
      (Model.stateEmbedding (virtualSet n A) j).natAdd n := by
  unfold appendStateEquiv
  simp only [Equiv.trans_apply,finSumFinEquiv_symm_apply_natAdd]
  change ((A.orderIsoOfFin rfl) ((A.orderIsoOfFin rfl).symm (appendStateSumLabel A (Sum.inr j))) : Fin (n+N)) = _
  rw [OrderIso.apply_symm_apply]
  rfl

/-- Exact continuation-state value decomposition, with no iid restriction on
the retained marginals and no restriction on the competing policy class. -/
theorem appendIID_restrictTo_value (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (N : ℕ) (A : Finset (Fin (n+N)))
    (hQ : Integrable Model.Instance.maximum (appendIID P κ hκ N).valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Model.optimalScalarValue ((appendIID P κ hκ N).restrictTo A) w c =
      Model.optimalScalarValue (appendIID (P.restrictTo (Model.retainedSet N A)) κ hκ (virtualSet n A).card) w c := by
  symm
  apply ((appendIID P κ hκ N).restrictTo A).optimalScalarValue_eq_of_law_equiv
    (appendIID (P.restrictTo (Model.retainedSet N A)) κ hκ (virtualSet n A).card) (appendStateEquiv A)
  · intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [appendIID,Model.Instance.restrictTo,Model.Instance.restrictBy,Fin.addCases_left]
      rw [appendStateEquiv_left]
      simp only [Fin.addCases_left]
    | right j =>
      simp only [appendIID,Model.Instance.restrictTo,Model.Instance.restrictBy,Fin.addCases_right]
      rw [appendStateEquiv_right]
      simp only [Fin.addCases_right]
  · exact (appendIID P κ hκ N).restrictTo_integrable_maximum A hQ
  · exact hw
  · exact hc

end ProphetSecretary.Limiting
