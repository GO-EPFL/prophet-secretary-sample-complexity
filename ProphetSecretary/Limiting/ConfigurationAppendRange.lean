import ProphetSecretary.Limiting.ConfigurationAppendPoint
import ProphetSecretary.Limiting.Mecke

/-!
# Point sets after deletion and reinsertion

Appending the deleted distinguished occurrence restores the original point
set, although its analytical array label may change. Multiplicities need not
be compared to identify the physical stopping duration of a Markov rule.
-/
open Set
open scoped Classical
namespace ProphetSecretary.Limiting

lemma range_appendConfigurationPoint (ω : Configuration) (p : Point) :
    Set.range (appendConfigurationPoint ω p).2=insert p (Set.range ω.2) := by
  ext y
  change (∃ j : Fin (ω.1+1), (if hj : j.val<ω.1 then ω.2 ⟨j.val,hj⟩ else p)=y) ↔
    y=p ∨ ∃ j : Fin ω.1, ω.2 j=y
  constructor
  · rintro ⟨j,hj⟩
    by_cases hOld : j.val<ω.1
    · rw [dif_pos hOld] at hj
      exact Or.inr ⟨⟨j.val,hOld⟩,hj⟩
    · rw [dif_neg hOld] at hj
      exact Or.inl hj.symm
  · rintro (hy|⟨j,hj⟩)
    · refine ⟨Fin.last ω.1,?_⟩
      simpa only [Fin.val_last,lt_self_iff_false,dite_false] using hy.symm
    · refine ⟨⟨j.val,Nat.lt_succ_of_lt j.isLt⟩,?_⟩
      simpa only [dif_pos j.isLt] using hj

lemma range_append_erasedPoint (ω : Configuration) (j : Fin ω.1) :
    Set.range (appendConfigurationPoint (erasePoint ω j) (ω.2 j)).2=Set.range ω.2 := by
  rw [range_appendConfigurationPoint]
  rcases ω with ⟨N,v⟩
  cases N with
  | zero => exact Fin.elim0 j
  | succ n =>
    change insert (v j) (Set.range (fun l : Fin n => v (j.succAbove l)))=Set.range v
    ext y
    simp only [Set.mem_insert_iff,Set.mem_range]
    constructor
    · rintro (hy|⟨l,hl⟩)
      · exact ⟨j,hy.symm⟩
      · exact ⟨j.succAbove l,hl⟩
    · rintro ⟨l,hl⟩
      by_cases hlj : l=j
      · exact Or.inl (hl.symm.trans (congrArg v hlj))
      · obtain ⟨q,hq⟩ := Fin.exists_succAbove_eq hlj
        exact Or.inr ⟨q,(congrArg v hq).trans hl⟩

end ProphetSecretary.Limiting
