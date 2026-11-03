import ProphetSecretary.Statistics.PlannerSampler

/-!
# Density contributions of the direct planner sampler

Write `D = insert i C` for a nonempty sampled subset containing the chosen
identity. The uniform-identity mass cancels the maximum-uniform density's
cardinality factor. The two powers of the remaining-time fraction then
combine, leaving the powerset expansion of the planner kernel.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics

variable {ι : Type*} [DecidableEq ι]

/-- Density contribution from `D = insert i C`, including the independent
Bernoulli choices for identities not in `D`. -/
noncomputable def plannerTransitionContribution (A : Finset ι) (p : ι → ℝ)
    (i : ι) (B C : Finset ι) (s : ℝ) : ℝ :=
  ((∏ j ∈ insert i C, (4 * p j)) / (plannerWeight A p - 1)) *
    ((1 / ((C.card + 1 : ℕ) : ℝ)) *
      (((C.card + 1 : ℕ) : ℝ) * s ^ C.card)) *
    s ^ (B.card - C.card) * (1 - s) ^ ((A.erase i).card - B.card)

lemma plannerTransitionContribution_eq (A : Finset ι) (p : ι → ℝ)
    (i : ι) (B C : Finset ι) (s : ℝ) (hi : i ∉ B) (hC : C ⊆ B) :
    plannerTransitionContribution A p i B C s =
      (4 * p i / (plannerWeight A p - 1)) *
        ((∏ j ∈ C, (4 * p j)) * s ^ B.card *
          (1 - s) ^ ((A.erase i).card - B.card)) := by
  have hiC : i ∉ C := fun h => hi (hC h)
  have hd : (((C.card + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hCancel : (1 / ((C.card + 1 : ℕ) : ℝ)) *
      (((C.card + 1 : ℕ) : ℝ) * s ^ C.card) = s ^ C.card := by
    field_simp
  have hPow : s ^ C.card * s ^ (B.card - C.card) = s ^ B.card := by
    rw [← pow_add, Nat.add_sub_of_le (Finset.card_le_card hC)]
  unfold plannerTransitionContribution
  rw [hCancel, Finset.prod_insert hiC]
  calc
    (4 * p i * ∏ j ∈ C, (4 * p j)) / (plannerWeight A p - 1) * s ^ C.card *
        s ^ (B.card - C.card) * (1 - s) ^ ((A.erase i).card - B.card) =
      (4 * p i / (plannerWeight A p - 1)) *
        ((∏ j ∈ C, (4 * p j)) * (s ^ C.card * s ^ (B.card - C.card)) *
          (1 - s) ^ ((A.erase i).card - B.card)) := by ring
    _ = _ := by rw [hPow]

/-- Summing over the possible companions of `i` gives exactly `K_A`'s density. -/
lemma plannerTransitionContribution_sum (A : Finset ι) (p : ι → ℝ)
    (i : ι) (B : Finset ι) (s : ℝ) (hB : B ⊆ A.erase i) :
    (∑ C ∈ B.powerset, plannerTransitionContribution A p i B C s) =
      plannerKernelDensity A p i B s := by
  have hi : i ∉ B := fun h => (Finset.mem_erase.mp (hB h)).1 rfl
  have h : (∑ C ∈ B.powerset, plannerTransitionContribution A p i B C s) =
      ∑ C ∈ B.powerset, (4 * p i / (plannerWeight A p - 1)) *
        ((∏ j ∈ C, (4 * p j)) * s ^ B.card *
          (1 - s) ^ ((A.erase i).card - B.card)) := by
    apply Finset.sum_congr rfl
    intro C hC
    exact plannerTransitionContribution_eq A p i B C s hi (Finset.mem_powerset.mp hC)
  rw [h]
  exact plannerKernelDensity_expansion A p i B s

/-- Indices of the direct sampler: the first subset, chosen identity, and
additional successes among the identities outside the first subset. -/
def PlannerSamplerIndex (A : Finset ι) :=
  {z : Finset ι × ι × Finset ι // z.1 ⊆ A ∧ z.2.1 ∈ z.1 ∧ z.2.2 ⊆ A \ z.1}

/-- Indices of the density calculation: identity, final unseen set, and
companions of the chosen identity in the first subset. -/
def PlannerDensityIndex (A : Finset ι) :=
  {z : ι × Finset ι × Finset ι // z.1 ∈ A ∧ z.2.1 ⊆ A.erase z.1 ∧ z.2.2 ⊆ z.2.1}

/-- The reindexing used to sum the direct sampler's density contributions. -/
def plannerSamplerIndexEquiv (A : Finset ι) : PlannerSamplerIndex A ≃ PlannerDensityIndex A where
  toFun z := ⟨(z.1.2.1, z.1.1.erase z.1.2.1 ∪ z.1.2.2, z.1.1.erase z.1.2.1), by
    rcases z with ⟨⟨D, i, T⟩, hD, hi, hT⟩
    refine ⟨hD hi, ?_, Finset.subset_union_left⟩
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, hD (Finset.mem_erase.mp hj).2⟩
    · have h := Finset.mem_sdiff.mp (hT hj)
      exact Finset.mem_erase.mpr ⟨fun hji => h.2 (hji ▸ hi), h.1⟩⟩
  invFun z := ⟨(insert z.1.1 z.1.2.2, z.1.1, z.1.2.1 \ z.1.2.2), by
    rcases z with ⟨⟨i, B, C⟩, hi, hB, hC⟩
    refine ⟨?_, Finset.mem_insert_self _ _, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact (Finset.mem_erase.mp (hB (hC hj))).2
    · intro j hj
      have h := Finset.mem_sdiff.mp hj
      have hBase := Finset.mem_erase.mp (hB h.1)
      exact Finset.mem_sdiff.mpr ⟨hBase.2, by
        intro hji
        rcases Finset.mem_insert.mp hji with hji | hjC
        · exact hBase.1 hji
        · exact h.2 hjC⟩⟩
  left_inv z := by
    rcases z with ⟨⟨D, i, T⟩, hD, hi, hT⟩
    apply Subtype.ext
    dsimp
    apply Prod.ext
    · exact Finset.insert_erase hi
    · apply Prod.ext
      · rfl
      · ext j
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro ⟨hj | hj, hNot⟩
          · exact False.elim (hNot hj)
          · exact hj
        · intro hj
          have hNot := (Finset.mem_sdiff.mp (hT hj)).2
          exact ⟨Or.inr hj, fun h => hNot h.2⟩
  right_inv z := by
    rcases z with ⟨⟨i, B, C⟩, hi, hB, hC⟩
    have hiC : i ∉ C := fun h => (Finset.mem_erase.mp (hB (hC h))).1 rfl
    apply Subtype.ext
    dsimp
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rw [Finset.erase_insert hiC]
        ext j
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (h | h)
          · exact hC h
          · exact h.1
        · intro h
          by_cases hj : j ∈ C
          · exact Or.inl hj
          · exact Or.inr ⟨h, hj⟩
      · exact Finset.erase_insert hiC

end ProphetSecretary.Statistics
