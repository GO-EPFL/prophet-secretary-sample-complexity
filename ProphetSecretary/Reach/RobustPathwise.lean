import ProphetSecretary.Model.MultiJackpot
import ProphetSecretary.Reach.RareReach

/-!
# Pathwise multi-jackpot comparison

All dummy identities remain present in the comparison execution, with value zero.
The jackpot flags are analytical coupling variables and are not supplied to the policy.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model.MultiJackpot

variable {n N : ℕ} {Seed : Type*}

def bit (b : Fin N → Bool) (j : Fin N) : ℝ := if b j = true then 1 else 0

def bitCount (b : Fin N → Bool) : ℝ := ∑ j, bit b j

def pairCount (b : Fin N → Bool) : ℝ :=
  ∑ j, ∑ l, if j ≠ l then bit b j * bit b l else 0

lemma bit_nonnegative (b : Fin N → Bool) (j : Fin N) : 0 ≤ bit b j := by
  unfold bit; split_ifs <;> norm_num

lemma bit_le_one (b : Fin N → Bool) (j : Fin N) : bit b j ≤ 1 := by
  unfold bit; split_ifs <;> norm_num

lemma pairCount_nonnegative (b : Fin N → Bool) : 0 ≤ pairCount b := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro l _
  split_ifs
  · exact mul_nonneg (bit_nonnegative b j) (bit_nonnegative b l)
  · rfl

lemma pairCount_add_bitCount (b : Fin N → Bool) : pairCount b + bitCount b = bitCount b ^ 2 := by
  have hdiag (j : Fin N) : (∑ l : Fin N, if j = l then bit b j * bit b l else 0) = bit b j := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold bit
    split_ifs <;> norm_num
  have hrow (j : Fin N) :
      (∑ l : Fin N, if j ≠ l then bit b j * bit b l else 0) + bit b j = ∑ l, bit b j * bit b l := by
    calc
      _ = (∑ l : Fin N, if j ≠ l then bit b j * bit b l else 0) +
          (∑ l : Fin N, if j = l then bit b j * bit b l else 0) := by rw [hdiag]
      _ = ∑ l : Fin N, ((if j ≠ l then bit b j * bit b l else 0) +
          (if j = l then bit b j * bit b l else 0)) := (Finset.sum_add_distrib).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : j = l <;> simp [h]

  rw [pairCount, bitCount, ← Finset.sum_add_distrib]
  simp_rw [hrow]
  rw [← Finset.sum_mul_sum]
  ring

lemma bitCount_sub_pairCount_le_one (b : Fin N → Bool) : bitCount b - pairCount b ≤ 1 := by
  have h := pairCount_add_bitCount b
  nlinarith [sq_nonneg (bitCount b - 1)]

lemma pairCount_ge_one_of_multiple (b : Fin N → Bool)
    (h : ∃ j l, j ≠ l ∧ b j = true ∧ b l = true) : 1 ≤ pairCount b := by
  obtain ⟨j, l, hjl, hj, hl⟩ := h
  have hinner : 1 ≤ ∑ a : Fin N, if j ≠ a then bit b j * bit b a else 0 := by
    calc
      1 = (if j ≠ l then bit b j * bit b l else 0) := by simp [hjl, bit, hj, hl]
      _ ≤ _ := Finset.single_le_sum
        (f := fun a : Fin N => if j ≠ a then bit b j * bit b a else 0) (a := l)
        (fun a _ => by unfold bit; split_ifs <;> norm_num) (Finset.mem_univ l)
  apply hinner.trans
  unfold pairCount
  exact Finset.single_le_sum
    (f := fun a : Fin N => ∑ c : Fin N, if a ≠ c then bit b a * bit b c else 0) (a := j)
    (fun a _ => Finset.sum_nonneg fun c _ => by
      unfold bit; split_ifs <;> norm_num) (Finset.mem_univ j)

lemma jackpotValues_eq_zero_of_none (A : ℝ) (b : Fin N → Bool) (x : Fin n → ℝ)
    (h : ¬∃ j, b j = true) : jackpotValues A b x = ZeroSimulation.appendValues (m := N) x := by
  funext k
  induction k using Fin.addCases with
  | left i => simp [jackpotValues, ZeroSimulation.appendValues]
  | right j =>
    have hj : b j ≠ true := fun hj => h ⟨j, hj⟩
    simp [jackpotValues, ZeroSimulation.appendValues, hj]

lemma jackpotValues_eq_update_of_single (A : ℝ) (b : Fin N → Bool) (x : Fin n → ℝ)
    (j : Fin N) (hj : b j = true) (hm : ¬∃ l a, l ≠ a ∧ b l = true ∧ b a = true) :
    jackpotValues A b x = Function.update (ZeroSimulation.appendValues (m := N) x) (Fin.natAdd n j) A := by
  funext k
  induction k using Fin.addCases with
  | left i =>
    have hne : Fin.castAdd N i ≠ Fin.natAdd n j := ne_of_lt (by
      change i.val < n + j.val
      exact i.isLt.trans_le (Nat.le_add_right n j.val))
    rw [Function.update_of_ne hne]
    simp [jackpotValues, ZeroSimulation.appendValues]
  | right l =>
    by_cases hlj : l = j
    · subst l; simp [jackpotValues, hj]
    · have hl : b l ≠ true := fun hl => hm ⟨l, j, hlj, hl, hj⟩
      simp [jackpotValues, ZeroSimulation.appendValues, hl, hlj]

noncomputable def reachScore (π : Policy Seed (n + N)) (r : Seed) (x : Fin n → ℝ)
    (u : Fin (n + N) → ℝ) (b : Fin N → Bool) : ℝ :=
  ∑ j, if b j = true ∧ π.Reaches r (ZeroSimulation.appendValues x) u (Fin.natAdd n j) then 1 else 0

lemma reachScore_nonnegative (π : Policy Seed (n + N)) (r : Seed) (x : Fin n → ℝ)
    (u : Fin (n + N) → ℝ) (b : Fin N → Bool) : 0 ≤ reachScore π r x u b := by
  exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

lemma maximum_jackpotValues_lower (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (b : Fin N → Bool) (x : Fin n → ℝ) (hx : ∀ i, x i ≤ H) :
    Instance.maximum x + A * bitCount b - H * (if ∃ j, b j = true then 1 else 0) - A * pairCount b ≤
      Instance.maximum (jackpotValues A b x) := by
  by_cases h : ∃ j, b j = true
  · obtain ⟨j, hj⟩ := h
    have hmax := Instance.maximum_le x hH hx
    have hlarge : A ≤ Instance.maximum (jackpotValues A b x) := by
      have hh := Instance.le_maximum (jackpotValues A b x) (Fin.natAdd n j)
      simpa [jackpotValues, hj] using hh
    rw [if_pos ⟨j, hj⟩, mul_one]
    have hcount := mul_le_mul_of_nonneg_left (bitCount_sub_pairCount_le_one b) hA
    nlinarith
  · have hb : bitCount b = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hj : b j ≠ true := fun hj => h ⟨j, hj⟩
      simp [bit, hj]
    have hp : pairCount b = 0 := by nlinarith [pairCount_add_bitCount b]
    rw [if_neg h, hb, hp, jackpotValues_eq_zero_of_none A b x h,
      Instance.maximum_appendValues]
    simp

lemma reward_jackpotValues_upper (π : Policy Seed (n + N)) (r : Seed)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (b : Fin N → Bool) (x : Fin n → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx : ∀ i, x i ≤ H) (u : Fin (n + N) → ℝ) (hu : ∀ j, u j ≤ 1) :
    π.reward r Finset.univ (jackpotValues A b x) u ≤
      π.reward r Finset.univ (ZeroSimulation.appendValues x) u +
        H * (if ∃ j, b j = true then 1 else 0) +
        A * reachScore π r x u b + A * pairCount b := by
  have hxzero : ∀ j, 0 ≤ ZeroSimulation.appendValues (m := N) x j := by
    intro j
    induction j using Fin.addCases with
    | left i => simpa [ZeroSimulation.appendValues] using hx0 i
    | right j => simp [ZeroSimulation.appendValues]
  have hbase := π.reward_nonnegative r Finset.univ (ZeroSimulation.appendValues x) u hxzero
  have hrs := reachScore_nonnegative π r x u b
  have hpair := pairCount_nonnegative b
  by_cases hany : ∃ j, b j = true
  · rw [if_pos hany, mul_one]
    by_cases hmulti : ∃ j l, j ≠ l ∧ b j = true ∧ b l = true
    · have hpair1 := pairCount_ge_one_of_multiple b hmulti
      have hcap : π.reward r Finset.univ (jackpotValues A b x) u ≤ H + A := by
        apply (π.reward_le_maximum r Finset.univ (jackpotValues A b x) u).trans
        apply Instance.maximum_le _ (add_nonneg hH hA)
        intro k
        induction k using Fin.addCases with
        | left i => simpa [jackpotValues] using (hx i).trans (le_add_of_nonneg_right hA)
        | right j =>
          simp only [jackpotValues, Fin.addCases_right]
          split_ifs <;> linarith
      have hp := mul_le_mul_of_nonneg_left hpair1 hA
      nlinarith [mul_nonneg hA hrs]
    · by_cases hsel : ∃ k, π.ActualSelects r Finset.univ (jackpotValues A b x) u k
      · obtain ⟨k, hk⟩ := hsel
        rw [π.reward_eq_of_actualSelects r Finset.univ (jackpotValues A b x) u hk]
        induction k using Fin.addCases with
        | left i =>
          simp only [jackpotValues, Fin.addCases_left]
          nlinarith [hx i, mul_nonneg hA hrs, mul_nonneg hA hpair]
        | right j =>
          by_cases hj : b j = true
          · have hreach := π.selects_implies_reaches r (jackpotValues A b x) u hk.1
            rw [jackpotValues_eq_update_of_single A b x j hj hmulti] at hreach
            have hr0 := (π.reaches_update_value r (ZeroSimulation.appendValues x) u (Fin.natAdd n j) A (hu _)).mp hreach
            have hr1 : 1 ≤ reachScore π r x u b := by
              have hh : (if b j = true ∧ π.Reaches r (ZeroSimulation.appendValues x) u (Fin.natAdd n j) then (1 : ℝ) else 0) ≤
                  ∑ a : Fin N, if b a = true ∧ π.Reaches r (ZeroSimulation.appendValues x) u (Fin.natAdd n a) then (1 : ℝ) else 0 :=
                Finset.single_le_sum
                  (f := fun a : Fin N => if b a = true ∧ π.Reaches r (ZeroSimulation.appendValues x) u (Fin.natAdd n a) then (1 : ℝ) else 0)
                  (a := j) (fun a _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
              simpa only [if_pos (And.intro hj hr0), reachScore] using hh
            simp only [jackpotValues, Fin.addCases_right, if_pos hj]
            nlinarith [mul_le_mul_of_nonneg_left hr1 hA, mul_nonneg hA hpair]
          · simp only [jackpotValues, Fin.addCases_right, if_neg hj]
            positivity
      · rw [π.reward_eq_zero_of_no_actualSelection r Finset.univ (jackpotValues A b x) u (fun k hk => hsel ⟨k, hk⟩)]
        positivity
  · rw [if_neg hany, mul_zero, jackpotValues_eq_zero_of_none A b x hany]
    nlinarith [mul_nonneg hA hrs, mul_nonneg hA hpair]

end ProphetSecretary.Model.MultiJackpot
