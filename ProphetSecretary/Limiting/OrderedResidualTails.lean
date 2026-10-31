import ProphetSecretary.Limiting.OrderedPaddedLaws

/-!
# Uniform rare-tail control from the actual mean ordering

The bounds hold after zero padding, uniformly over finite instance size. In the
S≤S₀ extraction subcase, they give both residual maximum exceedance tending to
zero and the residual square-sum bound needed for causal Poisson comparison.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma orderedPaddedLaw_tail_le_mean (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {b : ℝ} (hb : 0 < b) (j : ℕ) :
    (orderedPaddedLaw P j : Measure ℝ).real (Ioi b) ≤ (∫ x, x ∂(orderedPaddedLaw P j : Measure ℝ)) / b := by
  let ν : Measure ℝ := orderedPaddedLaw P j
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := ν) (f := fun x : ℝ => x)
    (orderedPaddedLaw_nonnegative P j) (orderedPaddedLaw_integrable_id P hP j) b
  have hsub : ν.real (Ioi b) ≤ ν.real (Ici b) := measureReal_mono Ioi_subset_Ici_self
  have hmul := (mul_le_mul_of_nonneg_left hsub hb.le).trans hm
  apply (le_div_iff₀ hb).mpr
  simpa only [mul_comm] using hmul

/-- The largest probability after the first N retained coordinates is at most
S₀/[b(N+1)], with zero-based retained indexing made explicit. -/
theorem orderedPaddedLaw_residual_tail_le (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {S₀ b : ℝ}
    (hS : P.totalFirstMoment ≤ S₀) (hb : 0 < b) {N j : ℕ} (hNj : N ≤ j) :
    (orderedPaddedLaw P j : Measure ℝ).real (Ioi b) ≤ S₀ / (b * (N+1 : ℕ)) := by
  have hp := (orderedPaddedLaw_tail_le P hP hb j).trans
    (div_le_div_of_nonneg_right hS (by positivity : 0 ≤ b * (j+1 : ℕ)))
  have hpMul := (le_div_iff₀ (by positivity : 0 < b * (j+1 : ℕ))).mp hp
  have hRank : ((N+1 : ℕ) : ℝ) ≤ ((j+1 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.add_le_add_right hNj 1)
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRank hb.le)
    (measureReal_nonneg (μ := (orderedPaddedLaw P j : Measure ℝ)) (s := Ioi b))
  apply (le_div_iff₀ (by positivity : 0 < b * (N+1 : ℕ))).mpr
  nlinarith only [hm,hpMul]

/-- Uniform residual rarity, stronger than the corresponding limsup-over-
instances conclusion: N is chosen before both the instance and its tail index. -/
theorem orderedPaddedLaw_residual_tail_uniform (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (hP : ∀ m, Integrable Model.Instance.maximum (P m).valuesLaw) {S₀ b : ℝ}
    (hS : ∀ m, (P m).totalFirstMoment ≤ S₀) (hb : 0 < b) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m j, N ≤ j → (orderedPaddedLaw (P m) j : Measure ℝ).real (Ioi b) < ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (S₀ / (b * ε))
  have hsmall : S₀ / (b * (N+1 : ℕ)) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < b * (N+1 : ℕ))).mpr
    have hscale := (div_lt_iff₀ (mul_pos hb hε)).mp hN
    have hstep : (N : ℝ) < ((N+1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self N
    have hmul := mul_lt_mul_of_pos_left hstep (mul_pos hb hε)
    nlinarith only [hscale,hmul]
  exact ⟨N,fun m j hj => (orderedPaddedLaw_residual_tail_le (P m) (hP m) (hS m) hb hj).trans_lt hsmall⟩

lemma sum_orderedPadded_means (P : Model.Instance n) :
    (∑ i : Fin n, ∫ x, x ∂(orderedPaddedLaw P i.val : Measure ℝ)) = P.totalFirstMoment := by
  calc
    _ = ∑ i : Fin n, ∫ x, x ∂(orderedMarginalLaw P i : Measure ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [orderedPaddedLaw_of_lt P i.isLt]
    _ = _ := sum_ordered_marginal_means P

/-- Actual finite square-sum control, independent of the number of residual
variables, for the S≤S₀ extraction subcase. -/
theorem orderedPaddedLaw_residual_tail_square_sum_le (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {S₀ b : ℝ}
    (hS₀ : 0 ≤ S₀) (hS : P.totalFirstMoment ≤ S₀) (hb : 0 < b) (N : ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
      (orderedPaddedLaw P i.val : Measure ℝ).real (Ioi b) ^ 2) ≤ S₀ ^ 2 / (b ^ 2 * (N+1 : ℕ)) := by
  let p : Fin n → ℝ := fun i => (orderedPaddedLaw P i.val : Measure ℝ).real (Ioi b)
  let A := Finset.univ.filter (fun i : Fin n => N ≤ i.val)
  let M := S₀ / (b * (N+1 : ℕ))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hp (i : Fin n) : 0 ≤ p i := measureReal_nonneg
  have htotal : (∑ i : Fin n, p i) ≤ S₀ / b := by
    calc
      _ ≤ ∑ i : Fin n, (∫ x, x ∂(orderedPaddedLaw P i.val : Measure ℝ)) / b :=
        Finset.sum_le_sum fun i _ => orderedPaddedLaw_tail_le_mean P hP hb i.val
      _ = P.totalFirstMoment / b := by rw [← Finset.sum_div,sum_orderedPadded_means P]
      _ ≤ _ := div_le_div_of_nonneg_right hS hb.le
  have hres : (∑ i ∈ A, p i) ≤ S₀ / b :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hp i)).trans htotal
  calc
    (∑ i ∈ A, p i ^ 2) ≤ ∑ i ∈ A, M * p i := by
      apply Finset.sum_le_sum
      intro i hi
      have hbnd : p i ≤ M := orderedPaddedLaw_residual_tail_le P hP hS hb (Finset.mem_filter.mp hi).2
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hbnd (hp i)
    _ = M * ∑ i ∈ A, p i := by rw [Finset.mul_sum]
    _ ≤ M * (S₀ / b) := mul_le_mul_of_nonneg_left hres hM
    _ = _ := by dsimp [M]; field_simp

end ProphetSecretary.Limiting
