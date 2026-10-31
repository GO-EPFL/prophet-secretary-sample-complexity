import ProphetSecretary.Statistics.FinitePriorHypothetical

/-!
# Exact information in the analytical hypothetical observation

The swapped next-prefix observation contains precisely the current training
prefix and ONLINE value vector. This sigma algebra is used only to evaluate a
conditional projection; the actual learner continues to see the training prefix.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

def appendOnlineRound (n N b k : ℕ) (hk : b+k<N)
    (d : ValueArray n N) (x : Fin n → ℝ) : ValueArray n N :=
  fun q => if q.2=nextColumn N b k hk then x q.1 else d q

lemma measurable_appendOnlineRound (n N b k : ℕ) (hk : b+k<N) :
    Measurable (fun p : ValueArray n N × (Fin n → ℝ) => appendOnlineRound n N b k hk p.1 p.2) := by
  apply measurable_pi_lambda
  intro q
  by_cases h : q.2=nextColumn N b k hk
  · simpa only [appendOnlineRound,if_pos h,Function.comp_def] using (measurable_pi_apply q.1).comp measurable_snd
  · simpa only [appendOnlineRound,if_neg h,Function.comp_def] using (measurable_pi_apply q).comp measurable_fst

lemma observe_swapped_next_eq_append (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) (ω : BaseWorld F N) :
    F.observe N b (k+1) (F.swapBaseEquiv N (nextColumn N b k hk) ω)=
      appendOnlineRound n N b k hk (F.observe N b k ω) (F.onlineValues ω) := by
  funext q
  rcases q with ⟨i,r⟩
  by_cases hj : r=nextColumn N b k hk
  · subst r
    have hmem : (i,nextColumn N b k hk)∈trainingCoordinates n N b (k+1) := by
      simp only [trainingCoordinates,Finset.mem_filter,Finset.mem_univ,true_and,nextColumn]
      omega
    simp only [observe,ProphetSecretary.Probability.maskCoordinates,if_pos hmem,
      swapBaseEquiv_apply,swapValueEquiv_apply,Equiv.swap_apply_left,appendOnlineRound,onlineValues,ite_true]
  · have hmem : (i,r)∈trainingCoordinates n N b (k+1) ↔ (i,r)∈trainingCoordinates n N b k := by
      simp only [trainingCoordinates,Finset.mem_filter,Finset.mem_univ,true_and]
      have hrv : r.val≠b+k := fun he => hj (Fin.ext he)
      omega
    by_cases h : (i,r)∈trainingCoordinates n N b k
    · have hN : r≠Fin.last N := by
        have hv : r.val<min (b+k) N := (Finset.mem_filter.mp h).2
        intro he
        have := congrArg Fin.val he
        simp only [Fin.val_last] at this
        omega
      simp only [observe,ProphetSecretary.Probability.maskCoordinates,if_pos h,if_pos (hmem.mpr h),
        swapBaseEquiv_apply,swapValueEquiv_apply,Equiv.swap_apply_of_ne_of_ne hj hN,
        appendOnlineRound,if_neg hj]
    · simp only [observe,ProphetSecretary.Probability.maskCoordinates,if_neg h,if_neg (hmem.not.mpr h),
        appendOnlineRound,if_neg hj]

/-- Training data together with online values are only an analytical observation. -/
abbrev onlineObservationSigma (F : FinitePrior n) (N b k : ℕ) : MeasurableSpace (BaseWorld F N) :=
  MeasurableSpace.comap (fun ω => (F.observe N b k ω,F.onlineValues ω)) inferInstance

lemma hypotheticalSigma_eq_onlineObservationSigma (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) :
    F.hypotheticalSigma N b k hk=F.onlineObservationSigma N b k := by
  let H : BaseWorld F N → ValueArray n N := fun ω =>
    F.observe N b (k+1) (F.swapBaseEquiv N (nextColumn N b k hk) ω)
  have hH : @Measurable (BaseWorld F N) (ValueArray n N) (F.hypotheticalSigma N b k hk) _ H := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap H _≤(MeasurableSpace.comap (F.observe N b (k+1)) _).comap
      (F.swapBaseEquiv N (nextColumn N b k hk))
    rw [MeasurableSpace.comap_comp]
    exact le_rfl
  apply le_antisymm
  · have hPair : @Measurable (BaseWorld F N) (ValueArray n N × (Fin n → ℝ))
        (F.onlineObservationSigma N b k) _ (fun ω => (F.observe N b k ω,F.onlineValues ω)) :=
      Measurable.of_comap_le le_rfl
    have h := (measurable_appendOnlineRound n N b k hk).comp hPair
    have h' : @Measurable (BaseWorld F N) (ValueArray n N) (F.onlineObservationSigma N b k) _ H := by
      convert h using 1
      funext ω
      exact F.observe_swapped_next_eq_append N b k hk ω
    change (MeasurableSpace.comap (F.observe N b (k+1)) _).comap
      (F.swapBaseEquiv N (nextColumn N b k hk))≤_
    rw [MeasurableSpace.comap_comp]
    exact h'.comap_le
  · have hOld : @Measurable (BaseWorld F N) (ValueArray n N) (F.hypotheticalSigma N b k hk) _
        (F.observe N b k) := by
      have h := (ProphetSecretary.Probability.measurable_maskCoordinates (trainingCoordinates n N b k)).comp hH
      convert h using 1
      funext ω
      change F.observe N b k ω=ProphetSecretary.Probability.maskCoordinates (trainingCoordinates n N b k)
        (F.observe N b (k+1) (F.swapBaseEquiv N (nextColumn N b k hk) ω))
      change F.observe N b k ω=ProphetSecretary.Probability.maskCoordinates (trainingCoordinates n N b k)
        (ProphetSecretary.Probability.maskCoordinates (trainingCoordinates n N b (k+1))
          (F.swapBaseEquiv N (nextColumn N b k hk) ω).2)
      rw [ProphetSecretary.Probability.maskCoordinates_subset (trainingCoordinates_mono n N b (Nat.le_succ k))]
      exact (F.observe_swap_next N b k hk ω).symm
    have hOnline : @Measurable (BaseWorld F N) (Fin n → ℝ) (F.hypotheticalSigma N b k hk) _ (F.onlineValues (N:=N)) := by
      letI : MeasurableSpace (BaseWorld F N) := F.hypotheticalSigma N b k hk
      refine measurable_pi_lambda _ (fun i => ?_)
      have h := (measurable_pi_apply (i,nextColumn N b k hk)).comp hH
      convert h using 1
      funext ω
      change F.onlineValues ω i=F.observe N b (k+1) (F.swapBaseEquiv N (nextColumn N b k hk) ω) (i,nextColumn N b k hk)
      rw [F.observe_swapped_next_eq_append]
      simp only [appendOnlineRound,ite_true]
    exact (hOld.prodMk hOnline).comap_le

/-- The analytical posterior really is E[Q | current training, online values]. -/
theorem hypotheticalPosterior_eq_online_condExp (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) :
    F.hypotheticalPosterior N b k hk =ᵐ[F.law N]
      (F.law N)[F.rewardIndicator|F.onlineObservationSigma N b k] := by
  rw [←F.hypotheticalSigma_eq_onlineObservationSigma N b k hk]
  exact F.hypotheticalPosterior_eq_condExp N b k hk

end ProphetSecretary.Statistics.FinitePrior
