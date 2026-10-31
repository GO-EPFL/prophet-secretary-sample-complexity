import ProphetSecretary.Statistics.FinitePriorExperiment
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# An actual hypothetical-round swap in the finite-prior experiment

A column transposition exchanges one still-hidden training round with the ONLINE
vector. It preserves each conditional independent product law and hence the
actual finite-prior mixture, while fixing nature's hidden target. Swapping the
next unused round leaves every current training observation unchanged.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

def columnSwap (n N : ℕ) (j : Fin (N+1)) : Equiv.Perm (Fin n × Fin (N+1)) :=
  Equiv.prodCongr (Equiv.refl (Fin n)) (Equiv.swap j (Fin.last N))

lemma columnSwap_involutive (n N : ℕ) (j : Fin (N+1)) (q : Fin n × Fin (N+1)) :
    columnSwap n N j (columnSwap n N j q)=q := by
  rcases q with ⟨i,r⟩
  change (i,Equiv.swap j (Fin.last N) (Equiv.swap j (Fin.last N) r))=(i,r)
  rw [Equiv.swap_apply_self]

def swapValueEquiv (n N : ℕ) (j : Fin (N+1)) : ValueArray n N ≃ᵐ ValueArray n N :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin (N+1) => ℝ) (columnSwap n N j)

lemma swapValueEquiv_apply (n N : ℕ) (j : Fin (N+1)) (a : ValueArray n N) (i : Fin n) (r : Fin (N+1)) :
    swapValueEquiv n N j a (i,r)=a (i,Equiv.swap j (Fin.last N) r) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ : Fin n × Fin (N+1) => ℝ)
    (columnSwap n N j) a (columnSwap n N j (i,r))
  rw [columnSwap_involutive] at h
  exact h

lemma swapValueEquiv_involutive (n N : ℕ) (j : Fin (N+1)) (a : ValueArray n N) :
    swapValueEquiv n N j (swapValueEquiv n N j a)=a := by
  funext q
  rcases q with ⟨i,r⟩
  simp only [swapValueEquiv_apply,Equiv.swap_apply_self]

lemma swapValueEquiv_measurePreserving (P : Instance n) (N : ℕ) (j : Fin (N+1)) :
    MeasurePreserving (swapValueEquiv n N j) (P.trainingCoordinateLaw (N+1)) (P.trainingCoordinateLaw (N+1)) :=
  measurePreserving_piCongrLeft (fun q : Fin n × Fin (N+1) => P.law q.1) (columnSwap n N j)

def swapBaseEquiv (F : FinitePrior n) (N : ℕ) (j : Fin (N+1)) : BaseWorld F N ≃ᵐ BaseWorld F N :=
  (MeasurableEquiv.refl (Fin F.size)).prodCongr (swapValueEquiv n N j)

lemma swapBaseEquiv_apply (F : FinitePrior n) (N : ℕ) (j : Fin (N+1)) (ω : BaseWorld F N) :
    F.swapBaseEquiv N j ω=(ω.1,swapValueEquiv n N j ω.2) := rfl

lemma swapBaseEquiv_involutive (F : FinitePrior n) (N : ℕ) (j : Fin (N+1)) (ω : BaseWorld F N) :
    F.swapBaseEquiv N j (F.swapBaseEquiv N j ω)=ω := by
  rw [swapBaseEquiv_apply,swapBaseEquiv_apply,swapValueEquiv_involutive]

lemma swapBaseEquiv_atom_measurePreserving (F : FinitePrior n) (N : ℕ) (j : Fin (N+1)) (θ : Fin F.size) :
    MeasurePreserving (F.swapBaseEquiv N j) (F.atomLaw N θ) (F.atomLaw N θ) :=
  (MeasurePreserving.id (Measure.dirac θ)).prod (swapValueEquiv_measurePreserving (F.offerInstance θ) N j)

lemma swapBaseEquiv_measurePreserving (F : FinitePrior n) (N : ℕ) (j : Fin (N+1)) :
    MeasurePreserving (F.swapBaseEquiv N j) (F.law N) (F.law N) := by
  refine ⟨(F.swapBaseEquiv N j).measurable,?_⟩
  simp only [law,Measure.map_finset_sum' (F.swapBaseEquiv N j).measurable.aemeasurable,Measure.map_smul]
  exact Finset.sum_congr rfl fun θ _ => congrArg (fun μ => F.weight θ • μ)
    (F.swapBaseEquiv_atom_measurePreserving N j θ).map_eq

lemma rewardIndicator_swap (F : FinitePrior n) (N : ℕ) (j : Fin (N+1)) (ω : BaseWorld F N) :
    F.rewardIndicator (F.swapBaseEquiv N j ω)=F.rewardIndicator ω := rfl

/-- k is public; column b+k is unused, and N remains the ONLINE column. -/
def nextColumn (N b k : ℕ) (hk : b+k<N) : Fin (N+1) := ⟨b+k,by omega⟩

lemma observe_swap_next (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) (ω : BaseWorld F N) :
    F.observe N b k (F.swapBaseEquiv N (nextColumn N b k hk) ω)=F.observe N b k ω := by
  funext q
  rcases q with ⟨i,r⟩
  by_cases hr : (i,r)∈trainingCoordinates n N b k
  · have hv : r.val<min (b+k) N := (Finset.mem_filter.mp hr).2
    have hnj : r≠nextColumn N b k hk := by intro he; have := congrArg Fin.val he; dsimp [nextColumn] at this; omega
    have hnN : r≠Fin.last N := by intro he; have := congrArg Fin.val he; simp only [Fin.val_last] at this; omega
    simp only [observe,ProphetSecretary.Probability.maskCoordinates,if_pos hr,swapBaseEquiv_apply,
      swapValueEquiv_apply,Equiv.swap_apply_of_ne_of_ne hnj hnN]
  · simp only [observe,ProphetSecretary.Probability.maskCoordinates,if_neg hr]

lemma posterior_swap_next (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) (ω : BaseWorld F N) :
    F.posterior N b k (F.swapBaseEquiv N (nextColumn N b k hk) ω)=F.posterior N b k ω :=
  F.posterior_eq_of_observe_eq N b k _ _ (F.observe_swap_next N b k hk ω)

/-- This posterior is analytical: the online values are not queried as training. -/
noncomputable def hypotheticalPosterior (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) : BaseWorld F N → ℝ :=
  fun ω => F.posterior N b (k+1) (F.swapBaseEquiv N (nextColumn N b k hk) ω)

lemma hypothetical_increment_energy (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) :
    (∫ ω, (F.hypotheticalPosterior N b k hk ω-F.posterior N b k ω)^2 ∂F.law N) =
      ∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N := by
  have h := (F.swapBaseEquiv_measurePreserving N (nextColumn N b k hk)).integral_comp'
    (fun ω => (F.posterior N b (k+1) ω-F.posterior N b k ω)^2)
  simpa only [hypotheticalPosterior,posterior_swap_next] using h

end ProphetSecretary.Statistics.FinitePrior
