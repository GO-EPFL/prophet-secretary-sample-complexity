import ProphetSecretary.Limiting.CountableAcceptedPointMeasure
import ProphetSecretary.Limiting.AcceptedPointSums
import ProphetSecretary.Model.Outcome

/-!
# Finite execution as an attained countable first acceptance

Padding the finite accepted set by absent candidates changes no execution.
This identifies the existing finite policy semantics with the countable
first-point construction used for observable-measure payoff transfer.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Limiting.FiniteFirstAcceptance
open FirstAcceptance

variable {n : ℕ} {Seed : Type*}

noncomputable def acceptedCode (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n))
    (x u : Fin n → ℝ) (_ : Unit) (i : ℕ) : Prop :=
  ∃ hi : i < n, (⟨i,hi⟩ : Fin n) ∈ π.accepted r D x u

noncomputable def timeCode (u : Fin n → ℝ) (_ : Unit) (i : ℕ) : ℝ :=
  if hi : i < n then u ⟨i,hi⟩ else 1

noncomputable def valueCode (x : Fin n → ℝ) (_ : Unit) (i : ℕ) : ℝ :=
  if hi : i < n then x ⟨i,hi⟩ else 0

lemma hasFirst (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    HasFirstIfAccepted (acceptedCode π r D x u) (timeCode u) () := by
  apply hasFirstIfAccepted_of_finite
  apply (Set.finite_Iio n).subset
  rintro i ⟨hi,_⟩
  exact hi

lemma timeCode_upper (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : ∀ i, u i ≤ 1) (i : ℕ) (hi : acceptedCode π r D x u () i) : timeCode u () i ≤ 1 := by
  obtain ⟨hi,_⟩ := hi
  rw [timeCode,dif_pos hi]
  exact hu _

lemma stoppingTime_eq (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : ∀ i, u i ≤ 1) :
    FirstAcceptance.stoppingTime (acceptedCode π r D x u) (timeCode u) () = π.stoppingTime r D x u := by
  let A := acceptedCode π r D x u
  have hfirst := hasFirst π r D x u
  have hupper := timeCode_upper π r D x u hu
  apply le_antisymm
  · apply (π.le_stoppingTime_iff r D x u _).mpr
    have h := (FirstAcceptance.le_stoppingTime_iff hfirst hupper _).mp le_rfl
    refine ⟨h.1,?_⟩
    intro i hi
    have he := h.2 i.val ⟨i.isLt,hi⟩
    simpa only [timeCode,dif_pos i.isLt] using he
  · apply (FirstAcceptance.le_stoppingTime_iff hfirst hupper _).mpr
    have h := (π.le_stoppingTime_iff r D x u _).mp le_rfl
    refine ⟨h.1,?_⟩
    rintro i ⟨hi,hA⟩
    rw [timeCode,dif_pos hi]
    exact h.2 _ hA

lemma earliest_of_actualSelects (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n))
    (x u : Fin n → ℝ) {i : Fin n} (hi : π.ActualSelects r D x u i) :
    Earliest (acceptedCode π r D x u) (timeCode u) () i.val := by
  refine ⟨⟨i.isLt,hi.1.1⟩,?_⟩
  rintro j ⟨hj,hA⟩
  simp only [timeCode,dif_pos i.isLt,dif_pos hj]
  refine ⟨hi.1.2.trans_le (π.stoppingTime_le_of_accepted r D x u _ hA),?_⟩
  intro ht
  have hs : π.Selects r D x u ⟨j,hj⟩ := ⟨hA,ht.symm.trans hi.1.2⟩
  exact hi.2 _ hs

lemma no_earliest_of_no_actualSelects (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n))
    (x u : Fin n → ℝ) (hu : ∀ i, u i ≤ 1) (hno : ¬∃ i, π.ActualSelects r D x u i) :
    ¬∃ i, Earliest (acceptedCode π r D x u) (timeCode u) () i := by
  rintro ⟨i,hi⟩
  obtain ⟨hin,hA⟩ := hi.1
  have ht := FirstAcceptance.stoppingTime_of_earliest hi
  rw [stoppingTime_eq π r D x u hu,timeCode,dif_pos hin] at ht
  have hs : π.Selects r D x u ⟨i,hin⟩ := ⟨hA,ht.symm⟩
  exact hno (π.exists_actualSelects r D x u ⟨_,hs⟩)

lemma reward_eq (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : ∀ i, u i ≤ 1) (a : ℝ) :
    FirstAcceptance.reward a (acceptedCode π r D x u) (timeCode u) (valueCode x) () =
      if ∃ i, π.ActualSelects r D x u i then π.reward r D x u else a := by
  by_cases hs : ∃ i, π.ActualSelects r D x u i
  · obtain ⟨i,hi⟩ := hs
    rw [if_pos ⟨i,hi⟩,FirstAcceptance.reward_of_earliest a (earliest_of_actualSelects π r D x u hi),
      valueCode,dif_pos i.isLt,π.reward_eq_of_actualSelects r D x u hi]
  · have he := no_earliest_of_no_actualSelects π r D x u hu hs
    rw [if_neg hs,FirstAcceptance.reward,(selectedCode_eq_zero_iff _ _ _).mpr he,if_pos rfl]

lemma timeCode_bounds (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : ∀ i, u i ∈ Icc (0 : ℝ) 1) (i : ℕ) (hi : acceptedCode π r D x u () i) :
    timeCode u () i ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hi,_⟩ := hi
  rw [timeCode,dif_pos hi]
  exact hu _

lemma valueCode_nonnegative (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (i : ℕ) (hi : acceptedCode π r D x u () i) : 0 ≤ valueCode x () i := by
  obtain ⟨hi,_⟩ := hi
  rw [valueCode,dif_pos hi]
  exact hx _

lemma timeCode_injOn (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : Function.Injective u) : Set.InjOn (timeCode u ()) {i | acceptedCode π r D x u () i} := by
  intro i hi j hj ht
  obtain ⟨hi,_⟩ := hi
  obtain ⟨hj,_⟩ := hj
  simp only [timeCode,dif_pos hi,dif_pos hj] at ht
  exact congrArg Fin.val (hu ht)

lemma pointMeasure_eq_sum (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    FirstAcceptance.pointMeasure (acceptedCode π r D x u) (timeCode u) (valueCode x) () =
      ∑ i : Fin n, if i ∈ π.accepted r D x u then Measure.dirac (u i,x i) else 0 := by
  unfold FirstAcceptance.pointMeasure
  calc
    _ = Measure.sum (fun i : ℕ => if hi : i < n then
        (if (⟨i,hi⟩ : Fin n) ∈ π.accepted r D x u then Measure.dirac (u ⟨i,hi⟩,x ⟨i,hi⟩) else 0) else 0) := by
      apply congrArg Measure.sum
      funext i
      by_cases hi : i < n
      · have hiff : acceptedCode π r D x u () i ↔ (⟨i,hi⟩ : Fin n) ∈ π.accepted r D x u := by
          constructor
          · rintro ⟨_,hA⟩
            exact hA
          · intro hA
            exact ⟨hi,hA⟩
        simp only [dif_pos hi,timeCode,valueCode,hiff]
      · have hn : ¬acceptedCode π r D x u () i := by rintro ⟨h,_⟩; exact hi h
        simp only [if_neg hn,dif_neg hi]
    _ = _ := measureSum_natPrefix n (fun i : Fin n =>
      if i ∈ π.accepted r D x u then Measure.dirac (u i,x i) else 0)

lemma pointMeasure_time_eq (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : ∀ i, u i ∈ Icc (0 : ℝ) 1) :
    FirstPoint.time (FirstAcceptance.pointMeasure (acceptedCode π r D x u) (timeCode u) (valueCode x) ()) =
      π.stoppingTime r D x u :=
  (FirstAcceptance.pointMeasure_time_eq (hasFirst π r D x u) (timeCode_bounds π r D x u hu)).trans
    (stoppingTime_eq π r D x u (fun i => (hu i).2))

lemma pointMeasure_reward_eq (π : Model.Policy Seed n) (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (μ : FiniteMeasure Point)
    (hmeasure : (μ : Measure Point) = FirstAcceptance.pointMeasure
      (acceptedCode π r D x u) (timeCode u) (valueCode x) ())
    (hu : ∀ i, u i ∈ Icc (0 : ℝ) 1) (hx : ∀ i, 0 ≤ x i) (hinj : Function.Injective u) (a : ℝ) :
    FirstPoint.reward a μ = if ∃ i, π.ActualSelects r D x u i then π.reward r D x u else a :=
  (FirstAcceptance.pointMeasure_reward_eq a μ hmeasure (hasFirst π r D x u)
    (timeCode_bounds π r D x u hu) (valueCode_nonnegative π r D x u hx) (timeCode_injOn π r D x u hinj)).trans
      (reward_eq π r D x u (fun i => (hu i).2) a)

end ProphetSecretary.Limiting.FiniteFirstAcceptance
