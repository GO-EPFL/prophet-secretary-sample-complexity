import ProphetSecretary.Model.Independence
import Mathlib.Data.Fintype.Sort

/-!
# Arrival orders

Independent uniform clocks have no ties. Reindexing their identities preserves their
joint law, and therefore every strict arrival order has the same probability.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ProphetSecretary.Model
namespace Instance

variable {n : ℕ}

/-- The permutation lists identities in strictly increasing arrival time. -/
def HasArrivalOrder (u : Fin n → ℝ) (p : Equiv.Perm (Fin n)) : Prop :=
  StrictMono (fun k => u (p k))

lemma measurableSet_hasArrivalOrder (p : Equiv.Perm (Fin n)) :
    MeasurableSet {u : Fin n → ℝ | HasArrivalOrder u p} := by
  change MeasurableSet {u : Fin n → ℝ | ∀ i j, i < j → u (p i) < u (p j)}
  simp only [setOf_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply (p i)) (measurable_pi_apply (p j))

private structure ArrivalIdentity (n : ℕ) where
  index : Fin n

private def arrivalIdentityEquiv : ArrivalIdentity n ≃ Fin n :=
  ⟨ArrivalIdentity.index, ArrivalIdentity.mk, by intro a; cases a; rfl, by intro a; rfl⟩

private instance : Fintype (ArrivalIdentity n) := Fintype.ofEquiv (Fin n) arrivalIdentityEquiv.symm

lemma exists_arrivalOrder {u : Fin n → ℝ} (hu : Function.Injective u) :
    ∃ p : Equiv.Perm (Fin n), HasArrivalOrder u p := by
  letI : LinearOrder (ArrivalIdentity n) := LinearOrder.lift' (fun j => u j.index)
    (fun a b hab => by cases a; cases b; congr; exact hu hab)
  let e : Fin n ≃o ArrivalIdentity n := monoEquivOfFin (ArrivalIdentity n)
    ((Fintype.card_congr arrivalIdentityEquiv).trans (Fintype.card_fin n))
  let p : Equiv.Perm (Fin n) := e.toEquiv.trans arrivalIdentityEquiv
  refine ⟨p, ?_⟩
  exact e.strictMono

lemma arrivalOrder_unique {u : Fin n → ℝ} {p q : Equiv.Perm (Fin n)}
    (hp : HasArrivalOrder u p) (hq : HasArrivalOrder u q) : p = q := by
  have hrange : Set.range (fun k => u (p k)) = Set.range (fun k => u (q k)) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨q.symm (p k), by simp⟩
    · rintro ⟨k, rfl⟩
      exact ⟨p.symm (q k), by simp⟩
  have heq := hp.range_inj hq |>.mp hrange
  have hu : Function.Injective u := by
    intro a b hab
    have hab' : u (p (p.symm a)) = u (p (p.symm b)) := by simpa using hab
    exact p.symm.injective (hp.injective hab')
  apply Equiv.ext
  intro k
  exact hu (congrFun heq k)

/-- Exchangeability here is a consequence of identical product clock marginals. -/
lemma clock_reindex_measurePreserving (p : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun u : Fin n → ℝ => fun k => u (p k)) (clocksLaw n) (clocksLaw n) := by
  have h := measurePreserving_piCongrLeft (α := fun _ : Fin n => ℝ)
    (fun _ : Fin n => uniformClock) p
  exact h.symm (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) p)

lemma arrivalOrder_probability_eq (p : Equiv.Perm (Fin n)) :
    clocksLaw n {u | HasArrivalOrder u p} =
      clocksLaw n {u | HasArrivalOrder u (Equiv.refl (Fin n))} := by
  have h := (clock_reindex_measurePreserving p).measure_preimage
    (measurableSet_hasArrivalOrder (Equiv.refl (Fin n))).nullMeasurableSet
  exact h

/-- The order of independent uniform clocks is uniform over all permutations. -/
lemma arrivalOrder_probability (p : Equiv.Perm (Fin n)) :
    clocksLaw n {u | HasArrivalOrder u p} = (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ := by
  have hd : Pairwise (fun p q : Equiv.Perm (Fin n) =>
      Disjoint {u | HasArrivalOrder u p} {u | HasArrivalOrder u q}) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro u hp hq
    exact hpq (arrivalOrder_unique hp hq)
  have hm : clocksLaw n (⋃ p : Equiv.Perm (Fin n), {u | HasArrivalOrder u p}) = 1 := by
    apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion measurableSet_hasArrivalOrder)).mp
    filter_upwards [clocks_pairwise_distinct (n := n)] with u hu
    obtain ⟨p, hp⟩ := exists_arrivalOrder hu
    exact Set.mem_iUnion.mpr ⟨p, hp⟩
  rw [measure_iUnion hd measurableSet_hasArrivalOrder, tsum_fintype] at hm
  simp_rw [arrivalOrder_probability_eq] at hm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm
  rw [arrivalOrder_probability_eq]
  have hm' : clocksLaw n {u | HasArrivalOrder u (Equiv.refl (Fin n))} *
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) = 1 := by simpa only [mul_comm] using hm
  exact ENNReal.eq_inv_of_mul_eq_one_left hm'

end Instance
end ProphetSecretary.Model
