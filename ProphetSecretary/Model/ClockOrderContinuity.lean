import ProphetSecretary.Model.Outcome
import ProphetSecretary.Reach.Pathwise
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Local constancy of arrival order and unseen identities

Distinct finite clocks have locally constant order. The actual unseen state
in the execution is therefore locally constant even though the times and
values stored in the full observation history vary. Terminal comparisons are
locally constant away from clock 1.
-/
open Set Filter
open scoped Topology Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma eventually_le_iff_of_continuousAt_ne {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hne : f x ≠ g x) : ∀ᶠ y in 𝓝 x, (f y ≤ g y ↔ f x ≤ g x) := by
  by_cases hle : f x ≤ g x
  · have hlt : f x < g x := lt_of_le_of_ne hle hne
    filter_upwards [hf.eventually_lt hg hlt] with y hy
    exact iff_of_true hy.le hle
  · filter_upwards [hg.eventually_lt hf (lt_of_not_ge hle)] with y hy
    exact iff_of_false (not_le_of_gt hy) hle

lemma clock_order_eventually_fixed (u : Fin n → ℝ) (hu : Function.Injective u) :
    ∀ᶠ v in 𝓝 u, ∀ i j, (v i < v j ↔ u i < u j) := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hij : i = j
  · subst j
    exact Eventually.of_forall fun _ => by simp
  · have hne : u j ≠ u i := fun h => hij (hu h).symm
    filter_upwards [eventually_le_iff_of_continuousAt_ne (continuous_apply j).continuousAt
      (continuous_apply i).continuousAt hne] with v hv
    exact not_le.symm.trans (hv.not.trans not_le)

lemma clock_le_order_fixed {u v : Fin n → ℝ}
    (horder : ∀ i j, (v i < v j ↔ u i < u j)) (i j : Fin n) :
    v i ≤ v j ↔ u i ≤ u j := by
  simpa only [not_lt] using (horder j i).not

lemma clocks_terminal_comparison_eventually_fixed (u : Fin n → ℝ) (hu : ∀ i, u i ≠ 1) :
    ∀ᶠ v in 𝓝 u, ∀ i, (v i ≤ 1 ↔ u i ≤ 1) := by
  apply eventually_all.mpr
  intro i
  exact eventually_le_iff_of_continuousAt_ne (continuous_apply i).continuousAt continuousAt_const (hu i)

lemma unseen_history_at_arrival_eq_of_clock_order (D : Finset (Fin n))
    (x y u v : Fin n → ℝ) (horder : ∀ i j, (v i < v j ↔ u i < u j)) (i : Fin n) :
    unseen (history D y v (v i)) = unseen (history D x u (u i)) := by
  ext j
  simp only [unseen,Finset.mem_filter,Finset.mem_univ,true_and,history,horder j i]
  by_cases hj : j ∈ D ∧ u j < u i <;> simp [hj]

lemma unseen_at_arrival_eventually_fixed (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : Function.Injective u) :
    ∀ᶠ z : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (x,u), ∀ i,
      unseen (history D z.1 z.2 (z.2 i)) = unseen (history D x u (u i)) := by
  filter_upwards [continuous_snd.continuousAt.eventually (clock_order_eventually_fixed u hu)] with z hz
  exact fun i => unseen_history_at_arrival_eq_of_clock_order D x z.1 u z.2 hz i

end ProphetSecretary.Model
