import Mathlib.Data.Nat.Find
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# A slowly increasing diagonal for countably many iterated limits

The retained prefix grows only after the finite set of current convergence
tests has stabilized. The schedule is monotone, never exceeds the outer
sequence index, and tends to infinity. This turns two separately proved limit
orders into an actual diagonal; it does not assert that such a diagonal is
valid without those convergence hypotheses.
-/
open Filter
open scoped Topology Classical
namespace ProphetSecretary.Analysis

noncomputable def slowIndex (T : ℕ → ℕ) (m : ℕ) : ℕ := Nat.findGreatest (fun k => T k ≤ m) m

lemma slowIndex_le (T : ℕ → ℕ) (m : ℕ) : slowIndex T m ≤ m := Nat.findGreatest_le m

lemma slowIndex_monotone (T : ℕ → ℕ) : Monotone (slowIndex T) := by
  intro m n hmn
  exact Nat.findGreatest_mono (fun _ hk => hk.trans hmn) hmn

lemma slowIndex_schedule_eventually (T : ℕ → ℕ) : ∀ᶠ m in atTop, T (slowIndex T m) ≤ m := by
  filter_upwards [eventually_ge_atTop (T 0)] with m hm
  exact Nat.findGreatest_spec (P := fun k => T k ≤ m) (Nat.zero_le m) hm

lemma slowIndex_tendsto_atTop (T : ℕ → ℕ) : Tendsto (slowIndex T) atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [eventually_ge_atTop (max K (T K))] with m hm
  exact Nat.le_findGreatest ((le_max_left _ _).trans hm) ((le_max_right _ _).trans hm)

/-- Actual countable-test slow diagonal, with no exchange-of-limits premise.
A can be evaluated in any pseudo-metric target, in particular for numerical
continuity tests of positive-band measure data. -/
theorem exists_slow_diagonal_of_iterated_limits {X : Type*} [PseudoMetricSpace X]
    (A : ℕ → ℕ → ℕ → X) (B : ℕ → ℕ → X) (z : ℕ → X)
    (hfirst : ∀ N j, Tendsto (fun m => A N m j) atTop (𝓝 (B N j)))
    (hsecond : ∀ j, Tendsto (fun N => B N j) atTop (𝓝 (z j))) :
    ∃ Ns : ℕ → ℕ, Monotone Ns ∧ (∀ m, Ns m ≤ m) ∧ Tendsto Ns atTop atTop ∧
      ∀ j, Tendsto (fun m => A (Ns m) m j) atTop (𝓝 (z j)) := by
  have hthreshold (N : ℕ) : ∃ T : ℕ, ∀ m ≥ T, ∀ j ≤ N,
      dist (A N m j) (B N j) < 1 / (N+1 : ℕ) := by
    have heach (j : Fin (N+1)) : ∀ᶠ m in atTop, dist (A N m j.val) (B N j.val) < 1 / (N+1 : ℕ) :=
      Metric.tendsto_nhds.mp (hfirst N j.val) _ (by positivity)
    have hall : ∀ᶠ m in atTop, ∀ j : Fin (N+1), dist (A N m j.val) (B N j.val) < 1 / (N+1 : ℕ) :=
      eventually_all.mpr heach
    obtain ⟨T,hT⟩ := eventually_atTop.mp hall
    exact ⟨T,fun m hm j hj => hT m hm ⟨j,Nat.lt_succ_of_le hj⟩⟩
  choose T hT using hthreshold
  let Ns := slowIndex T
  have htop : Tendsto Ns atTop atTop := slowIndex_tendsto_atTop T
  refine ⟨Ns,slowIndex_monotone T,slowIndex_le T,htop,?_⟩
  intro j
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_gt (2 / ε)
  have hMscaled := (div_lt_iff₀ hε).mp hM
  have hB := Metric.tendsto_nhds.mp ((hsecond j).comp htop) (ε/2) (by positivity)
  have hLarge : ∀ᶠ m in atTop, max j M ≤ Ns m := htop (eventually_ge_atTop (max j M))
  filter_upwards [slowIndex_schedule_eventually T,hLarge,hB] with m hSched hNs hBm
  have hj : j ≤ Ns m := (le_max_left _ _).trans hNs
  have hMN : M ≤ Ns m := (le_max_right _ _).trans hNs
  have hA := hT (Ns m) m hSched j hj
  have hDen : 0 < ((Ns m+1 : ℕ) : ℝ) := by positivity
  have hsmall : 1 / (Ns m+1 : ℕ) ≤ ε/2 := by
    apply (div_le_iff₀ hDen).mpr
    have hcast : (M : ℝ) ≤ (Ns m : ℝ) := Nat.cast_le.mpr hMN
    have hm := mul_le_mul_of_nonneg_right hcast hε.le
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith only [hMscaled,hm,hε]
  change dist (B (Ns m) j) (z j) < ε/2 at hBm
  exact (dist_triangle (A (Ns m) m j) (B (Ns m) j) (z j)).trans_lt (by linarith only [hA,hsmall,hBm])

end ProphetSecretary.Analysis
