import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Stability of a scalar acceptance comparison away from ties
-/

open Filter
open scoped Topology

namespace ProphetSecretary.Analysis

lemma eventually_le_iff_of_tendsto_ne {f : ℕ → ℝ} {v a : ℝ}
    (hf : Tendsto f atTop (𝓝 v)) (hne : v ≠ a) :
    ∀ᶠ n in atTop, (f n ≤ a ↔ v ≤ a) := by
  by_cases hv : v ≤ a
  · have hlt : v < a := lt_of_le_of_ne hv hne
    filter_upwards [hf.eventually (gt_mem_nhds hlt)] with n hn
    exact ⟨fun _ => hv,fun _ => hn.le⟩
  · have hlt : a < v := not_le.mp hv
    filter_upwards [hf.eventually (lt_mem_nhds hlt)] with n hn
    exact ⟨fun h => False.elim ((not_le_of_gt hn) h),fun h => False.elim (hv h)⟩

end ProphetSecretary.Analysis
