import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousOn

/-!
# Joint continuity with a discrete parameter
-/

open Filter Set
open scoped Topology

namespace ProphetSecretary.Analysis

lemma continuous_discrete_parameter {D X Y : Type*} [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace X] [TopologicalSpace Y] (f : D → X → Y)
    (hf : ∀ d, Continuous (f d)) : Continuous (fun z : D × X => f z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hConst : ContinuousAt (fun q : D × X => f z.1 q.2) z := (hf z.1).continuousAt.comp continuous_snd.continuousAt
  apply hConst.congr_of_eventuallyEq
  have hD : ∀ᶠ q : D × X in 𝓝 z, q.1 = z.1 := by
    have hOpen : IsOpen ((Prod.fst : D × X → D) ⁻¹' {z.1}) :=
      (isOpen_discrete {z.1}).preimage continuous_fst
    have hMem := hOpen.eventually_mem (show z ∈ (Prod.fst : D × X → D) ⁻¹' {z.1} from rfl)
    simpa only [mem_preimage,mem_singleton_iff] using hMem
  filter_upwards [hD] with q hq
  rw [hq]

end ProphetSecretary.Analysis
