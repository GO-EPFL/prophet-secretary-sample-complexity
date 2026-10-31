import ProphetSecretary.Limiting.HybridZeroProbability

/-!
# Inserting ignored individual identities before anonymous points

The embedding preserves the order of every existing retained and anonymous
identity. It is used only to compare finite adapters of the same shared hybrid
policy, never to reveal the realized anonymous count to a callback.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Limiting

lemma HybridZeroSimulation.keepEmbedding_ne_inserted (n k N : ℕ) (j : Fin k) (i : Fin (n + N)) :
    HybridZeroSimulation.keepEmbedding n k N i ≠ (j.natAdd n).castAdd N := by
  induction i using Fin.addCases with
  | left i =>
    rw [HybridZeroSimulation.keepEmbedding_left]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  | right l =>
    rw [HybridZeroSimulation.keepEmbedding_right]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega

end ProphetSecretary.Limiting
