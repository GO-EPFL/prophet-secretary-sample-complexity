import ProphetSecretary.Limiting.WeightedPaddedInstance
import ProphetSecretary.Model.TerminalBenchmarkReindex

/-!
# Actual benchmark correspondence for ordered zero-padded instances
-/

open MeasureTheory BoundedContinuousFunction

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma weightOrderedPrefix_full_terminal_benchmark (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {a : ℝ} (ha : 0 ≤ a) :
    (weightOrderedPrefix P wgt (N+n)).expectedTerminalMaximum a = P.expectedTerminalMaximum a := by
  let R := P.restrictBy (weightedMeanPermutation P wgt).toEmbedding
  have hR := P.restrictBy_integrable_maximum (weightedMeanPermutation P wgt).toEmbedding hP
  have hS := R.appendZeros_integrable_maximum N hR
  have he := (R.appendZeros N).expectedTerminalMaximum_eq_of_law_equiv
    (weightOrderedPrefix P wgt (N+n)) (finCongr (Nat.add_comm N n))
    (fun i => by
      have h := weightOrderedPrefix_full_law P wgt N ((finCongr (Nat.add_comm N n)) i)
      have hcast : (finCongr (Nat.add_comm n N)) ((finCongr (Nat.add_comm N n)) i) = i := by
        apply Fin.ext
        rfl
      rw [hcast] at h
      exact h.symm) hS ha
  have hRel := P.expectedTerminalMaximum_eq_of_law_equiv R (weightedMeanPermutation P wgt)
    (fun _ => rfl) hP ha
  exact he.trans ((R.expectedTerminalMaximum_appendZeros N hR ha).trans hRel)

end ProphetSecretary.Limiting
