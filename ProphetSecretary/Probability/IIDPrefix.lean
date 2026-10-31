import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw

/-!
# Actual finite prefixes of independent identical auxiliary samples

The infinite auxiliary sequence is fixed independently of the number of online
arrivals. Every requested finite prefix has its finite product law.
-/

open MeasureTheory ProbabilityTheory

namespace ProphetSecretary.Probability

lemma iidPrefix_measurePreserving {T : Type*} [MeasurableSpace T]
    (κ : Measure T) [IsProbabilityMeasure κ] (N : ℕ) :
    MeasurePreserving (fun z : ℕ → T => fun i : Fin N => z i.val)
      (Measure.infinitePi (fun _ : ℕ => κ)) (Measure.pi (fun _ : Fin N => κ)) := by
  refine ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply i.val),?_⟩
  have hIndependent : iIndepFun (fun j (z : ℕ → T) => z j) (Measure.infinitePi (fun _ : ℕ => κ)) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hPrefix := hIndependent.precomp (g := fun i : Fin N => i.val) Fin.val_injective
  have hLaw := hPrefix.hasLaw_pi (fun i : Fin N => (measurePreserving_eval_infinitePi (fun _ : ℕ => κ) i.val).hasLaw)
  exact hLaw.map_eq

end ProphetSecretary.Probability
