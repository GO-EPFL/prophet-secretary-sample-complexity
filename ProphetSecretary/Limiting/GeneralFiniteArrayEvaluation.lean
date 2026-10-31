import ProphetSecretary.Limiting.FiniteArrayEvaluation
import ProphetSecretary.Limiting.IndependentAppend

/-!
# Finite-array evaluation with nonidentical anonymous offer laws

The virtual identities may have arbitrary independent marginal laws. Their
analytical time/mark pairs and retained world map to the ordinary concatenated
instance, without supplying a realized count or generation label to the
shared hybrid callback.
-/
open MeasureTheory Set
namespace ProphetSecretary.Limiting
variable {n N : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma generalFiniteArrayWorld_measurePreserving (P : Model.Instance n) (Q : Model.Instance N)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun v : (Fin N → Point) × Model.World n Seed =>
      (combinedValues v.2.1 v.1, (combinedClocks v.2.2.1 v.1, v.2.2.2)))
      ((Measure.pi (fun j : Fin N => Model.Instance.uniformClock.prod (Q.law j))).prod (P.worldLaw ν))
      ((P.appendIndependent Q).worldLaw ν) := by
  let ρ : Fin n → Measure Point := fun i => Model.Instance.uniformClock.prod (P.law i)
  let σ : Fin N → Measure Point := fun j => Model.Instance.uniformClock.prod (Q.law j)
  have h₁ := (MeasurePreserving.id (Measure.pi σ)).prod (retainedPairs_measurePreserving P ν)
  have h₂ := (measurePreserving_prodAssoc (Measure.pi σ) (Measure.pi ρ) ν).symm MeasurableEquiv.prodAssoc
  have h₃ := (Measure.measurePreserving_swap (μ := Measure.pi σ) (ν := Measure.pi ρ)).prod
    (MeasurePreserving.id ν)
  have h₄ := (Model.measurePreserving_finAddCases_general ρ σ).prod (MeasurePreserving.id ν)
  let laws : Fin (n + N) → Measure ℝ := Fin.addCases P.law Q.law
  have hlaws : (Fin.addCases ρ σ : Fin (n + N) → Measure Point) =
      fun i => Model.Instance.uniformClock.prod (laws i) := by
    funext i
    induction i using Fin.addCases <;> simp [ρ, σ, laws]
  rw [hlaws] at h₄
  haveI : ∀ i, IsProbabilityMeasure (laws i) := by
    intro i
    induction i using Fin.addCases <;> simp only [laws, Fin.addCases_left, Fin.addCases_right] <;> infer_instance
  have h₅ := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n + N))
    (fun _ => Model.Instance.uniformClock) laws).prod (MeasurePreserving.id ν)
  have h₆ := (Measure.measurePreserving_swap
    (μ := Model.Instance.clocksLaw (n + N)) (ν := Measure.pi laws)).prod (MeasurePreserving.id ν)
  have h₇ := measurePreserving_prodAssoc (Measure.pi laws) (Model.Instance.clocksLaw (n + N)) ν
  have h := h₇.comp (h₆.comp (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))))
  convert h using 1
  · funext v
    apply Prod.ext
    · funext i
      induction i using Fin.addCases <;>
        simp [combinedValues, Function.comp_def, MeasurableEquiv.prodAssoc, Equiv.prodAssoc, Prod.map,
          MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    · apply Prod.ext
      · funext i
        induction i using Fin.addCases <;>
          simp [combinedClocks, Function.comp_def, MeasurableEquiv.prodAssoc, Equiv.prodAssoc, Prod.map,
            MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
      · rfl
  · rfl

end ProphetSecretary.Limiting
