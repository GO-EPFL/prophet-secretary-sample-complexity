import ProphetSecretary.Limiting.HybridPolicy
import ProphetSecretary.Model.TrainingZeroSimulation

/-!
# Finite-array evaluation of a hybrid rule

Conditioning the analytical Poisson count yields independent marks and uniform
clocks. This transport evaluates the same hybrid rule at every count; it does
not supply the count or generation labels to that rule.
-/

open MeasureTheory Set

namespace ProphetSecretary.Limiting

variable {n N : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- Append a specified iid marginal; the nonnegativity premise concerns input data. -/
noncomputable def appendIID (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (N : ℕ) : Model.Instance (n + N) where
  law := Fin.addCases P.law (fun _ => κ)
  probability := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa using P.probability i
    | right j => simpa using (inferInstance : IsProbabilityMeasure κ)
  nonnegative := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa using P.nonnegative i
    | right j => simpa using hκ

/-- Convert the analytical retained world into independent time-mark pairs. -/
lemma retainedPairs_measurePreserving (P : Model.Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun w : Model.World n Seed => ((fun i => (w.2.1 i, w.1 i)), w.2.2))
      (P.worldLaw ν)
      ((Measure.pi (fun i => Model.Instance.uniformClock.prod (P.law i))).prod ν) := by
  have h₁ := (measurePreserving_prodAssoc P.valuesLaw (Model.Instance.clocksLaw n) ν).symm MeasurableEquiv.prodAssoc
  have h₂ := (Measure.measurePreserving_swap (μ := P.valuesLaw) (ν := Model.Instance.clocksLaw n)).prod
    (MeasurePreserving.id ν)
  have h₃ := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => Model.Instance.uniformClock) P.law).symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
  exact (h₃.prod (MeasurePreserving.id ν)).comp (h₂.comp h₁)

/-- The finite-array branch has exactly the finite independent-instance law. -/
lemma finiteArrayWorld_measurePreserving (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) :
    MeasurePreserving (fun v : (Fin N → Point) × Model.World n Seed =>
      (combinedValues v.2.1 v.1, (combinedClocks v.2.2.1 v.1, v.2.2.2)))
      ((Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod (P.worldLaw ν))
      ((appendIID P κ hκ N).worldLaw ν) := by
  let ρ : Fin n → Measure Point := fun i => Model.Instance.uniformClock.prod (P.law i)
  let σ : Fin N → Measure Point := fun _ => Model.Instance.uniformClock.prod κ
  have h₁ := (MeasurePreserving.id (Measure.pi σ)).prod (retainedPairs_measurePreserving P ν)
  have h₂ := (measurePreserving_prodAssoc (Measure.pi σ) (Measure.pi ρ) ν).symm MeasurableEquiv.prodAssoc
  have h₃ := (Measure.measurePreserving_swap (μ := Measure.pi σ) (ν := Measure.pi ρ)).prod
    (MeasurePreserving.id ν)
  have h₄ := (Model.measurePreserving_finAddCases_general ρ σ).prod (MeasurePreserving.id ν)
  let laws : Fin (n + N) → Measure ℝ := Fin.addCases P.law (fun _ => κ)
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
