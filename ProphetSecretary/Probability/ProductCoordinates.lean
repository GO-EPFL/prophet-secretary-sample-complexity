import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Actual finite product-coordinate projection

An injective coordinate projection preserves the corresponding product law.
The proof uses the installed independence-of-product-coordinates and joint-law
identification statements. It supplies the training-prefix/ONLINE split of the
finite-prior experiment, without assuming that split as an interface.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical
namespace ProphetSecretary.Probability

lemma productCoordinateProjection_measurePreserving {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (e : κ ↪ ι) :
    MeasurePreserving (fun x : ι → ℝ => x ∘ e) (Measure.pi μ) (Measure.pi (fun q => μ (e q))) := by
  have hi := iIndepFun.precomp e.injective
    (iIndepFun_pi (μ:=μ) (X:=fun _ => id) (fun _ => aemeasurable_id))
  have hm := iIndepFun.map_fun_eq_pi_map (fun q => (measurable_pi_apply (e q)).aemeasurable) hi
  have he : (fun q => (Measure.pi μ).map (fun x : ι → ℝ => x (e q)))=fun q => μ (e q) := by
    funext q
    exact (measurePreserving_eval μ (e q)).map_eq
  change (Measure.pi μ).map (fun x => x ∘ e)=Measure.pi (fun q => (Measure.pi μ).map (fun x : ι → ℝ => x (e q))) at hm
  rw [he] at hm
  exact ⟨measurable_pi_lambda _ (fun q => measurable_pi_apply (e q)),hm⟩

end ProphetSecretary.Probability
