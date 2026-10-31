import ProphetSecretary.Limiting.PoissonBranchWeak
import ProphetSecretary.Model.WeakValueContinuity

/-!
# Weak convergence of retained offer and clock data

The actual independent retained world includes every offer identity, its
value and uniform clock. The singleton auxiliary seed is used for a fixed
deterministic canonical callback.
-/
open MeasureTheory Set Filter
open scoped Topology Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def retainedWorldProbabilityLaw (P : Model.Instance n) : ProbabilityMeasure (Model.World n Unit) :=
  ⟨P.worldLaw (Measure.dirac ()),inferInstance⟩

lemma retainedWorldProbabilityLaw_tendsto (Ps : ℕ → Model.Instance n) (P : Model.Instance n)
    (hP : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (P.marginalProbabilityLaw i))) :
    Tendsto (fun m => retainedWorldProbabilityLaw (Ps m)) atTop (𝓝 (retainedWorldProbabilityLaw P)) := by
  let χ : ProbabilityMeasure ℝ := ⟨Model.Instance.uniformClock,inferInstance⟩
  let ν : ProbabilityMeasure Unit := ⟨Measure.dirac (),inferInstance⟩
  let η : ProbabilityMeasure ((Fin n → ℝ) × Unit) := (ProbabilityMeasure.pi (fun _ : Fin n => χ)).prod ν
  have hValues := ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hP)
  exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    (hValues.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => η) atTop (𝓝 η)))
end ProphetSecretary.Limiting
