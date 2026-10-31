import ProphetSecretary.Limiting.WeightedCoarsePolicy
import ProphetSecretary.Model.ScoreProjection
import ProphetSecretary.Model.ZeroSimulationScore
import ProphetSecretary.Model.ZeroValueReconstruction

/-!
# Complete analytical scores through the coarse comparison policy

Static ordering, deterministic zero padding and identity projection define
the score pullback. Actual product-law maps and pathwise execution transport
score-weighted reward and duration, separately from unweighted guarantees.
Product integrability in the retained/residual instance is explicit.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n K : ℕ}

noncomputable def weightedCoarseScore (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (hKN : K ≤ N) (s : (Fin (K+n) → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  s (Model.ZeroSimulation.appendValues (x ∘ weightedMeanPermutation P wgt) ∘ weightedCoarseEmbedding n K N hKN)

lemma weightedCoarsePolicy_score_reward (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (hKN : K ≤ N) (π : RandomizedHybridPolicy K) (d : ℝ)
    (s : (Fin (K+n) → ℝ) → ℝ) (hs : Measurable s)
    (hInt : Integrable (fun ω : (π.finiteCutoffEvaluation n d).World => s ω.1*(π.finiteCutoffEvaluation n d).realizedReward ω)
      (((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)).worldLaw π.seedLaw)) :
    let γ := weightedCoarsePolicy P wgt N hKN π d
    Integrable (fun ω : γ.World => weightedCoarseScore P wgt N hKN s ω.1*γ.realizedReward ω) (P.worldLaw γ.seedLaw) ∧
      (∫ ω : γ.World, weightedCoarseScore P wgt N hKN s ω.1*γ.realizedReward ω ∂P.worldLaw γ.seedLaw)=
        ∫ ω : (π.finiteCutoffEvaluation n d).World, s ω.1*(π.finiteCutoffEvaluation n d).realizedReward ω
          ∂((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)).worldLaw π.seedLaw := by
  let e := weightedCoarseEmbedding n K N hKN
  let A := P.restrictBy (weightedMeanPermutation P wgt).toEmbedding
  let Γ := π.finiteCutoffEvaluation n d
  let ΓA := Γ.ignoreExtras e
  let sA := fun x : Fin n → ℝ => s (Model.ZeroSimulation.appendValues x ∘ e)
  have hsA : Measurable sA := hs.comp
    ((measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))).comp (A.appendValues_measurePreserving N).measurable)
  have hLaw : (A.appendZeros N).restrictBy e=
      (weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N) :=
    weightedCoarse_restricted_instance P wgt K N hKN
  have hIn : Integrable (fun ω : Γ.World => s ω.1*Γ.realizedReward ω)
      (((A.appendZeros N).restrictBy e).worldLaw Γ.seedLaw) := by rw [hLaw]; exact hInt
  have hSparse := Γ.ignoreExtras_score_reward (A.appendZeros N) e s hs hIn
  have hReplace : (fun ω : ΓA.World => sA (fun i => ω.1 (i.castAdd N))*ΓA.realizedReward ω) =ᵐ[(A.appendZeros N).worldLaw ΓA.seedLaw]
      (fun ω => s (ω.1 ∘ e)*ΓA.realizedReward ω) := by
    filter_upwards [A.appendZeros_values_reconstruct_ae ΓA.seedLaw] with ω hω
    change s (Model.ZeroSimulation.appendValues (fun i => ω.1 (i.castAdd N)) ∘ e)*ΓA.realizedReward ω=_
    rw [hω]
  have hProjInt := hSparse.1.congr hReplace.symm
  have hZero := ΓA.simulateZeros_score_reward A sA hsA hProjInt
  have hRel := ΓA.simulateZeros.ignoreExtras_score_reward P (weightedMeanPermutation P wgt).toEmbedding sA hsA hZero.1
  have hEq := hRel.2.trans (hZero.2.trans ((integral_congr_ae hReplace).trans hSparse.2))
  rw [hLaw] at hEq
  exact ⟨hRel.1,hEq⟩

lemma weightedCanonicalCoarsePolicy_score_duration (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (hKN : K ≤ N) (B : FiniteIntensityHybridInstance K) {w c : ℝ} (hw : 0<w) (hc : 0<c) (d : ℝ)
    (s : (Fin (K+n) → ℝ) → ℝ) (hs : Measurable s)
    (hInt : Integrable (fun ω : ((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation n d).World =>
      s ω.1*((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation n d).realizedDuration ω)
      (((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)).worldLaw (Measure.dirac ()))) :
    let π := B.valueThresholdPolicy hw.le hc.le
    let γ := weightedCoarsePolicy P wgt N hKN π d
    Integrable (fun ω : γ.World => weightedCoarseScore P wgt N hKN s ω.1*γ.realizedDuration ω) (P.worldLaw γ.seedLaw) ∧
      (∫ ω : γ.World, weightedCoarseScore P wgt N hKN s ω.1*γ.realizedDuration ω ∂P.worldLaw γ.seedLaw)=
        ∫ ω : (π.finiteCutoffEvaluation n d).World, s ω.1*(π.finiteCutoffEvaluation n d).realizedDuration ω
          ∂((weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N)).worldLaw π.seedLaw := by
  let e := weightedCoarseEmbedding n K N hKN
  let A := P.restrictBy (weightedMeanPermutation P wgt).toEmbedding
  let π := B.valueThresholdPolicy hw.le hc.le
  let Γ := π.finiteCutoffEvaluation n d
  let ΓA := Γ.ignoreExtras e
  let sA := fun x : Fin n → ℝ => s (Model.ZeroSimulation.appendValues x ∘ e)
  have hsA : Measurable sA := hs.comp
    ((measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))).comp (A.appendValues_measurePreserving N).measurable)
  have hLaw : (A.appendZeros N).restrictBy e=
      (weightOrderedPrefix P wgt K).appendIndependent (weightOrderedRemainder P wgt N) :=
    weightedCoarse_restricted_instance P wgt K N hKN
  have hIn : Integrable (fun ω : Γ.World => s ω.1*Γ.realizedDuration ω)
      (((A.appendZeros N).restrictBy e).worldLaw Γ.seedLaw) := by rw [hLaw]; exact hInt
  have hSparse := Γ.ignoreExtras_score_duration (A.appendZeros N) e s hs hIn
  have hReplace : (fun ω : ΓA.World => sA (fun i => ω.1 (i.castAdd N))*ΓA.realizedDuration ω) =ᵐ[(A.appendZeros N).worldLaw ΓA.seedLaw]
      (fun ω => s (ω.1 ∘ e)*ΓA.realizedDuration ω) := by
    filter_upwards [A.appendZeros_values_reconstruct_ae ΓA.seedLaw] with ω hω
    change s (Model.ZeroSimulation.appendValues (fun i => ω.1 (i.castAdd N)) ∘ e)*ΓA.realizedDuration ω=_
    rw [hω]
  have hProjInt := hSparse.1.congr hReplace.symm
  have hNo := B.coarse_no_zero_actions hw hc n d e A
  have hZero := ΓA.simulateZeros_score_duration A hNo sA hsA hProjInt
  have hRel := ΓA.simulateZeros.ignoreExtras_score_duration P (weightedMeanPermutation P wgt).toEmbedding sA hsA hZero.1
  have hEq := hRel.2.trans (hZero.2.trans ((integral_congr_ae hReplace).trans hSparse.2))
  rw [hLaw] at hEq
  exact ⟨hRel.1,hEq⟩
end ProphetSecretary.Limiting
