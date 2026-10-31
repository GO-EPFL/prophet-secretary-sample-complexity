import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Model.StandbyIidReward
import ProphetSecretary.Probability.BandScore

/-!
# Original-coordinate zero-atom scores of the virtual direct-approximation block

Retained individual variables receive score zero. Each virtual marginal uses
the same score, centered by removing band mass only from its zero atom. Its
information is at most twice the total band intensity, independently of the
numbers of retained or virtual variables.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

noncomputable def directCloudScore (n N : ℕ) (κ : Measure ℝ) (B : Set ℝ) : Fin (n+N) → ℝ → ℝ :=
  Fin.addCases (fun _ : Fin n => fun _ => 0) (fun _ : Fin N => bandScore κ B)

lemma directCloudScore_complete (n N : ℕ) (κ : Measure ℝ) (B : Set ℝ) (x : Fin (n+N) → ℝ) :
    completeScore (directCloudScore n N κ B) x=
      completeScore (fun _ : Fin N => bandScore κ B) (fun j => x (j.natAdd n)) := by
  simp only [completeScore,Fin.sum_univ_add,directCloudScore,Fin.addCases_left,Fin.addCases_right,
    Finset.sum_const_zero,zero_add]

lemma directCloudScore_properties {n N : ℕ} (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0≤x) {B : Set ℝ} (hB : MeasurableSet B) (hB0 : (0:ℝ)∉B)
    (hq : (1/2:ℝ)≤κ.real {0}) {a : ℝ} (hN : 0<N) (hp : κ.real B=a/(N:ℝ)) :
    let Q := Model.iidOfferInstance κ hκ N
    (∀ i, Measurable (directCloudScore n N κ B i)) ∧
      (∀ i x, |directCloudScore n N κ B i x|≤1) ∧
      (∀ i, (∫ x, directCloudScore n N κ B i x ∂(P.appendIndependent Q).law i)=0) ∧
      information (P.appendIndependent Q).law (directCloudScore n N κ B)≤2*a := by
  let Q := Model.iidOfferInstance κ hκ N
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [directCloudScore,Fin.addCases_left] using (measurable_const : Measurable (fun _ : ℝ => (0:ℝ)))
    | right j => simpa only [directCloudScore,Fin.addCases_right] using measurable_bandScore κ hB
  · intro i x
    induction i using Fin.addCases with
    | left i => norm_num [directCloudScore]
    | right j => simpa only [directCloudScore,Fin.addCases_right] using bandScore_abs_le_one κ hB0 hq x
  · intro i
    induction i using Fin.addCases with
    | left i => simp only [directCloudScore,Fin.addCases_left,integral_zero]
    | right j => simpa only [directCloudScore,Fin.addCases_right,Model.Instance.appendIndependent_law_right,Model.iidOfferInstance] using bandScore_mean κ hB hq
  · have hEq : information (P.appendIndependent Q).law (directCloudScore n N κ B)=
        (N:ℝ)*(∫ x, bandScore κ B x^2 ∂κ) := by
      simp only [information,Fin.sum_univ_add,directCloudScore,Fin.addCases_left,Fin.addCases_right,
        Model.Instance.appendIndependent,Model.iidOfferInstance,Q,zero_pow (by norm_num : (2:ℕ)≠0),
        integral_zero,Finset.sum_const_zero,zero_add,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [hEq]
    calc
      _ ≤ (N:ℝ)*(2*κ.real B) := mul_le_mul_of_nonneg_left (bandScore_secondMoment_le κ hB hB0 hq) (Nat.cast_nonneg N)
      _ = 2*a := by
        rw [hp]
        calc
          _ = 2*((N:ℝ)*(a/(N:ℝ))) := by ring
          _ = _ := by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]
end ProphetSecretary.Limiting
