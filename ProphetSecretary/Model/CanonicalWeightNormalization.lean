import ProphetSecretary.Model.CanonicalNormalization

/-!
# Normalizing positive scalar weights preserves every canonical decision

Dividing both weights by their sum leaves every threshold, including ties,
unchanged on every raw history. The bundled policies are equal before they
are evaluated under any possibly different independent offer laws.
-/
open MeasureTheory
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma Instance.valueThreshold_weightNormalized (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0<w) (hc : 0≤c)
    (A : Finset (Fin n)) (t : ℝ) (i : Fin n) :
    P.valueThreshold w c A t i=P.valueThreshold (w/(w+c)) (c/(w+c)) A t i := by
  have hs : 0<w+c := add_pos_of_pos_of_nonneg hw hc
  rw [P.valueThreshold_rewardNormalized hP hw hc,
    P.valueThreshold_rewardNormalized hP (div_pos hw hs) (div_nonneg hc hs.le)]
  have hRatio : (c/(w+c))/(w/(w+c))=c/w := by
    field_simp [hw.ne',hs.ne']
  rw [hRatio]

lemma Instance.valuePolicy_weightNormalized (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    P.valuePolicy hP hw.le hc=
      P.valuePolicy hP (w := w/(w+c)) (c := c/(w+c))
        (div_nonneg hw.le (add_pos_of_pos_of_nonneg hw hc).le)
        (div_nonneg hc (add_pos_of_pos_of_nonneg hw hc).le) := by
  have hThreshold : (fun (_ : Unit) A t i => P.valueThreshold w c A t i)=
      fun (_ : Unit) A t i => P.valueThreshold (w/(w+c)) (c/(w+c)) A t i := by
    funext r A t i
    exact P.valueThreshold_weightNormalized hP hw hc A t i
  unfold Instance.valuePolicy
  simp only [hThreshold]

lemma Instance.valuePolicy_weightNormalized_rule (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    (P.valuePolicy hP hw.le hc).rule=
      (P.valuePolicy hP (w := w/(w+c)) (c := c/(w+c))
        (div_nonneg hw.le (add_pos_of_pos_of_nonneg hw hc).le)
        (div_nonneg hc (add_pos_of_pos_of_nonneg hw hc).le)).rule := by
  change thresholdPolicy (fun (_ : Unit) A t i => P.valueThreshold w c A t i)=
    thresholdPolicy (fun (_ : Unit) A t i => P.valueThreshold (w/(w+c)) (c/(w+c)) A t i)
  congr 1
  funext r A t i
  exact P.valueThreshold_weightNormalized hP hw hc A t i

lemma Instance.valuePolicy_weightNormalized_payoffs (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    let π := P.valuePolicy hP hw.le hc
    let ρ := P.valuePolicy hP (w := w/(w+c)) (c := c/(w+c))
      (div_nonneg hw.le (add_pos_of_pos_of_nonneg hw hc).le)
      (div_nonneg hc (add_pos_of_pos_of_nonneg hw hc).le)
    π.expectedReward Q=ρ.expectedReward Q ∧ π.expectedDuration Q=ρ.expectedDuration Q := by
  dsimp only
  rw [P.valuePolicy_weightNormalized hP hw hc]
  exact ⟨rfl,rfl⟩

end ProphetSecretary.Model
