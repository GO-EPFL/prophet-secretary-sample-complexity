import ProphetSecretary.Model.VariableDeletion
import ProphetSecretary.Model.ZeroVariableValue

/-!
# Scalar cost of removing a rare variable in a continuation state

The quantitative stop-loss comparison first zeros the chosen marginal while
retaining its observed identity. The causal zero-removal theorem then deletes
that identity. The resulting bound has no additional instance-size factor.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.zeroCoordinate (P : Instance n) (i : Fin n) : Instance n where
  law := Function.update P.law i (Measure.dirac 0)
  probability := by
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      infer_instance
    · simpa only [Function.update_of_ne hj] using P.probability j
  nonnegative := by
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      simp
    · simpa only [Function.update_of_ne hj] using P.nonnegative j

lemma Instance.zeroCoordinate_law_self (P : Instance n) (i : Fin n) :
    (P.zeroCoordinate i).law i = Measure.dirac 0 := by simp only [zeroCoordinate, Function.update_self]

lemma Instance.zeroCoordinate_law_of_ne (P : Instance n) (i j : Fin n) (hji : j ≠ i) :
    (P.zeroCoordinate i).law j = P.law j := by simp only [zeroCoordinate, Function.update_of_ne hji]

lemma Instance.zeroCoordinate_integrable_maximum (P : Instance n) (i : Fin n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    Integrable Instance.maximum (P.zeroCoordinate i).valuesLaw := by
  apply Instance.integrable_maximum
  intro j
  by_cases hj : j = i
  · subst j
    rw [P.zeroCoordinate_law_self i]
    exact integrable_dirac (by simp)
  · rw [P.zeroCoordinate_law_of_ne i j hj]
    exact (P.integrable_maximum_iff.mp hP) j

lemma Instance.zeroCoordinate_restrictTo_erase (P : Instance n) (i : Fin n) :
    (P.zeroCoordinate i).restrictTo (Finset.univ.erase i) = P.restrictTo (Finset.univ.erase i) := by
  apply Instance.eq_of_law_eq
  funext j
  change (P.zeroCoordinate i).law (stateEmbedding (Finset.univ.erase i) j) = _
  exact P.zeroCoordinate_law_of_ne i _
    (Finset.mem_erase.mp ((Finset.univ.erase i).orderEmbOfFin_mem rfl j)).1

/-- The exact first-moment deletion budget in every sorted unseen state. -/
lemma Instance.optimalScalarValue_restrictTo_remove_loss (P : Instance n) (A : Finset (Fin n)) (i : Fin n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    0 ≤ optimalScalarValue (P.restrictTo A) w c - optimalScalarValue (P.restrictTo (A.erase i)) w c ∧
      optimalScalarValue (P.restrictTo A) w c - optimalScalarValue (P.restrictTo (A.erase i)) w c ≤ w * ∫ x, x ∂P.law i := by
  by_cases hiA : i ∈ A
  · let R := P.restrictTo A
    let k := stateIndex A i hiA
    let Q := R.zeroCoordinate k
    have hek : stateEmbedding A k = i := stateEmbedding_stateIndex A i hiA
    have hR : Integrable Instance.maximum R.valuesLaw := P.restrictTo_integrable_maximum A hP
    have hQ : Integrable Instance.maximum Q.valuesLaw := R.zeroCoordinate_integrable_maximum k hR
    have hloss := R.optimalScalarValue_single_zero_loss Q hR hQ k (R.zeroCoordinate_law_self k)
      (fun j hj => R.zeroCoordinate_law_of_ne k j hj) hw hc
    have hQval : optimalScalarValue Q w c = optimalScalarValue (P.restrictTo (A.erase i)) w c := by
      calc
        _ = optimalScalarValue (Q.restrictTo (Finset.univ.erase k)) w c :=
          Q.optimalScalarValue_remove_zero k hQ (R.zeroCoordinate_law_self k) hw.le hc
        _ = optimalScalarValue (R.restrictTo (Finset.univ.erase k)) w c := by rw [R.zeroCoordinate_restrictTo_erase k]
        _ = _ := by
          have hmap : (Finset.univ.erase k).map (stateEmbedding A) = A.erase i := by
            rw [Finset.map_erase]
            change (Finset.univ.map (A.orderEmbOfFin rfl).toEmbedding).erase (stateEmbedding A k) = _
            rw [A.map_orderEmbOfFin_univ rfl, hek]
          have hr := P.optimalScalarValue_restrictTo_map (A.orderEmbOfFin rfl) (Finset.univ.erase k) hP hw.le hc
          change optimalScalarValue (R.restrictTo (Finset.univ.erase k)) w c =
            optimalScalarValue (P.restrictTo ((Finset.univ.erase k).map (stateEmbedding A))) w c at hr
          rwa [hmap] at hr
    have hmean : (∫ x, x ∂R.law k) = ∫ x, x ∂P.law i := by
      change (∫ x, x ∂P.law (stateEmbedding A k)) = _
      rw [hek]
    rwa [hQval, hmean] at hloss
  · rw [Finset.erase_eq_of_notMem hiA]
    simp only [sub_self, le_refl, true_and]
    exact mul_nonneg hw.le (integral_nonneg_of_ae (P.nonnegative i))

/-- For a capped variable, its positive-arrival probability controls the cost. -/
lemma Instance.optimalScalarValue_restrictTo_remove_rare (P : Instance n) (A : Finset (Fin n)) (i : Fin n)
    (hP : Integrable Instance.maximum P.valuesLaw) {H w c : ℝ} (hbound : ∀ᵐ x ∂P.law i, x ≤ H)
    (hw : 0 < w) (hc : 0 ≤ c) :
    0 ≤ optimalScalarValue (P.restrictTo A) w c - optimalScalarValue (P.restrictTo (A.erase i)) w c ∧
      optimalScalarValue (P.restrictTo A) w c - optimalScalarValue (P.restrictTo (A.erase i)) w c ≤
        w * H * (P.law i).real (Ioi 0) := by
  have h := P.optimalScalarValue_restrictTo_remove_loss A i hP hw hc
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ ≤ w * (H * (P.law i).real (Ioi 0)) :=
      mul_le_mul_of_nonneg_left (P.marginalMean_le_cap_positiveProbability hP i hbound) hw.le
    _ = _ := by ring

end ProphetSecretary.Model
