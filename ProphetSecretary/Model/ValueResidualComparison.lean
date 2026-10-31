import ProphetSecretary.Model.BellmanResidual

/-!
# Converting proved uniform residual bounds into a value comparison

The upper comparison ranges over the full admissible policy class. The reverse
comparison evaluates the fixed design optimizer under the other law. Action
losses have the established sign and vanish only for that canonical optimizer.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem optimalScalarValue_comparison_of_residual_bounds (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c l u : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hres : ∀ π : RandomizedPolicy n,
      l ≤ π.expectedReachedTransitionResidual Q P w c ∧ π.expectedReachedTransitionResidual Q P w c ≤ u) :
    optimalScalarValue P w c ≤ optimalScalarValue Q w c - l ∧
      optimalScalarValue Q w c ≤ optimalScalarValue P w c + u := by
  constructor
  · apply csSup_le (scalarValues_nonempty P w c)
    rintro _ ⟨π,rfl⟩
    change π.scalarObjective P w c ≤ _
    have he := π.bellman_residualIdentity_split Q P hQ hP hw hc
    have hL := π.expectedReachedDesignActionLoss_nonnegative Q P w c
    have hr := (hres π).1
    linarith only [he,hL,hr]
  · let π := Q.valuePolicy hQ hw.le hc
    have he := π.bellman_residualIdentity_split Q P hQ hP hw hc
    rw [Q.valuePolicy_expectedDesignActionLoss_zero P hQ hw hc, add_zero] at he
    have hV := scalarObjective_le_optimal π P hP hw.le hc
    have hr := (hres π).2
    linarith only [he,hV,hr]

end ProphetSecretary.Model
