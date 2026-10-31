import ProphetSecretary.Model.ScalarValueProperties

/-! # Scalar-gap minimizers on prescribed compact coefficient intervals -/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.normalizedScalarGap_exists_interval_minimizer (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi : ℝ}
    (h0 : 0 ≤ lo) (h1 : hi ≤ 1) (hlohi : lo ≤ hi) :
    ∃ a ∈ Icc lo hi, ∀ b ∈ Icc lo hi, normalizedScalarGap P a ≤ normalizedScalarGap P b := by
  exact isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlohi)
    ((normalizedScalarGap_continuousOn P hP).mono (Icc_subset_Icc h0 h1))

end ProphetSecretary.Model
