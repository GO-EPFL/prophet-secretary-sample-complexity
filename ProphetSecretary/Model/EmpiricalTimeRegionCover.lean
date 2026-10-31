import ProphetSecretary.Model.ClockEarlyLoss
import ProphetSecretary.Statistics.TrueCriticalEntrance
import ProphetSecretary.Analysis.DyadicBandCover

/-!
# Actual near/far/early coverage of the candidate arrival time

After freezing the other clocks and training information, the only excluded
times are countably many true entrance points. They have zero uniform-clock
mass. Each earlier dyadic band starts strictly after its own entrance at twice
the band level, matching the actual post-entrance error envelope.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.empirical_time_region_cover_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a z x : ℝ}
    (hhi : 0 ≤ hi) (ha : 0 < a) (u : Fin n → ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      (t ∈ Ioc (P.trueCriticalEntrance hi a u) 1 ∧ x / 2 ≤ P.clockContinuation z u t) ∨
      (t ∈ Ioc (P.trueCriticalEntrance hi a u) 1 ∧ P.clockContinuation z u t < x / 2) ∨
      ∃ j : ℕ, t ∈ Ioc (P.trueCriticalEntrance hi (2 * ((2 : ℝ) ^ j * a)) u) 1 ∧
        (2 : ℝ) ^ j * a ≤ P.clockContinuation hi u t := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have hn : ∀ᵐ t ∂μ, t ≠ P.trueCriticalEntrance hi a u := μ.ae_ne _
  have hns : ∀ᵐ t ∂μ, ∀ j : ℕ, t ≠ P.trueCriticalEntrance hi (2 * ((2 : ℝ) ^ j * a)) u :=
    ae_all_iff.mpr fun _ => μ.ae_ne _
  filter_upwards [ae_restrict_mem measurableSet_Icc, hn, hns] with t ht hnt hnts
  by_cases hlow : P.clockContinuation hi u t ≤ a
  · have hcrit : P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1 - t) 1 hi ≤ a := by
      rw [P.clockContinuation_eq hi u ht.2] at hlow
      exact hlow
    have hle := P.trueCriticalEntrance_le_of_critical hP hhi u ht.1 ht.2 hcrit
    have hlt : P.trueCriticalEntrance hi a u < t := lt_of_le_of_ne hle (Ne.symm hnt)
    by_cases hx : x / 2 ≤ P.clockContinuation z u t
    · exact Or.inl ⟨⟨hlt, ht.2⟩, hx⟩
    · exact Or.inr (Or.inl ⟨⟨hlt, ht.2⟩, lt_of_not_ge hx⟩)
  · obtain ⟨j, hj, hj'⟩ := ProphetSecretary.Analysis.exists_dyadic_band ha (not_le.mp hlow).le
    have heq : (2 : ℝ) ^ (j + 1) * a = 2 * ((2 : ℝ) ^ j * a) := by rw [pow_succ]; ring
    rw [heq] at hj'
    have hcrit : P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1 - t) 1 hi ≤
        2 * ((2 : ℝ) ^ j * a) := by
      rw [P.clockContinuation_eq hi u ht.2] at hj'
      exact hj'
    have hle := P.trueCriticalEntrance_le_of_critical hP hhi u ht.1 ht.2 hcrit
    have hlt := lt_of_le_of_ne hle (Ne.symm (hnts j))
    exact Or.inr (Or.inr ⟨j, ⟨hlt, ht.2⟩, hj⟩)

end ProphetSecretary.Model
