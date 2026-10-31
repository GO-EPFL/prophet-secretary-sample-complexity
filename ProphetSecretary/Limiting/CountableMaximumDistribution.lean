import ProphetSecretary.Limiting.CountableBenchmark
import ProphetSecretary.Limiting.CountableVoid

/-!
# Distribution of the actual countable maximum above reserve

Individual product tails and the actual configuration void law determine the
benchmark distribution at every level strictly above the terminal reserve.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

lemma maximum_probability_Iic {t : ℝ} (hat : (B.terminal : ℝ) < t) :
    B.valueLaw {v | B.maximum v ≤ t} =
      ENNReal.ofReal (Real.exp (-B.intensity.real (Ioi t))) *
        ∏' i, (B.individuals i : Measure ℝ) (Iic t) := by
  have ht : 0 ≤ t := B.terminal.property.trans hat.le
  have hcap : (B.terminal : ℝ) ≤ B.cap := by exact_mod_cast B.terminal_le_cap
  have he : {v : ValueWorld | B.maximum v ≤ t} =ᵐ[B.valueLaw]
      ({ω : BandConfigurations | ∀ k j, ((ω k).2 j).2 ≤ t} ×ˢ
        univ.pi (fun _ : ℕ => Iic t)) := by
    filter_upwards [B.candidateMaxima_bounded] with v hv
    apply propext
    change (B.maximum v ≤ t) ↔ _
    rw [show (({ω : BandConfigurations | ∀ k j, ((ω k).2 j).2 ≤ t} ×ˢ
      univ.pi (fun _ : ℕ => Iic t)) v) ↔
      (∀ k j, ((v.1 k).2 j).2 ≤ t) ∧ (∀ i, v.2 i ≤ t) by
        exact mem_prod.trans (Iff.rfl.and (by
          simp only [mem_pi,mem_univ,forall_const,mem_Iic]))]
    constructor
    · intro hm
      have hcandidate (i : ℕ) : candidateMaxima v i ≤ t :=
        (le_countableMaximum hcap B.cap.property _ hv i).trans hm
      constructor
      · intro k j
        exact (Model.Instance.le_maximum (fun i : Fin (v.1 k).1 => ((v.1 k).2 i).2) j).trans
          ((le_max_right _ _).trans (hcandidate k))
      · intro i
        exact (le_max_left _ _).trans (hcandidate i)
    · rintro ⟨hp,hx⟩
      apply countableMaximum_le hat.le ht
      intro k
      exact max_le (hx k) (Model.Instance.maximum_le _ ht (hp k))
  rw [measure_congr he,valueLaw,Measure.prod_prod,
    B.bandConfigurations_no_marks_above_probability hat,
    individualValuesLaw,Measure.infinitePi_pi_univ _ (fun _ => measurableSet_Iic)]

end ProphetSecretary.Limiting.CountableInstance
