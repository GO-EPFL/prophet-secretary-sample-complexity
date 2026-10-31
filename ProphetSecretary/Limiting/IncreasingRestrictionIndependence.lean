import ProphetSecretary.Limiting.CountableWindowIndependence

/-!
# Independence through increasing observation regions

An increasing union may have infinite counting mass. The proof retains
extended-real evaluations and the directed union of the actual observation
sigma-algebras throughout.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting

theorem indepFun_restrict_iUnion {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {P : Measure Ω} [IsProbabilityMeasure P] {M : Ω → Measure Point} {X : Ω → A}
    (hM : Measurable M) (hX : Measurable X) (W : ℕ → Set Point)
    (hW : ∀ n, MeasurableSet (W n)) (hMono : Monotone W)
    (h : ∀ n, IndepFun (fun ω => (M ω).restrict (W n)) X P) :
    IndepFun (fun ω => (M ω).restrict (⋃ n, W n)) X P := by
  let R := fun n : ℕ => fun ω => (M ω).restrict (W n)
  let m := fun n : ℕ => MeasurableSpace.comap (R n) inferInstance
  have hRm (n) : Measurable (R n) := (measurable_restrict_pointMeasure (hW n)).comp hM
  have hmMono : Monotone m := by
    intro i j hij
    have hRj : @Measurable Ω (Measure Point) (m j) inferInstance (R j) :=
      Measurable.of_comap_le le_rfl
    have hRi := (measurable_restrict_pointMeasure (hW i)).comp hRj
    have he : (fun μ : Measure Point => μ.restrict (W i)) ∘ R j = R i := by
      funext ω
      change ((M ω).restrict (W j)).restrict (W i) = _
      rw [Measure.restrict_restrict (hW i),inter_eq_left.mpr (hMono hij)]
    rw [he] at hRi
    exact hRi.comap_le
  have hDir : Directed (· ⊆ ·) W := fun i j =>
    ⟨max i j,hMono (le_max_left i j),hMono (le_max_right i j)⟩
  have hUnion : @Measurable Ω (Measure Point) (⨆ n, m n) inferInstance
      (fun ω => (M ω).restrict (⋃ n, W n)) := by
    letI : MeasurableSpace Ω := ⨆ n, m n
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have he : (fun ω => ((M ω).restrict (⋃ n, W n)) S) =
        fun ω => ⨆ n, R n ω S := by
      funext ω
      exact Measure.restrict_iUnion_apply_eq_iSup hDir hS
    rw [he]
    apply Measurable.iSup
    intro n
    have hR : Measurable (R n) := Measurable.of_comap_le (le_iSup m n)
    exact (Measure.measurable_coe hS).comp hR
  have hInd (n) : Indep (m n) (MeasurableSpace.comap X inferInstance) P :=
    (IndepFun_iff_Indep _ _ _).mp (h n)
  have hSup := indep_iSup_of_monotone hInd (fun n => (hRm n).comap_le) hX.comap_le hmMono
  exact (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le_left hSup hUnion.comap_le)

end ProphetSecretary.Limiting
