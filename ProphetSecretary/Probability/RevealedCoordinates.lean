import ProphetSecretary.Model.Independence
import Mathlib.Probability.Process.Filtration

/-!
# Information from a revealed finite coordinate set

Unrevealed coordinates are analytically replaced by zero. The known set of revealed
indices distinguishes a revealed zero from a hidden coordinate. Its generated sigma
algebra increases with that set, and a fresh product coordinate is independent of it.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace ProphetSecretary.Probability

section Masks

variable {ι : Type*} [DecidableEq ι]

def maskCoordinates (s : Finset ι) (x : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ s then x i else 0

lemma measurable_maskCoordinates (s : Finset ι) : Measurable (maskCoordinates s) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ s
  · simpa only [maskCoordinates, hi, ite_true] using (measurable_pi_apply i)
  · simpa only [maskCoordinates, hi, ite_false] using (measurable_const : Measurable fun _ : ι → ℝ => (0 : ℝ))

lemma maskCoordinates_subset {s t : Finset ι} (hst : s ⊆ t) (x : ι → ℝ) :
    maskCoordinates s (maskCoordinates t x) = maskCoordinates s x := by
  funext i
  by_cases hi : i ∈ s
  · simp only [maskCoordinates, hi, hst hi, ite_true]
  · simp only [maskCoordinates, hi, ite_false]

abbrev revealedCoordinateSigma (s : Finset ι) : MeasurableSpace (ι → ℝ) :=
  (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)).comap (maskCoordinates s)

lemma revealedCoordinateSigma_le (s : Finset ι) :
    revealedCoordinateSigma s ≤ (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)) :=
  (measurable_maskCoordinates s).comap_le

lemma revealedCoordinateSigma_mono {s t : Finset ι} (hst : s ⊆ t) :
    revealedCoordinateSigma s ≤ revealedCoordinateSigma t := by
  have ht : @Measurable (ι → ℝ) (ι → ℝ) (revealedCoordinateSigma t) MeasurableSpace.pi
      (maskCoordinates t) := Measurable.of_comap_le le_rfl
  have hcomp : @Measurable (ι → ℝ) (ι → ℝ) (revealedCoordinateSigma t) MeasurableSpace.pi
      (fun x => maskCoordinates s (maskCoordinates t x)) := (measurable_maskCoordinates s).comp ht
  have hs : @Measurable (ι → ℝ) (ι → ℝ) (revealedCoordinateSigma t) MeasurableSpace.pi
      (maskCoordinates s) := by
    convert hcomp using 1
    funext x
    exact (maskCoordinates_subset hst x).symm
  exact hs.comap_le

lemma measurable_of_mask_invariant {s : Finset ι} {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hinv : ∀ x, f (maskCoordinates s x) = f x) :
    @Measurable (ι → ℝ) ℝ (revealedCoordinateSigma s) Real.measurableSpace f := by
  have hm : @Measurable (ι → ℝ) (ι → ℝ) (revealedCoordinateSigma s) MeasurableSpace.pi
      (maskCoordinates s) := Measurable.of_comap_le le_rfl
  have h := hf.comp hm
  convert h using 1
  funext x
  exact (hinv x).symm

lemma coordinate_revealed_measurable {s : Finset ι} {i : ι} (hi : i ∈ s) :
    @Measurable (ι → ℝ) ℝ (revealedCoordinateSigma s) Real.measurableSpace (fun x => x i) := by
  apply measurable_of_mask_invariant (measurable_pi_apply i)
  intro x
  simp only [maskCoordinates, hi, ite_true]

/-- Restore a partial revealed vector using the same deterministic zero mask. -/
def extendRevealedCoordinates (s : Finset ι) (y : s → ℝ) : ι → ℝ :=
  fun i => if hi : i ∈ s then y ⟨i, hi⟩ else 0

lemma measurable_extendRevealedCoordinates (s : Finset ι) :
    Measurable (extendRevealedCoordinates s) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ s
  · simpa only [extendRevealedCoordinates, hi, dite_true] using (measurable_pi_apply (⟨i, hi⟩ : s))
  · simpa only [extendRevealedCoordinates, hi, dite_false] using
      (measurable_const : Measurable fun _ : s → ℝ => (0 : ℝ))

/-- The mask representation gives exactly mathlib's standard finite-coordinate
filtration. In particular, assigning hidden coordinates zero loses no revealed zero. -/
lemma revealedCoordinateSigma_eq_piFinset (s : Finset ι) :
    revealedCoordinateSigma s = Filtration.piFinset (X := fun _ : ι => ℝ) s := by
  apply le_antisymm
  · have he : maskCoordinates s = extendRevealedCoordinates s ∘ s.restrict := by
      funext x i
      by_cases hi : i ∈ s <;> simp [maskCoordinates, extendRevealedCoordinates, hi]
    change MeasurableSpace.pi.comap (maskCoordinates s) ≤ MeasurableSpace.pi.comap s.restrict
    rw [he, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_extendRevealedCoordinates s).comap_le
  · have hm : @Measurable (ι → ℝ) (ι → ℝ) (revealedCoordinateSigma s) MeasurableSpace.pi
        (maskCoordinates s) := Measurable.of_comap_le le_rfl
    have hr : @Measurable (ι → ℝ) (s → ℝ) (revealedCoordinateSigma s) MeasurableSpace.pi
        s.restrict := by
      have hcomp := s.measurable_restrict.comp hm
      convert hcomp using 1
      funext x i
      change x i.val = if i.val ∈ s then x i.val else 0
      rw [if_pos i.property]
    exact hr.comap_le

end Masks

section Order

variable {ι : Type*}

/-- Coordinates strictly before `m` in a prescribed finite revelation order. -/
def coordinatesBefore {K : ℕ} (e : Fin K ≃ ι) (m : ℕ) : Finset ι :=
  (Finset.univ.filter (fun j : Fin K => j.val < m)).map e.toEmbedding

lemma mem_coordinatesBefore {K : ℕ} (e : Fin K ≃ ι) (m : ℕ) (i : ι) :
    i ∈ coordinatesBefore e m ↔ (e.symm i).val < m := by
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hi
    have hjm := (Finset.mem_filter.mp hj).2
    rw [← he]
    change (e.symm (e j)).val < m
    simpa only [e.symm_apply_apply] using hjm
  · intro hi
    apply Finset.mem_map.mpr
    exact ⟨e.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, e.apply_symm_apply i⟩

lemma coordinatesBefore_mono {K : ℕ} (e : Fin K ≃ ι) : Monotone (coordinatesBefore e) := by
  intro m m' hmm' i hi
  rw [mem_coordinatesBefore] at hi ⊢
  exact hi.trans_le hmm'

lemma coordinatesBefore_fresh {K : ℕ} (e : Fin K ≃ ι) {m : ℕ} (hm : m < K) :
    e ⟨m, hm⟩ ∉ coordinatesBefore e m := by
  rw [mem_coordinatesBefore]
  simp only [e.symm_apply_apply, Fin.val_mk, lt_self_iff_false, not_false_eq_true]

lemma coordinatesBefore_succ [DecidableEq ι] {K : ℕ} (e : Fin K ≃ ι) {m : ℕ} (hm : m < K) :
    coordinatesBefore e (m + 1) = insert (e ⟨m, hm⟩) (coordinatesBefore e m) := by
  ext i
  rw [mem_coordinatesBefore, Finset.mem_insert, mem_coordinatesBefore]
  have he : i = e ⟨m, hm⟩ ↔ (e.symm i).val = m := by
    constructor
    · intro h
      rw [h, e.symm_apply_apply]
    · intro h
      apply e.symm.injective
      rw [e.symm_apply_apply]
      exact Fin.ext h
  rw [he]
  omega

/-- Use mathlib's finite-coordinate sigma algebras in the actual reveal order. -/
def coordinateRevealFiltration {K : ℕ} (e : Fin K ≃ ι) :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)) where
  seq m := Filtration.piFinset (X := fun _ : ι => ℝ) (coordinatesBefore e m)
  mono' _ _ h := (Filtration.piFinset (X := fun _ : ι => ℝ)).mono (coordinatesBefore_mono e h)
  le' m := (Filtration.piFinset (X := fun _ : ι => ℝ)).le (coordinatesBefore e m)

end Order

section Independence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

omit [Fintype ι] in
lemma maskCoordinates_erase {s : Finset ι} {i : ι} (hi : i ∉ s) (x : ι → ℝ) :
    maskCoordinates s (ProphetSecretary.Model.eraseCoordinate i 0 x) = maskCoordinates s x := by
  funext j
  by_cases hj : j ∈ s
  · have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp only [maskCoordinates, hj, ite_true, ProphetSecretary.Model.eraseCoordinate, Function.update_of_ne hji]
  · simp only [maskCoordinates, hj, ite_false]

/-- Independence is derived from the actual product law and the erasure identity. -/
lemma revealedCoordinates_fresh_independent {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (maskCoordinates s) (fun x : ι → ℝ => x i) (Measure.pi μ) := by
  have h := ProphetSecretary.Model.erasedFunctional_independent μ i 0 (maskCoordinates s) (measurable_maskCoordinates s)
  convert h using 1
  funext x
  exact (maskCoordinates_erase hi x).symm

/-- The revealed vector together with a fresh sample has the derived product law. -/
lemma revealedCoordinates_fresh_pair_measurePreserving {s : Finset ι} {i : ι} (hi : i ∉ s) :
    MeasurePreserving (fun x : ι → ℝ => (maskCoordinates s x, x i)) (Measure.pi μ)
      (((Measure.pi μ).map (maskCoordinates s)).prod (μ i)) := by
  have hmap := (revealedCoordinates_fresh_independent μ hi).map_prod_eq_prod_map_map
    (measurable_maskCoordinates s).aemeasurable (measurable_pi_apply i).aemeasurable
  have heval : (Measure.pi μ).map (fun x : ι → ℝ => x i) = μ i := (measurePreserving_eval μ i).map_eq
  rw [heval] at hmap
  exact ⟨(measurable_maskCoordinates s).prodMk (measurable_pi_apply i), hmap⟩

end Independence

end ProphetSecretary.Probability
