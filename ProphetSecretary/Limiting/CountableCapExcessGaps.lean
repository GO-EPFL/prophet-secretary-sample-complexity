import ProphetSecretary.Limiting.CountableCapExcessPrefix

/-!
# Strict deficits between prefix excess sums and maxima

A pair of individual excesses costs at least their minimum. Within one
Poisson band the cost is its excess sum minus the excess of its largest mark.
These deterministic deficits survive passage to expected countable maxima.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

private lemma sum_pair_le {N : ℕ} (g : Fin N → ℝ) (hg : ∀ i, 0 ≤ g i)
    (i j : Fin N) (hij : i ≠ j) : g i+g j ≤ ∑ k : Fin N, g k := by
  have hSub : ({i,j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hSub (fun k _ _ => hg k)
  simpa only [Finset.sum_pair hij] using h

private lemma maximumPrefix_capExcess_le_of_bound (B : CountableInstance) (K : ℝ≥0)
    (hK : (B.terminal : ℝ) ≤ K) (N : ℕ) (v : ValueWorld) {D : ℝ} (hD : 0 ≤ D)
    (hEach : ∀ i : Fin N, candidateMaxima v i.val ≤ (K : ℝ)+D) :
    Model.tailValue K (B.maximumPrefix N v) ≤ D := by
  have hMax : B.maximumPrefix N v ≤ (K : ℝ)+D :=
    max_le (hK.trans (le_add_of_nonneg_right hD))
      (Model.Instance.maximum_le _ (add_nonneg K.property hD) hEach)
  exact max_le ((sub_le_iff_le_add).mpr (by simpa only [add_comm] using hMax)) hD

lemma maximumPrefix_capExcess_add_individualOverlap_le (B : CountableInstance) (K : ℝ≥0)
    (hK : (B.terminal : ℝ) ≤ K) (N : ℕ) (v : ValueWorld) (i j : Fin N) (hij : i ≠ j) :
    Model.tailValue K (B.maximumPrefix N v)+min (Model.tailValue K (v.2 i.val)) (Model.tailValue K (v.2 j.val)) ≤
      capExcessPrefix K N v := by
  let g : Fin N → ℝ := fun l => Model.tailValue K (v.2 l.val)+configurationCapExcess K (v.1 l.val)
  let d := min (Model.tailValue K (v.2 i.val)) (Model.tailValue K (v.2 j.val))
  have hg (l : Fin N) : 0 ≤ g l := add_nonneg (Model.tailValue_nonnegative K _) (configurationCapExcess_nonnegative K _)
  have hSum (l : Fin N) : g l ≤ capExcessPrefix K N v :=
    Finset.single_le_sum (f := g) (fun k _ => hg k) (Finset.mem_univ l)
  have hDleI : d ≤ g i := (min_le_left _ _).trans (le_add_of_nonneg_right (configurationCapExcess_nonnegative K _))
  have hDleJ : d ≤ g j := (min_le_right _ _).trans (le_add_of_nonneg_right (configurationCapExcess_nonnegative K _))
  have hD : 0 ≤ capExcessPrefix K N v-d := sub_nonneg.mpr (hDleI.trans (hSum i))
  have hEach (l : Fin N) : candidateMaxima v l.val ≤ (K : ℝ)+(capExcessPrefix K N v-d) := by
    have hBound : g l+d ≤ capExcessPrefix K N v := by
      by_cases hli : l=i
      · subst l
        exact (add_le_add le_rfl hDleJ).trans (sum_pair_le g hg i j hij)
      · exact (add_le_add le_rfl hDleI).trans (sum_pair_le g hg l i hli)
    exact (candidateMaxima_le_cutoff_add_excess K v l.val).trans
      (add_le_add le_rfl ((le_sub_iff_add_le).mpr hBound))
  exact (le_sub_iff_add_le).mp (maximumPrefix_capExcess_le_of_bound B K hK N v hD hEach)

lemma maximumPrefix_capExcess_add_bandOverlap_le (B : CountableInstance) (K : ℝ≥0)
    (hK : (B.terminal : ℝ) ≤ K) (N : ℕ) (v : ValueWorld) (i : Fin N) :
    Model.tailValue K (B.maximumPrefix N v)+configurationCapOverlap K (v.1 i.val) ≤ capExcessPrefix K N v := by
  let g : Fin N → ℝ := fun l => Model.tailValue K (v.2 l.val)+configurationCapExcess K (v.1 l.val)
  let d := configurationCapOverlap K (v.1 i.val)
  have hg (l : Fin N) : 0 ≤ g l := add_nonneg (Model.tailValue_nonnegative K _) (configurationCapExcess_nonnegative K _)
  have hSum (l : Fin N) : g l ≤ capExcessPrefix K N v :=
    Finset.single_le_sum (f := g) (fun k _ => hg k) (Finset.mem_univ l)
  have hDle : d ≤ g i := (sub_le_self _ (Model.tailValue_nonnegative K _)).trans
    (le_add_of_nonneg_left (Model.tailValue_nonnegative K _))
  have hD : 0 ≤ capExcessPrefix K N v-d := sub_nonneg.mpr (hDle.trans (hSum i))
  have hEach (l : Fin N) : candidateMaxima v l.val ≤ (K : ℝ)+(capExcessPrefix K N v-d) := by
    by_cases hli : l=i
    · subst l
      have hX := le_cutoff_add_tailValue K (v.2 i.val)
      have hM := le_cutoff_add_tailValue K (bandMaximum (v.1 i.val))
      have hCandidate : candidateMaxima v i.val ≤
          (K : ℝ)+(Model.tailValue K (v.2 i.val)+Model.tailValue K (bandMaximum (v.1 i.val))) := by
        apply max_le
        · exact hX.trans (add_le_add le_rfl (le_add_of_nonneg_right (Model.tailValue_nonnegative K _)))
        · exact hM.trans (add_le_add le_rfl (le_add_of_nonneg_left (Model.tailValue_nonnegative K _)))
      have hEq : g i-d=Model.tailValue K (v.2 i.val)+Model.tailValue K (bandMaximum (v.1 i.val)) := by
        dsimp only [g,d,configurationCapOverlap]
        ring
      calc
        _ ≤ (K : ℝ)+(g i-d) := by rwa [hEq]
        _ ≤ _ := add_le_add le_rfl (sub_le_sub_right (hSum i) d)
    · have hBound : g l+d ≤ capExcessPrefix K N v :=
        (add_le_add le_rfl hDle).trans (sum_pair_le g hg l i hli)
      exact (candidateMaxima_le_cutoff_add_excess K v l.val).trans
        (add_le_add le_rfl ((le_sub_iff_add_le).mpr hBound))
  exact (le_sub_iff_add_le).mp (maximumPrefix_capExcess_le_of_bound B K hK N v hD hEach)

end ProphetSecretary.Limiting.CountableInstance
