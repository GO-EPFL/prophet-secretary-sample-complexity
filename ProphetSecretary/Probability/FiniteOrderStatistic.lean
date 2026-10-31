import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Finite order statistics retaining repeated observations

The r-th largest observation is the maximum, over r-element subsets of sample
identities, of the minimum observation in that subset. This representation
keeps ties and yields exact closed/strict threshold-count characterizations.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Probability
variable {ι α : Type*} [Fintype ι] [LinearOrder α]

noncomputable def orderSubsets (ι : Type*) [Fintype ι] (r : ℕ) : Finset (Finset ι) :=
  Finset.univ.powersetCard r

lemma orderSubsets_nonempty {r : ℕ} (hr : r≤Fintype.card ι) : (orderSubsets ι r).Nonempty := by
  apply Finset.powersetCard_nonempty.mpr
  simpa only [Finset.card_univ] using hr

lemma orderSubset_nonempty {r : ℕ} (hr : 0<r) {A : Finset ι} (hA : A∈orderSubsets ι r) : A.Nonempty := by
  have hCard := (Finset.mem_powersetCard.mp hA).2
  exact Finset.card_pos.mp (by rwa [hCard])

noncomputable def sampleOrderStatistic (r : ℕ) (hr0 : 0<r) (hrN : r≤Fintype.card ι) (x : ι → α) : α :=
  (orderSubsets ι r).attach.sup' (Finset.attach_nonempty_iff.mpr (orderSubsets_nonempty hrN))
    (fun A => A.val.inf' (orderSubset_nonempty hr0 A.property) x)

lemma le_sampleOrderStatistic_iff (r : ℕ) (hr0 : 0<r) (hrN : r≤Fintype.card ι) (x : ι → α) (c : α) :
    c≤sampleOrderStatistic r hr0 hrN x ↔ r≤(Finset.univ.filter (fun i => c≤x i)).card := by
  rw [sampleOrderStatistic,Finset.le_sup'_iff]
  constructor
  · rintro ⟨A,_,hMin⟩
    have hSub : A.val⊆Finset.univ.filter (fun i => c≤x i) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hMin.trans (Finset.inf'_le x hi)⟩
    have hCard := Finset.card_le_card hSub
    rwa [(Finset.mem_powersetCard.mp A.property).2] at hCard
  · intro hCount
    obtain ⟨A,hSub,hCard⟩ := Finset.exists_subset_card_eq hCount
    have hA : A∈orderSubsets ι r := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hCard⟩
    refine ⟨⟨A,hA⟩,Finset.mem_attach _ _,?_⟩
    apply Finset.le_inf'
    intro i hi
    exact (Finset.mem_filter.mp (hSub hi)).2

lemma lt_sampleOrderStatistic_iff (r : ℕ) (hr0 : 0<r) (hrN : r≤Fintype.card ι) (x : ι → α) (c : α) :
    c<sampleOrderStatistic r hr0 hrN x ↔ r≤(Finset.univ.filter (fun i => c<x i)).card := by
  rw [sampleOrderStatistic,Finset.lt_sup'_iff]
  constructor
  · rintro ⟨A,_,hMin⟩
    have hSub : A.val⊆Finset.univ.filter (fun i => c<x i) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hMin.trans_le (Finset.inf'_le x hi)⟩
    have hCard := Finset.card_le_card hSub
    rwa [(Finset.mem_powersetCard.mp A.property).2] at hCard
  · intro hCount
    obtain ⟨A,hSub,hCard⟩ := Finset.exists_subset_card_eq hCount
    have hA : A∈orderSubsets ι r := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hCard⟩
    refine ⟨⟨A,hA⟩,Finset.mem_attach _ _,?_⟩
    rw [Finset.lt_inf'_iff]
    intro i hi
    exact (Finset.mem_filter.mp (hSub hi)).2

lemma sampleOrderStatistic_lt_iff (r : ℕ) (hr0 : 0<r) (hrN : r≤Fintype.card ι) (x : ι → α) (c : α) :
    sampleOrderStatistic r hr0 hrN x<c ↔ (Finset.univ.filter (fun i => c≤x i)).card<r := by
  rw [←not_le,le_sampleOrderStatistic_iff,not_le]

lemma sampleOrderStatistic_nonnegative {α : Type*} [LinearOrder α] [Zero α]
    (r : ℕ) (hr0 : 0<r) (hrN : r≤Fintype.card ι) (x : ι → α) (hx : ∀ i, 0≤x i) :
    0≤sampleOrderStatistic r hr0 hrN x := by
  rw [le_sampleOrderStatistic_iff]
  simpa only [Finset.filter_true_of_mem (fun i _ => hx i),Finset.card_univ] using hrN

lemma measurable_sampleOrderStatistic [MeasurableSpace α] [MeasurableSup₂ α] [MeasurableInf₂ α]
    (r : ℕ) (hr0 : 0<r) (hrN : r≤Fintype.card ι) :
    Measurable (sampleOrderStatistic (α:=α) r hr0 hrN) := by
  have hMin (A : {A : Finset ι // A∈orderSubsets ι r}) :
      Measurable (fun x : ι → α => A.val.inf' (orderSubset_nonempty hr0 A.property) x) := by
    have h : Measurable (A.val.inf' (orderSubset_nonempty hr0 A.property) (fun i (x : ι → α) => x i)) :=
      Finset.inf'_induction (orderSubset_nonempty hr0 A.property) _
        (fun _f hf _g hg => hf.inf hg) (fun i _ => measurable_pi_apply i)
    convert h using 1
    funext x
    simp only [Finset.inf'_apply]
  have hSup := Finset.measurable_sup' (Finset.attach_nonempty_iff.mpr (orderSubsets_nonempty hrN))
    (fun A _ => hMin A)
  convert hSup using 1
  funext x
  simp only [sampleOrderStatistic,Finset.sup'_apply]

end ProphetSecretary.Probability
