import ProphetSecretary.Reach.ReachHorizonRescaling
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# First-arrival decomposition of independent uniform clocks

The affine map `v ↦ t+(1-t)v` reconstructs every clock remaining after time
`t`. The measure identities below derive the residual law from the original
product uniforms; no conditional independence assertion is assumed.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ProphetSecretary.Model
namespace Instance

/-- Restore a normalized remaining clock after elapsed time `t`. -/
def tailClock (t v : ℝ) : ℝ := t + (1 - t) * v

lemma measurable_tailClock (t : ℝ) : Measurable (tailClock t) :=
  measurable_const.add (measurable_const.mul measurable_id)

/-- The residual uniform law on `[t,1]`, obtained by an affine pushforward. -/
lemma uniformClock_map_tailClock {t : ℝ} (ht : t < 1) :
    uniformClock.map (tailClock t) =
      ENNReal.ofReal (1 - t)⁻¹ • volume.restrict (Icc t 1) := by
  have hh : 0 < 1 - t := sub_pos.mpr ht
  have hp : (tailClock t) ⁻¹' Icc t 1 = Icc (0 : ℝ) 1 := by
    ext v
    simp only [mem_preimage, mem_Icc, tailClock]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> nlinarith
  have hv : volume.map (tailClock t) = ENNReal.ofReal (1 - t)⁻¹ • volume := by
    change volume.map ((fun x : ℝ ↦ t + x) ∘ (fun v : ℝ ↦ (1 - t) * v)) = _
    rw [← Measure.map_map (g := fun x : ℝ ↦ t + x)
      (f := fun v : ℝ ↦ (1 - t) * v) (measurable_const.add measurable_id)
      (measurable_const.mul measurable_id), Real.map_volume_mul_left hh.ne',
      Measure.map_smul, Measure.IsAddLeftInvariant.map_add_left_eq_self,
      abs_of_pos (inv_pos.mpr hh)]
  unfold uniformClock
  rw [← hp, ← Measure.restrict_map (f := tailClock t) (measurable_tailClock t) measurableSet_Icc,
    hv, Measure.restrict_smul]

/-- Restricting a unit clock to the event that it has not yet arrived gives
its remaining probability mass times the residual uniform probability law. -/
lemma uniformClock_restrict_Ici {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    uniformClock.restrict (Ici t) =
      ENNReal.ofReal (1 - t) • uniformClock.map (tailClock t) := by
  have hh : 0 < 1 - t := sub_pos.mpr ht1
  have hi : Ici t ∩ Icc (0 : ℝ) 1 = Icc t 1 := by
    ext v
    constructor
    · rintro ⟨h0, _h1, h2⟩
      exact ⟨h0, h2⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0, ht0.trans h0, h1⟩
  rw [uniformClock_map_tailClock ht1, smul_smul,
    ← ENNReal.ofReal_mul hh.le, mul_inv_cancel₀ hh.ne', ENNReal.ofReal_one, one_smul]
  exact (Measure.restrict_restrict measurableSet_Ici).trans (congrArg volume.restrict hi)

/-- The residual vector of independent uniforms, normalized coordinatewise. -/
def tailClocks (n : ℕ) (t : ℝ) (v : Fin n → ℝ) : Fin n → ℝ := fun j ↦ tailClock t (v j)

lemma measurable_tailClocks (n : ℕ) (t : ℝ) : Measurable (tailClocks n t) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_tailClock t).comp (measurable_pi_apply j)

/-- Conditioning a finite collection of independent clocks to remain unseen
leaves independent uniforms on the remaining interval, with the exact survival
mass `(1-t)^n`. This is a measure equality before normalization. -/
lemma clocksLaw_restrict_all_ge (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (clocksLaw n).restrict {u | ∀ j, t ≤ u j} =
      (ENNReal.ofReal (1 - t)) ^ n • (clocksLaw n).map (tailClocks n t) := by
  let ν := uniformClock.map (tailClock t)
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (measurable_tailClock t).aemeasurable
  haveI : IsFiniteMeasure (ENNReal.ofReal (1 - t) • ν) := by
    constructor
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_lt_top
  have hevent : {u : Fin n → ℝ | ∀ j, t ≤ u j} = univ.pi (fun _ ↦ Ici t) := by
    ext u
    simp only [mem_setOf_eq, mem_pi, mem_univ, forall_true_left, mem_Ici]
  have hmap : (clocksLaw n).map (tailClocks n t) = Measure.pi (fun _ : Fin n ↦ ν) := by
    exact Measure.pi_map_pi (fun _ ↦ (measurable_tailClock t).aemeasurable)
  rw [hevent, hmap, clocksLaw, Measure.restrict_pi_pi]
  simp_rw [uniformClock_restrict_Ici ht0 ht1]
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Candidate `i` is among the earliest arrivals. The overlaps are clock ties,
which have measure zero under the independent uniforms. -/
def firstRegion {n : ℕ} (i : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  {u | ∀ j, u i ≤ u j}

lemma measurableSet_firstRegion {n : ℕ} (i : Fin (n + 1)) : MeasurableSet (firstRegion i) := by
  unfold firstRegion
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)

lemma firstRegion_partition {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (u : Fin (n + 1) → ℝ) (hu : Function.Injective u) :
    (∑ i, (firstRegion i).indicator f u) = f u := by
  classical
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  have himin : u ∈ firstRegion i := fun j ↦ hmin j (Finset.mem_univ j)
  calc
    _ = (firstRegion i).indicator f u := by
      apply Finset.sum_eq_single i
      · intro j _hj hji
        apply Set.indicator_of_notMem
        intro hjmin
        exact hji (hu (le_antisymm (hjmin i) (himin j)))
      · intro hn
        exact False.elim (hn (Finset.mem_univ i))
    _ = f u := Set.indicator_of_mem himin f

lemma lintegral_firstRegion_partition {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ u, f u ∂clocksLaw (n + 1)) =
      ∑ i, ∫⁻ u, (firstRegion i).indicator f u ∂clocksLaw (n + 1) := by
  calc
    _ = ∫⁻ u, ∑ i, (firstRegion i).indicator f u ∂clocksLaw (n + 1) := by
      apply lintegral_congr_ae
      filter_upwards [clocks_pairwise_distinct (n := n + 1)] with u hu
      exact (firstRegion_partition f u hu).symm
    _ = _ := lintegral_finsetSum Finset.univ (fun i _hi ↦ hf.indicator (measurableSet_firstRegion i))

lemma firstRegion_insertNth {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (v : Fin n → ℝ) :
    i.insertNth t v ∈ firstRegion i ↔ ∀ j, t ≤ v j := by
  unfold firstRegion
  simp only [mem_setOf_eq, Fin.insertNth_apply_same]
  rw [i.forall_iff_succAbove]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, le_refl, true_and]

lemma measurable_insertNth {n : ℕ} (i : Fin (n + 1)) :
    Measurable (fun z : ℝ × (Fin n → ℝ) ↦ (i.insertNth z.1 z.2 : Fin (n + 1) → ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm.measurable

/-- Split one candidate's clock from the other clocks, then apply Tonelli.
The first-arrival condition becomes a product rectangle in the other clocks. -/
lemma lintegral_firstRegion_split {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (i : Fin (n + 1)) :
    (∫⁻ u, (firstRegion i).indicator f u ∂clocksLaw (n + 1)) =
      ∫⁻ t, (∫⁻ v, ({v : Fin n → ℝ | ∀ j, t ≤ v j}).indicator
        (fun v ↦ f (i.insertNth t v)) v ∂clocksLaw n) ∂uniformClock := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ uniformClock) i).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i)
  change MeasurePreserving _ (uniformClock.prod (clocksLaw n)) (clocksLaw (n + 1)) at hp
  have hg := hf.indicator (measurableSet_firstRegion i)
  rw [← hp.lintegral_comp hg]
  rw [lintegral_prod (fun a : ℝ × (Fin n → ℝ) ↦
    (firstRegion i).indicator f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm a))
    (hg.comp hp.measurable).aemeasurable]
  apply lintegral_congr
  intro t
  apply lintegral_congr
  intro v
  change (firstRegion i).indicator f (i.insertNth t v) = _
  by_cases h : ∀ j, t ≤ v j
  · exact (Set.indicator_of_mem ((firstRegion_insertNth i t v).mpr h) f).trans
      (Set.indicator_of_mem (s := {v : Fin n → ℝ | ∀ j, t ≤ v j}) (a := v) h
        (fun v ↦ f (i.insertNth t v))).symm
  · exact (Set.indicator_of_notMem (fun hm ↦ h ((firstRegion_insertNth i t v).mp hm)) f).trans
      (Set.indicator_of_notMem (s := {v : Fin n → ℝ | ∀ j, t ≤ v j}) (a := v) h
        (fun v ↦ f (i.insertNth t v))).symm

lemma lintegral_residual_clocks {n : ℕ} {g : (Fin n → ℝ) → ℝ≥0∞}
    (hg : Measurable g) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫⁻ v, ({v : Fin n → ℝ | ∀ j, t ≤ v j}).indicator g v ∂clocksLaw n) =
      (ENNReal.ofReal (1 - t)) ^ n * ∫⁻ v, g (tailClocks n t v) ∂clocksLaw n := by
  have hm : MeasurableSet {v : Fin n → ℝ | ∀ j, t ≤ v j} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le measurable_const (measurable_pi_apply j)
  rw [lintegral_indicator hm, clocksLaw_restrict_all_ge n ht0 ht1,
    lintegral_smul_measure, lintegral_map hg (measurable_tailClocks n t)]
  rfl

/-- The full first-arrival integration identity for a nonnegative measurable
functional of the complete clock vector. The residual clocks are derived
independent uniforms and the exact survival density is `(1-t)^n`. -/
theorem lintegral_firstArrival {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ u, f u ∂clocksLaw (n + 1)) =
      ∑ i : Fin (n + 1), ∫⁻ t,
        (ENNReal.ofReal (1 - t)) ^ n *
          (∫⁻ v, f (i.insertNth t (tailClocks n t v)) ∂clocksLaw n) ∂uniformClock := by
  rw [lintegral_firstRegion_partition hf]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lintegral_firstRegion_split hf i]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc, uniformClock.ae_ne 1] with t ht hne
  exact lintegral_residual_clocks
    (hf.comp ((measurable_insertNth i).comp (measurable_const.prodMk measurable_id)))
    ht.1 (lt_of_le_of_ne ht.2 hne)

/-- Exact density of a specified candidate being first at time `t`. Its mass
is `1/(n+1)`; summing over the `n+1` identities gives total probability one. -/
noncomputable def firstArrivalDensity (n : ℕ) (t : ℝ) : ℝ≥0∞ := (ENNReal.ofReal (1 - t)) ^ n

lemma measurable_firstArrivalDensity (n : ℕ) : Measurable (firstArrivalDensity n) :=
  (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)).pow_const n

abbrev FirstArrivalSample (n : ℕ) := Fin (n + 1) × (ℝ × (Fin n → ℝ))

noncomputable def firstArrivalSampleLaw (n : ℕ) : Measure (FirstArrivalSample n) :=
  Measure.count.prod ((uniformClock.withDensity (firstArrivalDensity n)).prod (clocksLaw n))

def firstArrivalSample {n : ℕ} (z : FirstArrivalSample n) : Fin (n + 1) → ℝ :=
  z.1.insertNth z.2.1 (tailClocks n z.2.1 z.2.2)

lemma measurable_tailClocks_joint (n : ℕ) :
    Measurable (fun z : ℝ × (Fin n → ℝ) ↦ tailClocks n z.1 z.2) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_fst.add ((measurable_const.sub measurable_fst).mul
    ((measurable_pi_apply j).comp measurable_snd))

lemma measurable_firstArrivalSample (n : ℕ) : Measurable (@firstArrivalSample n) := by
  apply measurable_from_prod_countable_right
  intro i
  exact (measurable_insertNth i).comp (measurable_fst.prodMk (measurable_tailClocks_joint n))

lemma lintegral_firstArrivalSample {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ z, f (firstArrivalSample z) ∂firstArrivalSampleLaw n) =
      ∑ i : Fin (n + 1), ∫⁻ t,
        (ENNReal.ofReal (1 - t)) ^ n *
          (∫⁻ v, f (i.insertNth t (tailClocks n t v)) ∂clocksLaw n) ∂uniformClock := by
  unfold firstArrivalSampleLaw
  rw [lintegral_prod (fun z ↦ f (firstArrivalSample z))
    (hf.comp (measurable_firstArrivalSample n)).aemeasurable,
    lintegral_count, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _hi
  have hmi : Measurable (fun z : ℝ × (Fin n → ℝ) ↦ f (firstArrivalSample (i, z))) :=
    hf.comp ((measurable_firstArrivalSample n).comp (measurable_const.prodMk measurable_id))
  rw [lintegral_prod (fun z : ℝ × (Fin n → ℝ) ↦ f (firstArrivalSample (i, z))) hmi.aemeasurable]
  exact lintegral_withDensity_eq_lintegral_mul uniformClock (measurable_firstArrivalDensity n)
    hmi.lintegral_prod_right'

/-- Sampling the first identity, its density-weighted time, and independent
normalized remaining clocks reconstructs exactly the original clock law. -/
theorem firstArrivalSample_measurePreserving (n : ℕ) :
    MeasurePreserving (@firstArrivalSample n) (firstArrivalSampleLaw n) (clocksLaw (n + 1)) := by
  refine ⟨measurable_firstArrivalSample n, ?_⟩
  apply Measure.ext
  intro s hs
  have hf : Measurable (s.indicator (fun _ ↦ (1 : ℝ≥0∞))) := measurable_const.indicator hs
  have h := (lintegral_firstArrivalSample hf).trans (lintegral_firstArrival hf).symm
  have hm := lintegral_map (μ := firstArrivalSampleLaw n) hf (measurable_firstArrivalSample n)
  rw [← hm] at h
  simpa only [lintegral_indicator hs, lintegral_const, Measure.restrict_apply_univ, one_mul] using h

instance firstArrivalSampleLaw_probability (n : ℕ) : IsProbabilityMeasure (firstArrivalSampleLaw n) := by
  have hmap := (firstArrivalSample_measurePreserving n).map_eq
  haveI : IsProbabilityMeasure ((firstArrivalSampleLaw n).map (@firstArrivalSample n)) := by
    rw [hmap]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map (@firstArrivalSample n)

/-- Independent offer values, training data, or policy randomness may be
adjoined unchanged to the first-arrival representation. This is a joint-law
identity for analytical use and supplies no future observations to a policy. -/
theorem firstArrivalSample_with_data {D : Type*} [MeasurableSpace D]
    (ν : Measure D) [SFinite ν] (n : ℕ) :
    MeasurePreserving (fun z : D × FirstArrivalSample n ↦ (z.1, firstArrivalSample z.2))
      (ν.prod (firstArrivalSampleLaw n)) (ν.prod (clocksLaw (n + 1))) :=
  (MeasurePreserving.id ν).prod (firstArrivalSample_measurePreserving n)

end Instance
end ProphetSecretary.Model
