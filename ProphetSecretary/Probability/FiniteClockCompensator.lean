import ProphetSecretary.Probability.UniformHazard
import ProphetSecretary.Model.ClockReplacement
import ProphetSecretary.Model.PrefixSurvival
import ProphetSecretary.Reach.Pending

/-!
# Finite clock compensation with the actual observation history

Keeping a candidate pending preserves survival until any time before its clock.
The auxiliary execution is constructed from the original rule, and replacing
that clock by a fresh independent uniform gives the compensator identities.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma Policy.survival_iff_pending_of_not_arrived (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) {t : ℝ} (ht : t ≤ 1) (hi : t ≤ u i) :
    t ≤ π.stoppingTime r Finset.univ x u ↔ t ≤ π.pendingTime r x u i := by
  rw [Policy.pendingTime, π.le_stoppingTime_iff_no_earlier_acceptance r Finset.univ x u ht,
    π.le_stoppingTime_iff_no_earlier_acceptance r (Finset.univ.erase i) x u ht]
  constructor
  · intro h j hj hju
    rw [π.action_pending_eq r x u i j (hju.le.trans hi)]
    exact h j (Finset.mem_univ _) hju
  · intro h j _ hju
    have hji : j ≠ i := by
      intro he
      subst j
      exact (not_lt_of_ge hi) hju
    rw [← π.action_pending_eq r x u i j (hju.le.trans hi)]
    exact h j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩) hju

namespace Instance

variable [MeasurableSpace Seed]

def eraseClock (i : Fin n) (ω : World n Seed) : World n Seed := replaceClock i (ω, 1)

lemma measurable_eraseClock (i : Fin n) : Measurable (@eraseClock n Seed i) := by
  unfold eraseClock replaceClock
  exact measurable_fst.prodMk ((measurable_pi_lambda _ (fun j => by
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (measurable_const : Measurable (fun _ : World n Seed => (1 : ℝ)))
    · simpa only [Function.update_of_ne hji, Function.comp_def] using
        (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))).prodMk
          (measurable_snd.comp measurable_snd))

omit [MeasurableSpace Seed] in
lemma eraseClock_replaceClock (i : Fin n) (z : World n Seed × ℝ) :
    eraseClock i (replaceClock i z) = eraseClock i z.1 := by
  simp [eraseClock, replaceClock, Function.update_idem]

end Instance
end ProphetSecretary.Model

namespace ProphetSecretary.Probability

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def clockReachedPremium (π : Model.Policy Seed n) (i : Fin n)
    (g : ℝ × Model.World n Seed → ℝ≥0∞) (ω : Model.World n Seed) : ℝ≥0∞ :=
  if π.Reaches ω.2.2 ω.1 ω.2.1 i then g (ω.2.1 i, Model.Instance.eraseClock i ω) else 0

lemma measurable_clockReachedPremium (π : Model.Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n)
    (g : ℝ × Model.World n Seed → ℝ≥0∞) (hg : Measurable g) : Measurable (clockReachedPremium π i g) := by
  exact Measurable.ite (π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)
    (hg.comp (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).prodMk
      (Model.Instance.measurable_eraseClock i))) measurable_const

omit [MeasurableSpace Seed] in
lemma clockReachedPremium_replaceClock (π : Model.Policy Seed n) (i : Fin n)
    (g : ℝ × Model.World n Seed → ℝ≥0∞) (z : Model.World n Seed × ℝ) (hu : z.2 ≤ 1) :
    clockReachedPremium π i g (Model.Instance.replaceClock i z) =
      if z.2 ≤ π.pendingTime z.1.2.2 z.1.1 z.1.2.1 i then g (z.2, Model.Instance.eraseClock i z.1) else 0 := by
  unfold clockReachedPremium
  rw [π.reaches_iff_le_pendingTime _ _ _ i (by simpa only [Model.Instance.replaceClock, Function.update_self] using hu),
    Model.Instance.pendingTime_replaceClock, Model.Instance.eraseClock_replaceClock]
  simp only [Model.Instance.replaceClock, Function.update_self]

/-- Candidate resampling derives the pending-execution integral. The test
premium erases the candidate clock by construction. -/
lemma lintegral_clockReachedPremium (π : Model.Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n)
    (P : Model.Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : ℝ × Model.World n Seed → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, clockReachedPremium π i g ω ∂P.worldLaw ν) =
      ∫⁻ ω, ∫⁻ t, if t ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i
        then g (t, Model.Instance.eraseClock i ω) else 0 ∂Model.Instance.uniformClock ∂P.worldLaw ν := by
  have hmp := P.replaceClock_measurePreserving ν i
  have hm := measurable_clockReachedPremium π hπ i g hg
  have hcomp : Measurable (fun z : Model.World n Seed × ℝ => clockReachedPremium π i g (Model.Instance.replaceClock i z)) :=
    hm.comp hmp.measurable
  rw [← hmp.lintegral_comp hm, lintegral_prod _ hcomp.aemeasurable]
  apply lintegral_congr
  intro ω
  apply lintegral_congr_ae
  filter_upwards [uniformClock_mem_open_unit] with t ht
  exact clockReachedPremium_replaceClock π i g (ω, t) ht.2.le

noncomputable def clockStoppedHazard (π : Model.Policy Seed n) (i : Fin n)
    (g : ℝ × Model.World n Seed → ℝ≥0∞) (q : Model.World n Seed × ℝ) : ℝ≥0∞ :=
  if q.2 ≤ π.stoppingTime q.1.2.2 Finset.univ q.1.1 q.1.2.1 ∧ q.2 < q.1.2.1 i
    then g (q.2, Model.Instance.eraseClock i q.1) / ENNReal.ofReal (1 - q.2) else 0

lemma measurable_clockStoppedHazard (π : Model.Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n)
    (g : ℝ × Model.World n Seed → ℝ≥0∞) (hg : Measurable g) : Measurable (clockStoppedHazard π i g) := by
  exact Measurable.ite ((measurableSet_le measurable_snd ((π.measurable_worldTime hπ Finset.univ).comp measurable_fst)).inter
    (measurableSet_lt measurable_snd ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))))
    ((hg.comp (measurable_snd.prodMk ((Model.Instance.measurable_eraseClock i).comp measurable_fst))).div
      (measurable_const.sub measurable_snd).ennreal_ofReal) measurable_const

omit [MeasurableSpace Seed] in
lemma clockStoppedHazard_replaceClock (π : Model.Policy Seed n) (i : Fin n)
    (g : ℝ × Model.World n Seed → ℝ≥0∞) (z : Model.World n Seed × ℝ) (t : ℝ) (ht : t ≤ 1) :
    clockStoppedHazard π i g (Model.Instance.replaceClock i z, t) =
      uniformHazardKernel (fun s => g (s, Model.Instance.eraseClock i z.1))
        (π.pendingTime z.1.2.2 z.1.1 z.1.2.1 i) (z.2, t) := by
  by_cases htu : t < z.2
  · have hsurvive := π.survival_iff_pending_of_not_arrived (Model.Instance.replaceClock i z).2.2
      (Model.Instance.replaceClock i z).1 (Model.Instance.replaceClock i z).2.1 i ht
      (show t ≤ (Model.Instance.replaceClock i z).2.1 i from by
        simpa only [Model.Instance.replaceClock, Function.update_self] using htu.le)
    rw [Model.Instance.pendingTime_replaceClock] at hsurvive
    unfold clockStoppedHazard uniformHazardKernel
    rw [Model.Instance.eraseClock_replaceClock]
    simp only [Model.Instance.replaceClock, Function.update_self, htu, and_true]
    exact ite_congr (propext hsurvive) (fun _ => rfl) (fun _ => rfl)
  · simp [clockStoppedHazard, uniformHazardKernel, Model.Instance.replaceClock, htu]

lemma lintegral_clockStoppedHazard (π : Model.Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n)
    (P : Model.Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : ℝ × Model.World n Seed → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∫⁻ t, clockStoppedHazard π i g (ω, t) ∂Model.Instance.uniformClock ∂P.worldLaw ν) =
      ∫⁻ ω, ∫⁻ t, if t ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i
        then g (t, Model.Instance.eraseClock i ω) else 0 ∂Model.Instance.uniformClock ∂P.worldLaw ν := by
  let f : Model.World n Seed → ℝ≥0∞ := fun ω =>
    ∫⁻ t, clockStoppedHazard π i g (ω, t) ∂Model.Instance.uniformClock
  have hm : Measurable f := (measurable_clockStoppedHazard π hπ i g hg).lintegral_prod_right'
  have hmp := P.replaceClock_measurePreserving ν i
  have hcomp : Measurable (fun z : Model.World n Seed × ℝ => f (Model.Instance.replaceClock i z)) := hm.comp hmp.measurable
  change (∫⁻ ω, f ω ∂P.worldLaw ν) = _
  rw [← hmp.lintegral_comp hm, lintegral_prod _ hcomp.aemeasurable]
  apply lintegral_congr
  intro ω
  calc
    _ = ∫⁻ u, ∫⁻ t, uniformHazardKernel (fun s => g (s, Model.Instance.eraseClock i ω))
        (π.pendingTime ω.2.2 ω.1 ω.2.1 i) (u, t) ∂Model.Instance.uniformClock ∂Model.Instance.uniformClock := by
      apply lintegral_congr
      intro u
      apply lintegral_congr_ae
      filter_upwards [uniformClock_mem_open_unit] with t ht
      exact clockStoppedHazard_replaceClock π i g (ω, u) t ht.2.le
    _ = _ := lintegral_uniform_hazard _ (hg.comp (measurable_id.prodMk measurable_const)) _

/-- Exact finite compensator. The full policy history, including observed zero
identities, is retained. Independence is derived by candidate replacement. -/
theorem finite_clock_compensator (π : Model.Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n)
    (P : Model.Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : ℝ × Model.World n Seed → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, clockReachedPremium π i g ω ∂P.worldLaw ν) =
      ∫⁻ ω, ∫⁻ t, clockStoppedHazard π i g (ω, t) ∂Model.Instance.uniformClock ∂P.worldLaw ν :=
  (lintegral_clockReachedPremium π hπ i P ν g hg).trans
    (lintegral_clockStoppedHazard π hπ i P ν g hg).symm

end ProphetSecretary.Probability
