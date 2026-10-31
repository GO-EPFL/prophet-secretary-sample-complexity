import ProphetSecretary.Model.Instance
import Mathlib.Logic.Function.Basic

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace ProphetSecretary.Model

/-- Pull independence back through an exactly measure-preserving sampling map. -/
lemma indepFun_pullback {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B] {μ : Measure Ω} {ν : Measure Ω'}
    {T : Ω → Ω'} (hT : MeasurePreserving T μ ν) {f : Ω' → A} {g : Ω' → B}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g ν) :
    IndepFun (f ∘ T) (g ∘ T) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  change μ (T ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t)) = μ (T ⁻¹' (f ⁻¹' s)) * μ (T ⁻¹' (g ⁻¹' t))
  rw [hT.measure_preimage ((hf hs).inter (hg ht)).nullMeasurableSet, hT.measure_preimage (hf hs).nullMeasurableSet,
    hT.measure_preimage (hg ht).nullMeasurableSet]
  exact h.measure_inter_preimage_eq_mul s t hs ht

/-- Adding an independent random seed to one side preserves independence. -/
lemma indepFun_with_seed {Ω A B Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Seed] {μ : Measure Ω} {ν : Measure Seed}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : Ω → A} {g : Ω → B}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g μ) :
    IndepFun (fun z : Ω × Seed => (f z.1, z.2)) (fun z => g z.1) (μ.prod ν) := by
  let mf := μ.map f
  let mg := μ.map g
  have hmf : IsProbabilityMeasure mf := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hmg : IsProbabilityMeasure mg := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hp : MeasurePreserving (fun x => (f x, g x)) μ (mf.prod mg) :=
    ⟨hf.prodMk hg, h.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable⟩
  have h₁ := hp.prod (MeasurePreserving.id ν)
  have h₂ := measurePreserving_prodAssoc mf mg ν
  have h₃ := (MeasurePreserving.id mf).prod (Measure.measurePreserving_swap (μ := mg) (ν := ν))
  have h₄ := (measurePreserving_prodAssoc mf ν mg).symm MeasurableEquiv.prodAssoc
  have htotal := h₄.comp (h₃.comp (h₂.comp h₁))
  have hh := indepFun_pullback htotal measurable_fst measurable_snd
    (indepFun_prod (μ := mf.prod ν) (ν := mg) measurable_id measurable_id)
  exact hh

section Erasure

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]

/-- Erasing coordinate `i` removes its value, rather than declaring independence of
an execution that might still inspect that value. -/
def eraseCoordinate (i : ι) (a₀ : A) (x : ι → A) : ι → A := Function.update x i a₀

omit [Fintype ι] in
lemma measurable_eraseCoordinate (i : ι) (a₀ : A) : Measurable (eraseCoordinate i a₀) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j = i
  · subst j
    simp only [eraseCoordinate, Function.update_self]
    exact measurable_const
  · simpa [eraseCoordinate, Function.update_of_ne h] using (measurable_pi_apply j)

lemma eraseCoordinate_independent (i : ι) (a₀ : A) :
    IndepFun (eraseCoordinate i a₀) (fun x : ι → A => x i) (Measure.pi μ) := by
  have h := (iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun_finset
    (Finset.univ.erase i) {i} (by simp) (fun j => measurable_pi_apply j)
  let restore : ((j : Finset.univ.erase i) → A) → (ι → A) := fun x j =>
    if hj : j = i then a₀ else x ⟨j, by simp [hj]⟩
  have hrestore : Measurable restore := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j = i
    · simp only [restore, hj, dite_true]
      exact measurable_const
    · simpa [restore, hj] using (measurable_pi_apply (⟨j, by simp [hj]⟩ : Finset.univ.erase i))
  have hh := h.comp hrestore (measurable_pi_apply (⟨i, by simp⟩ : ({i} : Finset ι)))
  convert hh using 1
  · funext x j
    by_cases hj : j = i
    · subst j
      simp [eraseCoordinate, restore]
    · simp [eraseCoordinate, restore, hj]
  · rfl

/-- Every measurable functional of the erased vector is independent of the omitted
coordinate. No independence assumption about the functional is required. -/
lemma erasedFunctional_independent {B : Type*} [MeasurableSpace B]
    (i : ι) (a₀ : A) (f : (ι → A) → B) (hf : Measurable f) :
    IndepFun (fun x => f (eraseCoordinate i a₀ x)) (fun x : ι → A => x i) (Measure.pi μ) := by
  exact (eraseCoordinate_independent μ i a₀).comp hf measurable_id

end Erasure

namespace Instance

variable {n : ℕ} (P : Instance n)

lemma values_independent : iIndepFun (fun (i : Fin n) (x : Fin n → ℝ) => x i) P.valuesLaw := by
  exact iIndepFun_pi (fun _ => aemeasurable_id)

lemma clocks_independent : iIndepFun (fun (i : Fin n) (u : Fin n → ℝ) => u i) (clocksLaw n) := by
  exact iIndepFun_pi (fun _ => aemeasurable_id)

lemma values_clocksSeed_independent {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IndepFun (fun ω : (Fin n → ℝ) × ((Fin n → ℝ) × Seed) => ω.1)
      (fun ω => ω.2) (P.worldLaw ν) := by
  exact indepFun_prod measurable_id measurable_id

lemma clocks_seed_independent {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IndepFun (fun ω : (Fin n → ℝ) × Seed => ω.1) (fun ω => ω.2)
      ((clocksLaw n).prod ν) := by
  exact indepFun_prod measurable_id measurable_id

/-- Removing a candidate from the analytical complete world erases both its value
and its clock while retaining the independent policy seed. -/
def eraseWorld {Seed : Type*} (i : Fin n)
    (ω : (Fin n → ℝ) × ((Fin n → ℝ) × Seed)) :
    (Fin n → ℝ) × ((Fin n → ℝ) × Seed) :=
  (eraseCoordinate i 0 ω.1, (eraseCoordinate i 0 ω.2.1, ω.2.2))

lemma measurable_eraseWorld {Seed : Type*} [MeasurableSpace Seed] (i : Fin n) :
    Measurable (@eraseWorld n Seed i) := by
  exact ((measurable_eraseCoordinate i 0).comp measurable_fst).prodMk
    (((measurable_eraseCoordinate i 0).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

/-- The erased complete world, including all other offers, all other clocks and the
policy seed, is independent of the omitted candidate's value and arrival time. -/
lemma erasedWorld_candidate_independent {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    IndepFun (eraseWorld i)
      (fun ω : (Fin n → ℝ) × ((Fin n → ℝ) × Seed) => (ω.1 i, ω.2.1 i))
      (P.worldLaw ν) := by
  let pairLaw : Fin n → Measure (ℝ × ℝ) := fun j => (P.law j).prod uniformClock
  have he := eraseCoordinate_independent pairLaw i (0, 0)
  have hseed := indepFun_with_seed (measurable_eraseCoordinate i (0, 0))
    (measurable_pi_apply i) he (ν := ν)
  let pack : ((Fin n → ℝ × ℝ) × Seed) → ((Fin n → ℝ) × ((Fin n → ℝ) × Seed)) :=
    fun z => ((fun j => (z.1 j).1), ((fun j => (z.1 j).2), z.2))
  have hpack : Measurable pack := by fun_prop
  have hraw := hseed.comp hpack measurable_id
  have hsplit := (measurePreserving_prodAssoc P.valuesLaw (clocksLaw n) ν).symm
    MeasurableEquiv.prodAssoc
  have hpair := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) P.law
    (fun _ => uniformClock)).symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
  have hT := (hpair.prod (MeasurePreserving.id ν)).comp hsplit
  have hh := indepFun_pullback hT
    (hpack.comp ((measurable_eraseCoordinate i (0, 0)).comp measurable_fst |>.prodMk measurable_snd))
    ((measurable_pi_apply i).comp measurable_fst) hraw
  convert hh using 1
  · funext ω
    apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j; simp [eraseWorld, eraseCoordinate, pack]
      · simp [eraseWorld, eraseCoordinate, pack, Function.update_of_ne hj]
        rfl
    · apply Prod.ext
      · funext j
        by_cases hj : j = i
        · subst j; simp [eraseWorld, eraseCoordinate, pack]
        · simp [eraseWorld, eraseCoordinate, pack, Function.update_of_ne hj]
          rfl
      · rfl
  · rfl
  · rfl

/-- A measurable execution that is unchanged by erasing a candidate is independent
of that candidate. The invariance must be established from its execution rules. -/
lemma erasedFunctional_candidate_independent {Seed B : Type*} [MeasurableSpace Seed]
    [MeasurableSpace B] (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n)
    (f : ((Fin n → ℝ) × ((Fin n → ℝ) × Seed)) → B) (hf : Measurable f)
    (hinv : ∀ ω, f (eraseWorld i ω) = f ω) :
    IndepFun f (fun ω => (ω.1 i, ω.2.1 i)) (P.worldLaw ν) := by
  have h := (P.erasedWorld_candidate_independent ν i).comp hf measurable_id
  convert h using 1
  · funext ω
    exact (hinv ω).symm
  · rfl

lemma clocks_mem_unitInterval : ∀ᵐ u ∂clocksLaw n, ∀ i, u i ∈ Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  apply (measurePreserving_eval (fun _ : Fin n => uniformClock) i).quasiMeasurePreserving.ae
  exact ae_restrict_mem measurableSet_Icc

instance uniformClock_nullSingleton : NullSingletonClass uniformClock := by
  dsimp [uniformClock]
  infer_instance

lemma clocks_pair_ne (i j : Fin n) (hij : i ≠ j) :
    ∀ᵐ u ∂clocksLaw n, u i ≠ u j := by
  have hm := (clocks_independent (n := n)).indepFun hij |>.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  have hei := (measurePreserving_eval (fun _ : Fin n => uniformClock) i).map_eq
  have hej := (measurePreserving_eval (fun _ : Fin n => uniformClock) j).map_eq
  change (clocksLaw n).map (fun u => (u i, u j)) =
    ((clocksLaw n).map (fun u => u i)).prod ((clocksLaw n).map (fun u => u j)) at hm
  change (clocksLaw n).map (fun u => u i) = uniformClock at hei
  change (clocksLaw n).map (fun u => u j) = uniformClock at hej
  rw [hei, hej] at hm
  have hp : MeasurePreserving (fun u : Fin n → ℝ => (u i, u j)) (clocksLaw n)
      (uniformClock.prod uniformClock) := ⟨by fun_prop, hm⟩
  have hz : ∀ᵐ z ∂uniformClock.prod uniformClock, z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact Filter.Eventually.of_forall fun x => (uniformClock.ae_ne x).mono fun _ h => Ne.symm h
  exact hp.quasiMeasurePreserving.ae hz

/-- Independent continuous clocks are tie-free almost surely. -/
lemma clocks_pairwise_distinct : ∀ᵐ u ∂clocksLaw n, Function.Injective u := by
  change ∀ᵐ u ∂clocksLaw n, ∀ i j, u i = u j → i = j
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ => hij
  · filter_upwards [clocks_pair_ne i j hij] with u hu
    exact fun heq => False.elim (hu heq)

end Instance
end ProphetSecretary.Model
