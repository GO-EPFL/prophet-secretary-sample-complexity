import ProphetSecretary.Model.Independence
import ProphetSecretary.Model.Continuation
import ProphetSecretary.Model.Restriction

/-!
# Fresh blocks and observable prefixes

Erasing a block removes both values and normalized clocks at those identities. The
erased world, including independent policy randomness, is independent of the fresh
block. This is derived from the finite product measure, not assumed of a prefix.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

section Coordinates

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

def eraseCoordinates (A : Finset ι) (e₀ : E) (x : ι → E) : ι → E :=
  fun j => if j ∈ A then e₀ else x j

omit [Fintype ι] in
lemma measurable_eraseCoordinates (A : Finset ι) (e₀ : E) : Measurable (eraseCoordinates A e₀) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j ∈ A
  · simpa only [eraseCoordinates, if_pos hj] using (measurable_const : Measurable (fun _ : ι → E => e₀))
  · simpa only [eraseCoordinates, if_neg hj] using (measurable_pi_apply j)

lemma eraseCoordinates_independent (μ : ι → Measure E) [∀ j, IsProbabilityMeasure (μ j)]
    (A : Finset ι) (e₀ : E) :
    IndepFun (eraseCoordinates A e₀) (fun x : ι → E => fun j : A => x j) (Measure.pi μ) := by
  let D : Finset ι := Finset.univ \ A
  have hdis : Disjoint D A := Finset.disjoint_left.mpr (by
    intro j hj hA
    exact (Finset.mem_sdiff.mp hj).2 hA)
  have h := (iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun_finset
    D A hdis (fun j => measurable_pi_apply j)
  let restore : ((j : D) → E) → (ι → E) :=
    fun x j => if hj : j ∈ A then e₀ else x ⟨j, by simp [D, hj]⟩
  have hm : Measurable restore := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j ∈ A
    · simp only [restore, dif_pos hj]
      exact measurable_const
    · simpa only [restore, dif_neg hj] using
        (measurable_pi_apply (⟨j, by simp [D, hj]⟩ : D))
  have hh := h.comp hm measurable_id
  convert hh using 1
  · funext x j
    by_cases hj : j ∈ A <;> simp [eraseCoordinates, restore, hj]
  · rfl

end Coordinates

variable {n : ℕ} {Seed : Type*}

def eraseSetWorld (A : Finset (Fin n)) (ω : World n Seed) : World n Seed :=
  (eraseCoordinates A 0 ω.1, (eraseCoordinates A 0 ω.2.1, ω.2.2))

def freshWorld (A : Finset (Fin n)) (ω : World n Seed) : World A.card Unit :=
  (ω.1 ∘ stateEmbedding A, (ω.2.1 ∘ stateEmbedding A, ()))

variable [MeasurableSpace Seed]

lemma measurable_eraseSetWorld (A : Finset (Fin n)) : Measurable (@eraseSetWorld n Seed A) := by
  exact ((measurable_eraseCoordinates A 0).comp measurable_fst).prodMk
    (((measurable_eraseCoordinates A 0).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

lemma measurable_freshWorld (A : Finset (Fin n)) : Measurable (@freshWorld n Seed A) := by
  fun_prop [freshWorld]

namespace Instance

lemma erasedWorld_freshWorld_independent (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Finset (Fin n)) : IndepFun (eraseSetWorld A) (freshWorld A) (P.worldLaw ν) := by
  let pairLaw : Fin n → Measure (ℝ × ℝ) := fun j => (P.law j).prod uniformClock
  have h := eraseCoordinates_independent pairLaw A (0, 0)
  have htuple : Measurable (fun x : Fin n → ℝ × ℝ => fun j : A => x j) := by fun_prop
  have hseed := indepFun_with_seed (measurable_eraseCoordinates A (0, 0)) htuple h (ν := ν)
  let pack : ((Fin n → ℝ × ℝ) × Seed) → World n Seed :=
    fun z => ((fun j => (z.1 j).1), ((fun j => (z.1 j).2), z.2))
  let future : ((j : A) → ℝ × ℝ) → World A.card Unit := fun z =>
    ((fun j => (z ⟨stateEmbedding A j, A.orderEmbOfFin_mem rfl j⟩).1),
      ((fun j => (z ⟨stateEmbedding A j, A.orderEmbOfFin_mem rfl j⟩).2), ()))
  have hpack : Measurable pack := by fun_prop
  have hfuture : Measurable future := by fun_prop
  have hraw := hseed.comp hpack hfuture
  have hsplit := (measurePreserving_prodAssoc P.valuesLaw (clocksLaw n) ν).symm MeasurableEquiv.prodAssoc
  have hpair := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) P.law (fun _ => uniformClock)).symm
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
  have hT := (hpair.prod (MeasurePreserving.id ν)).comp hsplit
  have hproj : Measurable (fun z : (Fin n → ℝ × ℝ) × Seed => fun j : A => z.1 j) := by fun_prop
  have hh := indepFun_pullback hT
    (hpack.comp (((measurable_eraseCoordinates A (0, 0)).comp measurable_fst).prodMk measurable_snd))
    (hfuture.comp hproj) hraw
  convert hh using 1
  · funext ω
    apply Prod.ext
    · funext j
      by_cases hj : j ∈ A <;> simp [eraseSetWorld, eraseCoordinates, pack, hj]
      rfl
    · apply Prod.ext
      · funext j
        by_cases hj : j ∈ A <;> simp [eraseSetWorld, eraseCoordinates, pack, hj]
        rfl
      · rfl
  · funext ω
    apply Prod.ext
    · funext j; rfl
    · apply Prod.ext
      · funext j; rfl
      · rfl
  · rfl

lemma freshWorld_measurePreserving (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Finset (Fin n)) :
    MeasurePreserving (freshWorld A) (P.worldLaw ν) ((P.restrictTo A).worldLaw (Measure.dirac ())) := by
  let Q := P.restrictTo A
  have hs := (measurePreserving_prodAssoc P.valuesLaw (clocksLaw n) ν).symm MeasurableEquiv.prodAssoc
  have hpair : MeasurePreserving (fun ω : World n Seed => (ω.1, ω.2.1))
      (P.worldLaw ν) (P.valuesLaw.prod (clocksLaw n)) := measurePreserving_fst.comp hs
  have hproj := (P.restrictValues_measurePreserving (stateEmbedding A)).prod
    (restrictClocks_measurePreserving (stateEmbedding A))
  have hunit : MeasurePreserving (fun z : (Fin A.card → ℝ) × (Fin A.card → ℝ) => (z, ()))
      (Q.valuesLaw.prod (clocksLaw A.card)) ((Q.valuesLaw.prod (clocksLaw A.card)).prod (Measure.dirac ())) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.prod_dirac]
  have hassoc := measurePreserving_prodAssoc Q.valuesLaw (clocksLaw A.card) (Measure.dirac ())
  exact hassoc.comp (hunit.comp (hproj.comp hpair))

end Instance
end ProphetSecretary.Model
