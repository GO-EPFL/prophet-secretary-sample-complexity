import ProphetSecretary.Model.Jackpot
import ProphetSecretary.Model.Learner
import ProphetSecretary.Model.JackpotMoments
import ProphetSecretary.Reach.RareReach

/-!
# Hard-budget jackpot coupling

A full reservoir can be coupled before any adaptive requests. If none of the candidate's
potential draws receives a jackpot indicator, every request and observed sample agrees.
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped ENNReal BigOperators Classical

namespace ProphetSecretary.Probability

/-- Transforming one coordinate using fresh independent randomness preserves the
independent product law, with precisely that marginal replaced. -/
lemma measurePreserving_transformCoordinate {n : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Fin n → Measure A)
    [∀ j, IsProbabilityMeasure (μ j)] (ν : Measure B) [IsProbabilityMeasure ν]
    (i : Fin n) (targetLaw : Measure A) [IsProbabilityMeasure targetLaw] (f : B × A → A)
    (hf : MeasurePreserving f (ν.prod (μ i)) targetLaw) :
    MeasurePreserving (fun z : B × (Fin n → A) => Function.update z.2 i (f (z.1, z.2 i)))
      (ν.prod (Measure.pi μ)) (Measure.pi (Function.update μ i targetLaw)) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let μ' : Fin (n + 1) → Measure A := Function.update μ i targetLaw
    haveI : ∀ j, IsProbabilityMeasure (μ' j) := by
      intro j
      by_cases hj : j = i
      · subst j; simpa [μ'] using (inferInstance : IsProbabilityMeasure targetLaw)
      · simpa [μ', Function.update_of_ne hj] using (inferInstance : IsProbabilityMeasure (μ j))
    have hrest : (fun j : Fin n => μ' (i.succAbove j)) = fun j => μ (i.succAbove j) := by
      funext j
      exact Function.update_of_ne (Fin.succAbove_ne i j) _ _
    have h₁ := (MeasurePreserving.id ν).prod (measurePreserving_piFinSuccAbove μ i)
    have h₂ := (measurePreserving_prodAssoc ν (μ i) (Measure.pi (fun j : Fin n => μ (i.succAbove j)))).symm
      MeasurableEquiv.prodAssoc
    have h₃ := hf.prod (MeasurePreserving.id (Measure.pi (fun j : Fin n => μ (i.succAbove j))))
    have h₄ := (measurePreserving_piFinSuccAbove μ' i).symm (MeasurableEquiv.piFinSuccAbove (fun _ => A) i)
    change MeasurePreserving _ ((μ' i).prod (Measure.pi (fun j : Fin n => μ' (i.succAbove j)))) _ at h₄
    rw [hrest] at h₄
    simp only [μ', Function.update_self] at h₄
    have h := h₄.comp (h₃.comp (h₂.comp h₁))
    convert h using 1
    funext z j
    induction j using i.succAboveCases with
    | x => simp [MeasurableEquiv.piFinSuccAbove]; rfl
    | p j => simp [MeasurableEquiv.piFinSuccAbove]; rfl

open ProphetSecretary.Model

noncomputable def jackpotCoins (k : ℕ) (p : unitInterval) : Measure (Fin k → Bool) :=
  Measure.pi (fun _ => bernoulliMeasure true false p)

instance jackpotCoins_probability (k : ℕ) (p : unitInterval) : IsProbabilityMeasure (jackpotCoins k p) := by
  dsimp [jackpotCoins]
  infer_instance

/-- Perturb all potential draws of the candidate marginal, before any adaptive requests. -/
def perturbReservoir {n k : ℕ} (i : Fin n) (A : ℝ)
    (z : (Fin k → Bool) × Reservoir n k) : Reservoir n k :=
  Function.update z.2 i (fun j => realizeJackpot A (z.1 j, z.2 i j))

lemma perturbReservoir_eq_of_noJackpot {n k : ℕ} (i : Fin n) (A : ℝ)
    (z : (Fin k → Bool) × Reservoir n k) (hz : ∀ j, z.1 j = false) : perturbReservoir i A z = z.2 := by
  have he : (fun j => realizeJackpot A (z.1 j, z.2 i j)) = z.2 i := by
    funext j
    simp [realizeJackpot, hz j]
  simp [perturbReservoir, he]

lemma jackpotBlock_measurePreserving (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (k : ℕ) (p : unitInterval) (A : ℝ) :
    MeasurePreserving (fun z : (Fin k → Bool) × (Fin k → ℝ) => fun j => realizeJackpot A (z.1 j, z.2 j))
      ((jackpotCoins k p).prod (Measure.pi (fun _ : Fin k => μ)))
      (Measure.pi (fun _ : Fin k => jackpotLaw μ p A)) := by
  have hsplit := (measurePreserving_arrowProdEquivProdArrow Bool ℝ (Fin k)
    (fun _ => bernoulliMeasure true false p) (fun _ => μ)).symm
    (MeasurableEquiv.arrowProdEquivProdArrow Bool ℝ (Fin k))
  have hmap := measurePreserving_pi (fun _ : Fin k => (bernoulliMeasure true false p).prod μ)
    (fun _ : Fin k => jackpotLaw μ p A) (fun _ => realizeJackpot_measurePreserving μ p A)
  exact hmap.comp hsplit

lemma perturbReservoir_measurePreserving {n : ℕ} (P : Instance n) (k : ℕ) (i : Fin n)
    (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) :
    MeasurePreserving (perturbReservoir i A) ((jackpotCoins k p).prod (P.reservoirLaw k))
      ((P.jackpot i p A hA).reservoirLaw k) := by
  have h := measurePreserving_transformCoordinate (fun j => Measure.pi (fun _ : Fin k => P.law j))
    (jackpotCoins k p) i (Measure.pi (fun _ : Fin k => jackpotLaw (P.law i) p A))
    (fun z : (Fin k → Bool) × (Fin k → ℝ) => fun j => realizeJackpot A (z.1 j, z.2 j))
    (jackpotBlock_measurePreserving (P.law i) k p A)
  have he : (Function.update (fun j => Measure.pi (fun _ : Fin k => P.law j)) i
      (Measure.pi (fun _ : Fin k => jackpotLaw (P.law i) p A))) =
      (fun j => Measure.pi (fun _ : Fin k => (P.jackpot i p A hA).law j)) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [Instance.jackpot]
    · simp [Instance.jackpot, Function.update_of_ne hj]
  rw [he] at h
  exact h

/-- At least one of the candidate's `k` potential training draws is a jackpot. -/
def badJackpotCoins {k : ℕ} (b : Fin k → Bool) : Prop := ∃ j, b j = true

lemma measurableSet_badJackpotCoins (k : ℕ) :
    MeasurableSet {b : Fin k → Bool | badJackpotCoins b} := by
  simp only [badJackpotCoins, Set.setOf_exists]
  exact MeasurableSet.iUnion fun j => measurableSet_eq_fun (measurable_pi_apply j) measurable_const

lemma jackpotCoins_coordinate_probability (k : ℕ) (p : unitInterval) (j : Fin k) :
    (jackpotCoins k p).real {b | b j = true} = (p : ℝ) := by
  have hp := measurePreserving_eval (fun _ : Fin k => bernoulliMeasure true false p) j
  change MeasurePreserving (fun b : Fin k → Bool => b j) (jackpotCoins k p) (bernoulliMeasure true false p) at hp
  calc
    _ = ((jackpotCoins k p).map (fun b => b j)).real {true} := by
      rw [map_measureReal_apply (measurable_pi_apply j) (measurableSet_singleton true)]
      rfl
    _ = (bernoulliMeasure true false p).real {true} := by rw [hp.map_eq]
    _ = p := bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton true) (by simp) (by simp)

lemma badJackpotCoins_probability_le (k : ℕ) (p : unitInterval) :
    (jackpotCoins k p).real {b | badJackpotCoins b} ≤ k * (p : ℝ) := by
  have he : {b : Fin k → Bool | badJackpotCoins b} = ⋃ j : Fin k, {b | b j = true} := by
    ext b
    simp [badJackpotCoins]
  rw [he]
  calc
    _ ≤ ∑ j : Fin k, (jackpotCoins k p).real {b | b j = true} := measureReal_iUnion_fintype_le _
    _ = k * (p : ℝ) := by simp only [jackpotCoins_coordinate_probability, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

variable {n k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- Common base reservoir and auxiliary seed, with `k` independent jackpot coins. -/
noncomputable def coupledTrainingLaw (P : Instance n) (p : unitInterval) (ν : Measure Seed) :
    Measure ((Fin k → Bool) × (Reservoir n k × Seed)) :=
  (jackpotCoins k p).prod ((P.reservoirLaw k).prod ν)

instance coupledTrainingLaw_probability (P : Instance n) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (coupledTrainingLaw (k := k) P p ν) := by
  dsimp [coupledTrainingLaw]
  infer_instance

def perturbTraining (i : Fin n) (A : ℝ)
    (z : (Fin k → Bool) × (Reservoir n k × Seed)) : Reservoir n k × Seed :=
  (perturbReservoir i A (z.1, z.2.1), z.2.2)

lemma perturbTraining_measurePreserving (P : Instance n) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (A : ℝ) (hA : 0 ≤ A) :
    MeasurePreserving (perturbTraining i A) (coupledTrainingLaw (k := k) P p ν)
      (((P.jackpot i p A hA).reservoirLaw k).prod ν) := by
  have h₁ := (measurePreserving_prodAssoc (jackpotCoins k p) (P.reservoirLaw k) ν).symm
    MeasurableEquiv.prodAssoc
  exact ((perturbReservoir_measurePreserving P k i p A hA).prod (MeasurePreserving.id ν)).comp h₁

lemma baseTraining_measurePreserving (P : Instance n) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    MeasurePreserving (fun z : (Fin k → Bool) × (Reservoir n k × Seed) => z.2)
      (coupledTrainingLaw P p ν) ((P.reservoirLaw k).prod ν) :=
  measurePreserving_snd

omit [MeasurableSpace Seed] in
lemma perturbTraining_eq_of_noJackpot (i : Fin n) (A : ℝ)
    (z : (Fin k → Bool) × (Reservoir n k × Seed)) (hz : ¬badJackpotCoins z.1) :
    perturbTraining i A z = z.2 := by
  apply Prod.ext
  · exact perturbReservoir_eq_of_noJackpot i A _ (fun j => by
      have h : z.1 j ≠ true := fun hj => hz ⟨j, hj⟩
      cases hb : z.1 j <;> simp_all)
  · rfl

/-- Any deterministic training output, including an entire induced online policy,
agrees except on an event of probability at most `kp`. This covers adaptive requests. -/
lemma coupledTraining_disagreement_le (P : Instance n) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (A : ℝ) {B : Type*}
    (f : Reservoir n k × Seed → B) :
    (coupledTrainingLaw P p ν).real {z | f (perturbTraining i A z) ≠ f z.2} ≤ k * (p : ℝ) := by
  have hsub : {z : (Fin k → Bool) × (Reservoir n k × Seed) | f (perturbTraining i A z) ≠ f z.2} ⊆
      {z | badJackpotCoins z.1} := by
    intro z hz
    by_contra hno
    exact hz (congrArg f (perturbTraining_eq_of_noJackpot i A z hno))
  calc
    _ ≤ (coupledTrainingLaw P p ν).real {z | badJackpotCoins z.1} := measureReal_mono hsub
    _ = (jackpotCoins k p).real {b | badJackpotCoins b} := by
      have hp : MeasurePreserving (fun z : (Fin k → Bool) × (Reservoir n k × Seed) => z.1)
          (coupledTrainingLaw P p ν) (jackpotCoins k p) := measurePreserving_fst
      rw [← hp.map_eq, map_measureReal_apply hp.measurable (measurableSet_badJackpotCoins k)]
      rfl
    _ ≤ k * (p : ℝ) := badJackpotCoins_probability_le k p

/-- Project a coupled training experiment to its unchanged reservoir and seed. -/
def baseCoupledWorld (ω : World n ((Fin k → Bool) × (Reservoir n k × Seed))) :
    World n (Reservoir n k × Seed) := (ω.1, (ω.2.1, ω.2.2.2))

def perturbedCoupledWorld (i : Fin n) (A : ℝ)
    (ω : World n ((Fin k → Bool) × (Reservoir n k × Seed))) : World n (Reservoir n k × Seed) :=
  (ω.1, (ω.2.1, perturbTraining i A ω.2.2))

lemma baseCoupledWorld_measurePreserving (P : Instance n) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    MeasurePreserving (baseCoupledWorld (n := n) (k := k)) (P.worldLaw (coupledTrainingLaw P p ν))
      (P.worldLaw ((P.reservoirLaw k).prod ν)) :=
  (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.clocksLaw n)).prod
    (baseTraining_measurePreserving P p ν))

lemma perturbedCoupledWorld_measurePreserving (P : Instance n) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (A : ℝ) (hA : 0 ≤ A) :
    MeasurePreserving (perturbedCoupledWorld i A) (P.worldLaw (coupledTrainingLaw P p ν))
      (P.worldLaw (((P.jackpot i p A hA).reservoirLaw k).prod ν)) :=
  (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.clocksLaw n)).prod
    (perturbTraining_measurePreserving P p ν i A hA))

lemma coupledWorld_badProbability_le (P : Instance n) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (P.worldLaw (coupledTrainingLaw (k := k) P p ν)).real
      {ω | badJackpotCoins ω.2.2.1} ≤ k * (p : ℝ) := by
  have hp : MeasurePreserving
      (fun ω : World n ((Fin k → Bool) × (Reservoir n k × Seed)) => ω.2.2.1)
      (P.worldLaw (coupledTrainingLaw P p ν)) (jackpotCoins k p) :=
    measurePreserving_fst.comp (measurePreserving_snd.comp measurePreserving_snd)
  calc
    _ = (jackpotCoins k p).real {b | badJackpotCoins b} := by
      rw [← hp.map_eq, map_measureReal_apply hp.measurable (measurableSet_badJackpotCoins k)]
      rfl
    _ ≤ k * (p : ℝ) := badJackpotCoins_probability_le k p

/-- Changing the training marginal changes reach by at most the hard-budget coupling
error. Online values retain the base law on both sides of this comparison. -/
lemma training_reachProbability_le (P : Instance n) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (A : ℝ) (hA : 0 ≤ A)
    (π : Policy (Reservoir n k × Seed) n) (hπ : π.IsMeasurable) :
    π.reachProbability P (((P.jackpot i p A hA).reservoirLaw k).prod ν) i ≤
      π.reachProbability P ((P.reservoirLaw k).prod ν) i + k * (p : ℝ) := by
  let C := P.worldLaw (coupledTrainingLaw (k := k) P p ν)
  let E := {ω : World n (Reservoir n k × Seed) | π.Reaches ω.2.2 ω.1 ω.2.1 i}
  have hE : MeasurableSet E := π.measurableSet_reaches hπ
    (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hsub : perturbedCoupledWorld i A ⁻¹' E ⊆ baseCoupledWorld ⁻¹' E ∪
      {ω | badJackpotCoins ω.2.2.1} := by
    intro ω hω
    by_cases hb : badJackpotCoins ω.2.2.1
    · exact Or.inr hb
    · apply Or.inl
      have he := perturbTraining_eq_of_noJackpot i A ω.2.2 hb
      simpa only [Set.mem_preimage, E, perturbedCoupledWorld, baseCoupledWorld, he] using hω
  have hp := perturbedCoupledWorld_measurePreserving (k := k) P p ν i A hA
  have hb := baseCoupledWorld_measurePreserving (k := k) P p ν
  change (P.worldLaw (((P.jackpot i p A hA).reservoirLaw k).prod ν)).real E ≤ _
  rw [← hp.map_eq, map_measureReal_apply hp.measurable hE]
  calc
    C.real (perturbedCoupledWorld i A ⁻¹' E) ≤
        C.real (baseCoupledWorld ⁻¹' E ∪ {ω | badJackpotCoins ω.2.2.1}) := measureReal_mono hsub
    _ ≤ C.real (baseCoupledWorld ⁻¹' E) + C.real {ω | badJackpotCoins ω.2.2.1} := measureReal_union_le _ _
    _ ≤ C.real (baseCoupledWorld ⁻¹' E) + k * (p : ℝ) :=
      add_le_add le_rfl (coupledWorld_badProbability_le (k := k) P p ν)
    _ = π.reachProbability P ((P.reservoirLaw k).prod ν) i + k * (p : ℝ) := by
      rw [← map_measureReal_apply hb.measurable hE, hb.map_eq]
      rfl

/-- Erase only the candidate value; every arrival time remains visible as before. -/
def eraseValueWorld {n : ℕ} {Seed : Type*} (i : Fin n) (ω : World n Seed) : World n Seed :=
  (eraseCoordinate i 0 ω.1, ω.2)

lemma erasedValueWorld_value_independent {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    IndepFun (eraseValueWorld i) (fun ω : World n Seed => ω.1 i) (P.worldLaw ν) := by
  exact indepFun_with_seed (measurable_eraseCoordinate i 0) (measurable_pi_apply i)
    (eraseCoordinate_independent P.law i 0)

/-- Reach is independent of the candidate's own value. Functional invariance is proved
from online execution, and product-law independence is then derived by value erasure. -/
lemma reachIndicator_value_independent {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n)
    (π : Policy Seed n) (hπ : π.IsMeasurable) :
    IndepFun (fun ω : World n Seed => if π.Reaches ω.2.2 ω.1 ω.2.1 i then (1 : ℝ) else 0)
      (fun ω => ω.1 i) (P.worldLaw ν) := by
  let f : World n Seed → ℝ := fun ω => if π.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0
  have hf : Measurable f := Measurable.ite (π.measurableSet_reaches hπ
    (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)
    measurable_const measurable_const
  have he : (f ∘ eraseValueWorld i) =ᵐ[P.worldLaw ν] f := by
    filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hω
    change (if π.Reaches ω.2.2 (Function.update ω.1 i 0) ω.2.1 i then (1 : ℝ) else 0) = _
    rw [π.reaches_update_value _ _ _ i 0 (hω i).2]
  exact ((erasedValueWorld_value_independent P ν i).comp hf measurable_id).congr he (Filter.EventuallyEq.rfl)

/-- Couple the online candidate with one independent jackpot coin, retaining its
original value and every other part of the complete world. -/
def perturbOnline {n : ℕ} {Seed : Type*} (i : Fin n) (A : ℝ) (z : Bool × World n Seed) : World n Seed :=
  (Function.update z.2.1 i (realizeJackpot A (z.1, z.2.1 i)), z.2.2)

lemma perturbOnline_measurePreserving {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (p : unitInterval) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (i : Fin n) (A : ℝ) (hA : 0 ≤ A) :
    MeasurePreserving (perturbOnline i A) ((bernoulliMeasure true false p).prod (P.worldLaw ν))
      ((P.jackpot i p A hA).worldLaw ν) := by
  have h₁ := (measurePreserving_prodAssoc (bernoulliMeasure true false p) P.valuesLaw
    ((Instance.clocksLaw n).prod ν)).symm MeasurableEquiv.prodAssoc
  have hx := measurePreserving_transformCoordinate P.law (bernoulliMeasure true false p)
    i (jackpotLaw (P.law i) p A) (realizeJackpot A) (realizeJackpot_measurePreserving (P.law i) p A)
  exact (hx.prod (MeasurePreserving.id ((Instance.clocksLaw n).prod ν))).comp h₁

lemma expectedReward_jackpot_le {n : ℕ} (π : RandomizedPolicy n) (P : Instance n) (i : Fin n)
    (p : unitInterval) {H A : ℝ} (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    π.expectedReward (P.jackpot i p A hA) ≤
      H + (p : ℝ) * A * π.rule.reachProbability P π.seedLaw i := by
  let W := (bernoulliMeasure true false p).prod (P.worldLaw π.seedLaw)
  let E : Set π.World := {ω | π.rule.Reaches ω.2.2 ω.1 ω.2.1 i}
  let B : Set (Bool × π.World) := {true} ×ˢ E
  have hE : MeasurableSet E := π.rule.measurableSet_reaches π.measurable_rule
    (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hB : MeasurableSet B := (measurableSet_singleton true).prod hE
  have hI : Integrable (B.indicator (fun _ => (1 : ℝ))) W :=
    (integrable_const 1).indicator hB
  have hmax := P.jackpot_integrable_maximum (P.integrable_maximum_of_bounded hbound) i p hA
  have hp := perturbOnline_measurePreserving P p π.seedLaw i A hA
  have heq := integral_map (μ := W) hp.measurable.aemeasurable π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at heq
  have hxb : ∀ᵐ x ∂P.valuesLaw, ∀ j, x j ≤ H := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval P.law j).quasiMeasurePreserving.ae (hbound j)
  have hx : ∀ᵐ z : Bool × π.World ∂W, ∀ j, z.2.1 j ≤ H :=
    (measurePreserving_fst.comp measurePreserving_snd).quasiMeasurePreserving.ae hxb
  have hu : ∀ᵐ z : Bool × π.World ∂W, ∀ j, z.2.2.1 j ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_snd : MeasurePreserving (fun z : Bool × π.World => z.2) W
      (P.worldLaw π.seedLaw)).quasiMeasurePreserving.ae (P.world_clocks_mem_unitInterval π.seedLaw)
  change ∫ ω, π.realizedReward ω ∂(P.jackpot i p A hA).worldLaw π.seedLaw ≤ _
  rw [heq]
  calc
    _ ≤ ∫ z : Bool × π.World, H + A * B.indicator (fun _ => (1 : ℝ)) z ∂W := by
      apply integral_mono_ae (hp.integrable_comp_of_integrable (π.integrable_realizedReward _ hmax))
        ((integrable_const H).add (hI.const_mul A))
      filter_upwards [hx, hu] with z hz hzu
      have h := π.rule.reward_le_jackpot_reach z.2.2.2 z.2.1 z.2.2.1 i z.1 hH hA hz (hzu i).2
      simpa only [RandomizedPolicy.realizedReward, perturbOnline, realizeJackpot,
        B, E, Set.indicator, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq, Pi.one_apply,
        Function.comp_apply, Pi.add_apply] using h
    _ = H + A * W.real B := by
      rw [integral_add (integrable_const H) (hI.const_mul A), integral_const_mul,
        integral_indicator_const 1 hB]
      simp
    _ = H + (p : ℝ) * A * π.rule.reachProbability P π.seedLaw i := by
      dsimp [B, W]
      rw [measureReal_prod_prod, bernoulliMeasure_real_apply_of_mem_of_notMem p
        (measurableSet_singleton true) (by simp) (by simp)]
      change H + A * ((p : ℝ) * (P.worldLaw π.seedLaw).real E) =
        H + (p : ℝ) * A * (P.worldLaw π.seedLaw).real E
      ring

/-- Final quantitative coupling estimate for an arbitrary measurable adaptive learner. -/
lemma learner_expectedReward_jackpot_le {n k : ℕ} (L : Learner n k) (P : Instance n) (i : Fin n)
    (p : unitInterval) {H A : ℝ} (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    L.expectedReward (P.jackpot i p A hA) ≤
      H + (p : ℝ) * A * (L.reachProbability P i + k * (p : ℝ)) := by
  have honline := expectedReward_jackpot_le (L.randomizedPolicy (P.jackpot i p A hA)) P i p hH hA hbound
  have htrain := training_reachProbability_le P p L.seedLaw i A hA L.policy L.policy_isMeasurable
  apply honline.trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left htrain (mul_nonneg p.2.1 hA)

end ProphetSecretary.Probability
