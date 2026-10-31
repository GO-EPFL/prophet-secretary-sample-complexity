import ProphetSecretary.Model.RankPolicy
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable rank histories and the clock-to-rank adapter

The absent/present observation space has the usual disjoint-union σ-algebra.
Measurability of the adapter is proved from the original callback; no policy
class is restricted to finite-support or Markov decision rules.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

def rankObservationCode : Option (Fin n × ℝ) → Unit ⊕ (Fin n × ℝ)
  | none => Sum.inl ()
  | some z => Sum.inr z

instance rankObservationMeasurableSpace : MeasurableSpace (Option (Fin n × ℝ)) :=
  MeasurableSpace.comap rankObservationCode inferInstance

def RankPolicy.IsMeasurable {Seed : Type*} [MeasurableSpace Seed] (π : RankPolicy Seed n) : Prop :=
  Measurable (fun z : Seed × (Fin n × (Fin n × (ℝ × RankHistory n))) =>
    π.decide z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)

lemma measurable_rank_time_eval : Measurable (fun z : (Fin n → ℝ) × Fin n => z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro k
  exact measurable_pi_apply k

lemma measurable_rankObservation_to_time : Measurable
    (fun z : (Fin n → ℝ) × Option (Fin n × ℝ) =>
      z.2.map (fun a => (z.1 a.1,a.2))) := by
  rw [measurable_comap_iff]
  let f : (((Fin n → ℝ) × Unit) ⊕ ((Fin n → ℝ) × (Fin n × ℝ))) → Unit ⊕ (ℝ × ℝ) :=
    Sum.elim (fun _ => Sum.inl ()) (fun z => Sum.inr (z.1 z.2.1,z.2.2))
  have hf : Measurable f := measurable_const.sumElim
    (measurable_inr.comp ((measurable_rank_time_eval.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd)))
  have hc : Measurable (fun z : (Fin n → ℝ) × Option (Fin n × ℝ) =>
      (z.1,rankObservationCode z.2)) :=
    measurable_fst.prodMk ((comap_measurable rankObservationCode).comp measurable_snd)
  have h := hf.comp ((MeasurableEquiv.prodSumDistrib (Fin n → ℝ) Unit (Fin n × ℝ)).measurable.comp hc)
  convert h using 1
  funext z
  rcases z with ⟨s,o⟩
  cases o <;> rfl

variable {Ω Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]

lemma measurable_rankHistory {p : Ω → Equiv.Perm (Fin n)} {x : Ω → Fin n → ℝ} {k : Ω → Fin n}
    (hp : Measurable p) (hx : ∀ i, Measurable (fun ω => x ω i)) (hk : Measurable k) :
    Measurable (fun ω => rankHistory (p ω) (x ω) (k ω)) := by
  classical
  apply measurable_pi_lambda
  intro j
  have hpj : Measurable (fun ω => (p ω).symm j) := (measurable_of_finite (fun q : Equiv.Perm (Fin n) => q.symm j)).comp hp
  have hCond : MeasurableSet {ω | (p ω).symm j < k ω} := measurableSet_lt hpj hk
  rw [measurable_comap_iff]
  have h : Measurable (fun ω : Ω => if (p ω).symm j < k ω then
      (Sum.inr ((p ω).symm j,x ω j) : Unit ⊕ (Fin n × ℝ)) else Sum.inl ()) :=
    Measurable.ite hCond (measurable_inr.comp (hpj.prodMk (hx j))) measurable_const
  convert h using 1
  funext ω
  simp only [rankHistory,Function.comp_def]
  split <;> rfl

lemma measurable_embedRankHistory {s : Ω → Fin n → ℝ} {H : Ω → RankHistory n}
    (hs : Measurable s) (hH : Measurable H) :
    Measurable (fun ω j => (H ω j).map (fun z => (s ω z.1,z.2))) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_rankObservation_to_time.comp (hs.prodMk ((measurable_pi_apply j).comp hH))

lemma Policy.clockToRank_measurable (π : Policy Seed n) (hπ : π.IsMeasurable) :
    π.clockToRank.IsMeasurable := by
  let A := ((Fin n → ℝ) × Seed) × (Fin n × (Fin n × (ℝ × RankHistory n)))
  have hr : Measurable (fun z : A => z.1.2) := measurable_snd.comp measurable_fst
  have hs : Measurable (fun z : A => z.1.1) := measurable_fst.comp measurable_fst
  have hk : Measurable (fun z : A => z.2.1) := measurable_fst.comp measurable_snd
  have hi : Measurable (fun z : A => z.2.2.1) := by fun_prop
  have hx : Measurable (fun z : A => z.2.2.2.1) := by fun_prop
  have hH : Measurable (fun z : A => z.2.2.2.2) := by fun_prop
  have ht := measurable_rank_time_eval.comp (hs.prodMk hk)
  have hPast := measurable_embedRankHistory hs hH
  exact hπ.comp (hr.prodMk (ht.prodMk (hi.prodMk (hx.prodMk hPast))))

lemma RankPolicy.measurable_action (π : RankPolicy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {p : Ω → Equiv.Perm (Fin n)} {x : Ω → Fin n → ℝ}
    (hr : Measurable r) (hp : Measurable p) (hx : ∀ j, Measurable (fun ω => x ω j)) (i : Fin n) :
    Measurable (fun ω => π.action (r ω) (p ω) (x ω) i) := by
  have hk : Measurable (fun ω => (p ω).symm i) :=
    (measurable_of_finite (fun q : Equiv.Perm (Fin n) => q.symm i)).comp hp
  exact hπ.comp (hr.prodMk (hk.prodMk (measurable_const.prodMk
    ((hx i).prodMk (measurable_rankHistory hp hx hk)))))

lemma RankPolicy.measurableSet_reaches (π : RankPolicy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {p : Ω → Equiv.Perm (Fin n)} {x : Ω → Fin n → ℝ}
    (hr : Measurable r) (hp : Measurable p) (hx : ∀ j, Measurable (fun ω => x ω j)) (i : Fin n) :
    MeasurableSet {ω | π.Reaches (r ω) (p ω) (x ω) i} := by
  classical
  simp only [RankPolicy.Reaches,RankPolicy.mem_accepted]
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  have hA : MeasurableSet {ω | π.action (r ω) (p ω) (x ω) j = true} :=
    (π.measurable_action hπ hr hp hx j) (measurableSet_singleton true)
  have hi : Measurable (fun ω => (p ω).symm i) :=
    (measurable_of_finite (fun q : Equiv.Perm (Fin n) => q.symm i)).comp hp
  have hj : Measurable (fun ω => (p ω).symm j) :=
    (measurable_of_finite (fun q : Equiv.Perm (Fin n) => q.symm j)).comp hp
  have heq : {ω | π.action (r ω) (p ω) (x ω) j = true → (p ω).symm i ≤ (p ω).symm j} =
      {ω | π.action (r ω) (p ω) (x ω) j = true}ᶜ ∪ {ω | (p ω).symm i ≤ (p ω).symm j} := by
    ext ω
    exact imp_iff_not_or
  rw [heq]
  exact hA.compl.union (measurableSet_le hi hj)

lemma RankPolicy.measurableSet_selects (π : RankPolicy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {p : Ω → Equiv.Perm (Fin n)} {x : Ω → Fin n → ℝ}
    (hr : Measurable r) (hp : Measurable p) (hx : ∀ j, Measurable (fun ω => x ω j)) (i : Fin n) :
    MeasurableSet {ω | π.Selects (r ω) (p ω) (x ω) i} := by
  have hA : MeasurableSet {ω | π.action (r ω) (p ω) (x ω) i = true} :=
    (π.measurable_action hπ hr hp hx i) (measurableSet_singleton true)
  simpa only [RankPolicy.Selects,RankPolicy.mem_accepted,Set.setOf_and] using
    hA.inter (π.measurableSet_reaches hπ hr hp hx i)

lemma RankPolicy.measurable_reward (π : RankPolicy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {p : Ω → Equiv.Perm (Fin n)} {x : Ω → Fin n → ℝ}
    (hr : Measurable r) (hp : Measurable p) (hx : ∀ j, Measurable (fun ω => x ω j)) :
    Measurable (fun ω => π.reward (r ω) (p ω) (x ω)) := by
  classical
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (π.measurableSet_selects hπ hr hp hx i) (hx i) measurable_const

end ProphetSecretary.Model
