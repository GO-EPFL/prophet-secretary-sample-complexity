import ProphetSecretary.Statistics.ScalarPlannerWorkData

/-!
# Sampling only the active identities

The transition law is unchanged when uniform coordinates outside the
active list are omitted. The executable sampler draws three arrays of
active length and two scalar uniforms.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Model

variable {n : ℕ}

def countedPlannerIndexOf (i : Fin n) : List (Fin n) → ℕ × ℕ
  | [] => (0,1)
  | j :: l =>
    if j = i then (0,2)
    else
      let q := countedPlannerIndexOf i l
      (q.1+1,q.2+4)

lemma countedPlannerIndexOf_value (i : Fin n) (l : List (Fin n)) :
    (countedPlannerIndexOf i l).1 = l.idxOf i := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    by_cases h : j = i
    · simp [countedPlannerIndexOf, h]
    · rw [List.idxOf_cons_ne _ h]
      simp [countedPlannerIndexOf, h, ih]

lemma countedPlannerIndexOf_work (i : Fin n) (l : List (Fin n)) :
    (countedPlannerIndexOf i l).2 ≤ 4*l.length+1 := by
  induction l with
  | nil => simp [countedPlannerIndexOf]
  | cons j l ih =>
    simp only [countedPlannerIndexOf, List.length_cons]
    split <;> dsimp only <;> omega

def countedActiveSeedCoordinate {K : Type*} [Zero K] (l : List (Fin n))
    (u : Fin l.length → K) (i : Fin n) : K × ℕ :=
  let q := countedPlannerIndexOf i l
  let len := l.length
  if h : q.1 < len then (u ⟨q.1,h⟩,q.2+2*len+4) else (0,q.2+2*len+2)

lemma countedActiveSeedCoordinate_work {K : Type*} [Zero K] (l : List (Fin n))
    (u : Fin l.length → K) (i : Fin n) :
    (countedActiveSeedCoordinate l u i).2 ≤ 8*(l.length+1) := by
  have h := countedPlannerIndexOf_work i l
  dsimp only [countedActiveSeedCoordinate]
  split <;> dsimp only <;> omega

def plannerRestrictSeed {K : Type*} (l : List (Fin n))
    (s : PlannerFieldSeed n K) : PlannerFieldSeed l.length K :=
  ((s.1.1,fun i => s.1.2 (l.get i)),
    (s.2.1,(fun i => s.2.2.1 (l.get i),fun i => s.2.2.2 (l.get i))))

def plannerExpandSeed {K : Type*} [Zero K] (l : List (Fin n))
    (s : PlannerFieldSeed l.length K) : PlannerFieldSeed n K :=
  ((s.1.1,fun i => (countedActiveSeedCoordinate l s.1.2 i).1),
    (s.2.1,(fun i => (countedActiveSeedCoordinate l s.2.2.1 i).1,
      fun i => (countedActiveSeedCoordinate l s.2.2.2 i).1)))

private lemma activeSeedCoordinate_restrict {K : Type*} [Zero K] (l : List (Fin n))
    (u : Fin n → K) (i : Fin n) (hi : i ∈ l) :
    (countedActiveSeedCoordinate l (fun j => u (l.get j)) i).1 = u i := by
  unfold countedActiveSeedCoordinate
  have hq : (countedPlannerIndexOf i l).1 < l.length := by
    rw [countedPlannerIndexOf_value]
    exact List.idxOf_lt_length_iff.mpr hi
  rw [dif_pos hq]
  apply congrArg u
  have hidx : (⟨(countedPlannerIndexOf i l).1,hq⟩ : Fin l.length) =
      ⟨l.idxOf i,List.idxOf_lt_length_iff.mpr hi⟩ := Fin.ext (countedPlannerIndexOf_value i l)
  rw [hidx]
  exact List.idxOf_get _

private lemma measurable_activeSeedCoordinate (l : List (Fin n)) (i : Fin n) :
    Measurable (fun u : Fin l.length → ℝ => (countedActiveSeedCoordinate l u i).1) := by
  by_cases h : (countedPlannerIndexOf i l).1 < l.length
  · simpa only [countedActiveSeedCoordinate, dif_pos h] using
      (measurable_pi_apply (X := fun _ : Fin l.length => ℝ) ⟨_,h⟩)
  · simp only [countedActiveSeedCoordinate,dif_neg h]
    exact measurable_const

lemma measurable_plannerExpandSeed (l : List (Fin n)) :
    Measurable (plannerExpandSeed l : PlannerUniformSeed l.length → PlannerUniformSeed n) := by
  exact (measurable_fst.fst.prodMk (measurable_pi_iff.mpr fun i =>
    (measurable_activeSeedCoordinate l i).comp measurable_fst.snd)).prodMk
    (measurable_snd.fst.prodMk
      ((measurable_pi_iff.mpr fun i =>
        (measurable_activeSeedCoordinate l i).comp measurable_snd.snd.fst).prodMk
        (measurable_pi_iff.mpr fun i =>
          (measurable_activeSeedCoordinate l i).comp measurable_snd.snd.snd)))

private theorem measurePreserving_pi_read_injective {I J K : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace K] (μ : Measure K) [IsProbabilityMeasure μ] (e : I → J) (he : Function.Injective e) :
    MeasurePreserving (fun (s : J → K) i => s (e i))
      (Measure.pi (fun _ : J => μ)) (Measure.pi (fun _ : I => μ)) := by
  classical
  let sub := fun j : J => j ∈ Set.range e
  letI : Fintype (Subtype sub) := Subtype.fintype sub
  have hs := measurePreserving_piEquivPiSubtypeProd (fun _ : J => μ) sub
  let e' : I ≃ Subtype sub := Equiv.ofInjective e he
  have hπ := (measurePreserving_piCongrLeft (fun _ : Subtype sub => μ) e').symm
  exact hπ.comp (measurePreserving_fst.comp hs)

theorem measurePreserving_plannerRestrictSeed (l : List (Fin n)) (hl : l.Nodup) :
    MeasurePreserving (plannerRestrictSeed l) (plannerUniformSeedLaw n)
      (plannerUniformSeedLaw l.length) := by
  have h := measurePreserving_pi_read_injective Instance.uniformClock l.get hl.injective_get
  have hI := MeasurePreserving.id Instance.uniformClock
  exact (hI.prod h).prod (hI.prod (h.prod h))

def countedActivePlannerSampler {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (p : Fin n → K) (s : PlannerFieldSeed l.length K) :
    PlannerListOutput n K × ℕ :=
  let q := countedPlannerUniformSampler l p (plannerExpandSeed l s)
  (q.1, q.2*(8*(l.length+1))+2*(l.length+1)+10)

theorem countedActivePlannerSampler_work {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (hl : l.Nodup) (p : Fin n → K) (s : PlannerFieldSeed l.length K) :
    (countedActivePlannerSampler l p s).2 ≤ 8020*(l.length+1)^4 := by
  have h := countedPlannerUniformSampler_work l hl p (plannerExpandSeed l s)
  calc
    _ ≤ 1000*(l.length+1)^3*(8*(l.length+1))+2*(l.length+1)+10 :=
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _) _
    _ = 8000*(l.length+1)^4+2*(l.length+1)+10 := by ring
    _ ≤ _ := by
      have h1 : 1 ≤ (l.length+1)^4 := Nat.one_le_pow 4 _ (by omega)
      have h2 : l.length+1 ≤ (l.length+1)^4 := by
        calc
          _ = (l.length+1)^1 := by simp
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
      omega

private lemma activeSampler_value_restrict (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → ℝ) (hA : l.toFinset.Nonempty) (s : PlannerUniformSeed n) :
    plannerListOutputToSet (countedActivePlannerSampler l p (plannerRestrictSeed l s)).1 =
      plannerUniformTransition l.toFinset p s := by
  change plannerListOutputToSet (countedPlannerUniformSampler l p _).1 = _
  rw [countedPlannerUniformSampler_value l hl]
  symm
  apply plannerUniformTransition_eq_of_seed_agrees _ _ hA
  · rfl
  · rfl
  · intro i hi
    exact (activeSeedCoordinate_restrict l s.1.2 i
      (List.mem_toFinset.mp (Finset.mem_filter.mp hi).1)).symm
  · intro i hi
    exact (activeSeedCoordinate_restrict l s.2.2.1 i
      (List.mem_toFinset.mp (plannerFirstSuccessUniform_subset _ _ hA s.1 hi))).symm
  · intro i hi
    exact (activeSeedCoordinate_restrict l s.2.2.2 i
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hi).1)).symm

/-- A compressed independent uniform seed has the same kernel law
as the full array seed, with no draws for inactive identities. -/
theorem map_countedActivePlannerSampler (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → ℝ) (hA : l.toFinset.Nonempty) (hp : ∀ i ∈ l.toFinset, 0 < p i) :
    (plannerUniformSeedLaw l.length).map
      (fun s => plannerListOutputToSet (countedActivePlannerSampler l p s).1) =
      (plannerKernelLaw l.toFinset p).map plannerSomeTransition := by
  let f := fun s : PlannerUniformSeed l.length =>
    plannerListOutputToSet (countedActivePlannerSampler l p s).1
  have hf : Measurable f := by
    have he : f = plannerUniformTransition l.toFinset p ∘ plannerExpandSeed l := by
      funext s
      exact countedPlannerUniformSampler_value l hl p (plannerExpandSeed l s)
    rw [he]
    exact (measurable_plannerUniformTransition _ _).comp (measurable_plannerExpandSeed l)
  have hproj := measurePreserving_plannerRestrictSeed l hl
  change (plannerUniformSeedLaw l.length).map f = _
  rw [← hproj.map_eq, Measure.map_map hf hproj.measurable]
  rw [show f ∘ plannerRestrictSeed l = plannerUniformTransition l.toFinset p by
    funext s
    exact activeSampler_value_restrict l hl p hA s]
  exact map_plannerUniformTransition_of_nonempty _ _ hA hp

universe v

def sampleActivePlannerM {M : Type → Type v} [Monad M] {K : Type} [Field K] [LinearOrder K]
    (l : List (Fin n)) (p : Fin n → K) (uniform : M K) : M (PlannerListOutput n K × ℕ) := do
  let s ← plannerFullSeedM l.length uniform
  pure (countedActivePlannerSampler l p s)

/-- The compressed sampler draws exactly three uniforms per active
identity and two more for the categorical choices. -/
theorem sampleActivePlannerM_draws {K : Type} [Field K] [LinearOrder K]
    (l : List (Fin n)) (p : Fin n → K) (a : K) (c : ℕ) :
    ((sampleActivePlannerM (M := StateM ℕ) l p (fun s => (a,s+1))).run c).2 =
      c+3*l.length+2 := by
  exact plannerFullSeedM_draws a l.length c

theorem sampleActivePlannerM_draws_le {K : Type} [Field K] [LinearOrder K]
    (l : List (Fin n)) (hl : l.Nodup) (hA : l.toFinset.Nonempty)
    (p : Fin n → K) (a : K) (c : ℕ) :
    ((sampleActivePlannerM (M := StateM ℕ) l p (fun s => (a,s+1))).run c).2 ≤
      c + 5*l.toFinset.card := by
  rw [sampleActivePlannerM_draws, List.toFinset_card_of_nodup hl]
  have h := Finset.card_pos.mpr hA
  rw [List.toFinset_card_of_nodup hl] at h
  omega

end ProphetSecretary.Statistics
