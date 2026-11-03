import ProphetSecretary.Statistics.ScalarPlannerDataMeasurability

/-!
# Independent seed banks for data-selected query levels

A query reads only the block for the level selected from its inputs. A
deterministic public cap on levels lets all training and online seed spaces
be fixed before the data are drawn.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ} {k : Fin n → ℕ}

noncomputable def scalarPlannerLevel (β h : ℝ) : ℕ :=
  if H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio β h then
    (countedScalarPlannerLevel β h H).1 else 0

lemma scalarPlannerLevel_error {β h : ℝ} (hβ : 1 ≤ β) (hh : h ∈ Ioo (0 : ℝ) 1) :
    25*β^2*(1/2 : ℝ)^scalarPlannerLevel β h ≤ h^2/64 := by
  simp only [scalarPlannerLevel, dif_pos (scalarPlannerPrecision_exists hβ hh)]
  exact countedScalarPlannerLevel_error hβ hh _

lemma scalarPlannerLevel_le_of_error {β h : ℝ} (hβ : 1 ≤ β) (hh : h ∈ Ioo (0 : ℝ) 1)
    {R : ℕ} (hR : 25*β^2*(1/2 : ℝ)^R ≤ h^2/64) :
    scalarPlannerLevel β h ≤ R := by
  let H := scalarPlannerPrecision_exists hβ hh
  have hR' : (1/2 : ℝ)^R ≤ scalarPlannerPrecisionRatio β h := by
    unfold scalarPlannerPrecisionRatio
    have hd : 0 < 1600*β^2 := by positivity
    apply (le_div_iff₀ hd).mpr
    linarith only [hR, show (1/2 : ℝ)^R*(1600*β^2) = 64*(25*β^2*(1/2 : ℝ)^R) by ring]
  rw [scalarPlannerLevel, dif_pos H]
  exact le_of_not_gt (fun h => (not_lt_of_ge hR') (countedScalarPlannerLevel_least hβ hh H R h))

noncomputable def boundedScalarPlannerLevel (R : ℕ) (h : ℝ) (y : ScalarPlannerRows n k)
    (A : Finset (Fin n)) : Fin (R+1) :=
  ⟨min R (scalarPlannerLevel (scalarPlannerWeight y A) h), Nat.lt_succ_of_le (min_le_left _ _)⟩

lemma measurable_boundedScalarPlannerLevel (R : ℕ) (h : ℝ) :
    Measurable (fun q : ScalarPlannerRows n k × Finset (Fin n) =>
      boundedScalarPlannerLevel R h q.1 q.2) := by
  let f : Finset (Fin n) × ((i : Fin n) → Fin (k i+1)) → Fin (R+1) := fun q =>
    ⟨min R (scalarPlannerLevel (plannerWeight q.1 (scalarPlannerCountProbability q.2)) h),
      Nat.lt_succ_of_le (min_le_left _ _)⟩
  have hf : Measurable f := measurable_of_countable _
  simpa only [Function.comp_def, f, boundedScalarPlannerLevel, scalarPlannerWeight,
    scalarPlannerCountProbability_counts] using
    hf.comp (measurable_plannerActive_data.prodMk (measurable_scalarPlannerPositiveCounts.comp measurable_fst))

abbrev ScalarPlannerSeedBank (n R copies : ℕ) :=
  (j : Fin (R+1)) → Fin copies → MultilevelTree (PlannerUniformSeed n) j.val

noncomputable def scalarPlannerSeedBankLaw (n R copies : ℕ) : Measure (ScalarPlannerSeedBank n R copies) :=
  Measure.pi fun j => Measure.pi fun _ => multilevelTreeLaw (plannerUniformSeedLaw n) j.val

instance (n R copies : ℕ) : IsProbabilityMeasure (scalarPlannerSeedBankLaw n R copies) := by
  unfold scalarPlannerSeedBankLaw
  infer_instance

noncomputable def scalarPlannerBankQuery (R : ℕ) (h p : ℝ) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (y : ScalarPlannerRows n k) (x : ScalarPlannerState n)
    (s : ScalarPlannerSeedBank n R (confidenceCopyCount p H)) : ℝ :=
  let q := scalarPlannerClampRows y
  let j := boundedScalarPlannerLevel R h q x.1
  (scalarPlannerQueryAtLevel q x j.val p H (s j)).value

set_option maxHeartbeats 1200000 in
theorem measurable_scalarPlannerBankQuery (R : ℕ) (h p : ℝ) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p) :
    Measurable (fun q : ScalarPlannerDataState n k × ScalarPlannerSeedBank n R (confidenceCopyCount p H) =>
      scalarPlannerBankQuery R h p H q.1.1 q.1.2 q.2) := by
  let Ω := ScalarPlannerDataState n k × ScalarPlannerSeedBank n R (confidenceCopyCount p H)
  let lev : Ω → Fin (R+1) := fun q => boundedScalarPlannerLevel R h (scalarPlannerClampRows q.1.1) q.1.2.1
  let f (j : Fin (R+1)) (q : Ω) :=
    (scalarPlannerQueryAtLevel (scalarPlannerClampRows q.1.1) q.1.2 j.val p H (q.2 j)).value
  have hrows : Measurable (fun q : Ω => q.1.1) := measurable_fst.comp measurable_fst
  have hA : Measurable (fun q : Ω => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hData : Measurable (fun q : Ω => (scalarPlannerClampRows q.1.1,q.1.2.1)) :=
    (measurable_scalarPlannerClampRows.comp hrows).prodMk hA
  have hlev : Measurable lev := by
    let v : ScalarPlannerRows n k × Finset (Fin n) → Fin (R+1) :=
      fun t => boundedScalarPlannerLevel R h t.1 t.2
    let g : Ω → ScalarPlannerRows n k × Finset (Fin n) := fun q =>
      (scalarPlannerClampRows q.1.1,q.1.2.1)
    change Measurable (v ∘ g)
    have hv : Measurable v := measurable_boundedScalarPlannerLevel (n := n) (k := k) R h
    have hg : Measurable g := hData
    exact hv.comp hg
  have hf (j : Fin (R+1)) : Measurable (f j) := by
    let g : Ω → ScalarPlannerMedianInput n k j.val (confidenceCopyCount p H) :=
      fun q => (q.1,q.2 j)
    have hfst : Measurable (fun q : Ω => q.1) := measurable_fst
    have hsnd : Measurable (fun q : Ω => q.2) := measurable_snd
    have hg : Measurable g := hfst.prodMk ((measurable_pi_apply j).comp hsnd)
    let v : ScalarPlannerMedianInput n k j.val (confidenceCopyCount p H) → ℝ := fun t =>
      (scalarPlannerQueryAtLevel (scalarPlannerClampRows t.1.1) t.1.2 j.val p H t.2).value
    change Measurable (v ∘ g)
    have hv : Measurable v :=
      measurable_scalarPlannerQueryAtLevel_clamped_data (n := n) (k := k) j.val p H
    exact hv.comp hg
  let F (j : Fin (R+1)) (q : Ω) : ℝ := if lev q = j then f j q else 0
  have hF (j : Fin (R+1)) : Measurable (F j) :=
    Measurable.ite (hlev (measurableSet_singleton j)) (hf j) measurable_const
  have hsum : Measurable (fun q : Ω => ∑ j : Fin (R+1), F j q) :=
    Finset.measurable_sum _ (fun j _ => hF j)
  have heq (q : Ω) : (∑ j : Fin (R+1), F j q) = f (lev q) q := by
    rw [Finset.sum_eq_single (lev q)]
    · simp only [F, if_pos rfl]
    · intro j _ hne
      exact if_neg (Ne.symm hne)
    · simp
  change Measurable (fun q : Ω => f (lev q) q)
  simp_rw [← heq]
  exact hsum

/-- The selected block has exactly the required independent-copy law. -/
theorem scalarPlannerBankQuery_correct [∀ i, NeZero (k i)]
    (R : ℕ) (h p : ℝ) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (hh : h ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    (y : ScalarPlannerRows n k) (hy : ∀ i j, y i j ∈ Icc (0 : ℝ) 1)
    (x : ScalarPlannerState n)
    (hR : 25*(scalarPlannerWeight y x.1)^2*(1/2 : ℝ)^R ≤ h^2/64) :
    (scalarPlannerSeedBankLaw n R (confidenceCopyCount p H)).real
      {s | h < |scalarPlannerBankQuery R h p H y x s -
        scalarPlannerValue y (fun i j => (hy i j).1) x|} ≤ p := by
  let β := scalarPlannerWeight y x.1
  have hβ : 1 ≤ β := scalarPlannerWeight_ge_one y x.1
  let j := boundedScalarPlannerLevel R h y x.1
  have hj : j.val = scalarPlannerLevel β h :=
    min_eq_right (scalarPlannerLevel_le_of_error hβ hh hR)
  have hc := scalarPlannerQueryAtLevel_correct y (fun i j => (hy i j).1)
    (fun i j => (hy i j).2) x j.val h p hh.1 hp.1 hp.2 H
    (by rw [hj]; exact scalarPlannerLevel_error hβ hh)
  let E := {t | h < |(scalarPlannerQueryAtLevel y x j.val p H t).value -
    scalarPlannerValue y (fun i j => (hy i j).1) x|}
  have habs := continuous_abs.measurable.comp
    (hc.1.sub_const (scalarPlannerValue y (fun i j => (hy i j).1) x))
  have hE : MeasurableSet E := measurableSet_lt measurable_const habs
  have hLaw := measurePreserving_eval (fun l : Fin (R+1) =>
    (Measure.pi (fun _ : Fin (confidenceCopyCount p H) =>
      multilevelTreeLaw (plannerUniformSeedLaw n) l.val))) j
  unfold scalarPlannerBankQuery
  dsimp only
  rw [scalarPlannerClampRows_eq y hy]
  change (scalarPlannerSeedBankLaw n R (confidenceCopyCount p H)).real ((fun s => s j) ⁻¹' E) ≤ _
  rw [← map_measureReal_apply hLaw.measurable hE]
  rw [show (scalarPlannerSeedBankLaw n R (confidenceCopyCount p H)).map (fun s => s j) = _ from hLaw.map_eq]
  exact hc.2.1

end ProphetSecretary.Statistics
