import ProphetSecretary.Statistics.BinaryPublicSearch
import ProphetSecretary.Statistics.BinaryCalibrationPublic
import ProphetSecretary.Statistics.PlannerBitPrecision
import ProphetSecretary.Statistics.BinaryScalarPlannerGuarantee

/-!
# Standalone scalar planning with binary rationals

The preparation computes the empirical weight and chooses the depth,
dyadic precision, and number of copies from the input. Each row keeps
its own observation count. The estimator uses the independent fair
bits of the selected finite shape.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability ProphetSecretary.Statistics.Calibration
open CalibrationBinaryExpr

variable {n : ℕ} {k : Fin n → ℕ}

def standaloneBinaryWeight (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) : BinaryRational :=
  let p := countedBinaryPlannerProbabilities rows
  (countedBinaryPlannerFrame (plannerProbabilityRead p.1) x).1.weight

lemma standaloneBinaryWeight_value (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) :
    (standaloneBinaryWeight rows x).value =
      storedScalarPlannerWeight (plannerRowsValueMap BinaryRational.value rows)
        (scalarPlannerStateValueMap BinaryRational.value x) := by
  let p := plannerProbabilityRead (countedBinaryPlannerProbabilities rows).1
  let rows' := plannerRowsValueMap BinaryRational.value rows
  have hp : plannerProbabilityRead (countedPlannerProbabilities rows').1 =
      fun i => (p i).value := by
    funext i
    exact (plannerProbabilityRead_valueMap BinaryRational.valueHom BinaryRational.value_strictMono rows i).trans
      (congrArg BinaryRational.value (countedBinaryPlannerProbabilities_value rows i).symm)
  have h := countedScalarPlannerFrame_valueMap BinaryRational.valueHom BinaryRational.value_strictMono p x
  rw [← countedBinaryPlannerFrame_value] at h
  unfold standaloneBinaryWeight storedScalarPlannerWeight
  dsimp only
  rw [hp]
  exact (congrArg ScalarPlannerFrame.weight h).symm

def standaloneBinaryGridExpr (β h N : BinaryRational) : CalibrationBinaryExpr :=
  .node .div (.node .mul (.atom 3) (.atom h))
    (.node .mul (.node .mul (.atom 4) (.atom β)) (.atom N))

def countedStandaloneBinaryGrid (n : ℕ) (β h : BinaryRational) : BinaryRational × ℕ :=
  let a := countedCalibrationNat (10*n+4)
  let q := (standaloneBinaryGridExpr β h a.1).evaluate
  (q.1,a.2+q.2+5)

lemma countedStandaloneBinaryGrid_value (n : ℕ) (β h : BinaryRational) :
    (countedStandaloneBinaryGrid n β h).1.value=plannerGridTolerance n β.value h.value := by
  simp only [countedStandaloneBinaryGrid,evaluate_value,standaloneBinaryGridExpr,
    CalibrationBinaryExpr.value,rationalCalibrationOp,countedCalibrationNat_value,
    show (3:BinaryRational).value=(3:ℚ) from BinaryRational.ofRat_value 3,
    show (4:BinaryRational).value=(4:ℚ) from BinaryRational.ofRat_value 4,
    plannerGridTolerance,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]

def countedBinaryStandalonePlan (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational) : BinaryPublicSearchResult :=
  let c := countedBinaryPlannerProbabilities rows
  let f := countedBinaryPlannerFrame (plannerProbabilityRead c.1) x
  let r := countedBinaryPrecisionRatio f.1.weight h
  let b := countedStandaloneBinaryGrid n f.1.weight h
  let s := countedBinaryPublicSearch r.1 b.1 p
  {s with work := c.2+f.2+r.2+b.2+s.work+7}

abbrev StandaloneBinarySeed (n : ℕ) (q : BinaryPublicSearchResult) :=
  Fin (2*q.halfCopies+1) → MultilevelTree (PlannerFairSeed n q.precision) q.level

noncomputable def standaloneBinarySeedLaw (n : ℕ) (q : BinaryPublicSearchResult) :
    Measure (StandaloneBinarySeed n q) :=
  Measure.pi fun _ => multilevelTreeLaw (plannerFairSeedLaw n q.precision) q.level

def countedBinaryStandaloneQuery (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational)
    (seed : StandaloneBinarySeed n (countedBinaryStandalonePlan rows x h p)) :
    MedianCopiesResult BinaryRational :=
  let s := countedBinaryStandalonePlan rows x h p
  let q := countedBinaryScalarQueryAtLevel rows x s.precision s.level s.halfCopies seed
  {q with work := s.work+q.work+3}

private lemma standaloneGrid_ratCast (n : ℕ) (β h : ℚ) :
    ((plannerGridTolerance n β h : ℚ):ℝ)=plannerGridTolerance n (β:ℝ) (h:ℝ) := by
  simp only [plannerGridTolerance,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]

private lemma standaloneRatio_ratCast (β h : ℚ) :
    ((scalarPlannerPrecisionRatio β (h/2):ℚ):ℝ)=scalarPlannerPrecisionRatio (β:ℝ) ((h:ℝ)/2) := by
  simp only [scalarPlannerPrecisionRatio,Rat.cast_pow,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat]

private lemma standaloneHalfPow_ratCast (r : ℕ) :
    (((1/2:ℚ)^r:ℚ):ℝ)=(1/2:ℝ)^r := by
  simp only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]

private lemma standaloneConfidence_congr {p q : ℝ} (e : p=q)
    (H : ∃ j : ℕ, (1/4:ℝ)^j≤p) (G : ∃ j : ℕ, (1/4:ℝ)^j≤q) :
    (countedConfidenceLevel p H).1=(countedConfidenceLevel q G).1 := by
  subst q
  rfl

set_option maxHeartbeats 1000000 in
private theorem standaloneSearch_spec (n : ℕ) (w h p : BinaryRational) (β : ℝ)
    (hw : (w.value:ℝ)=β) (hβ : 1≤β) (hh : (h.value:ℝ)∈Ioo (0:ℝ) 1)
    (hp : (p.value:ℝ)∈Ioo (0:ℝ) 1) (HC : ∃ j : ℕ, (1/4:ℚ)^j≤p.value) :
    let q := countedBinaryPublicSearch (countedBinaryPrecisionRatio w h).1 (countedStandaloneBinaryGrid n w h).1 p
    let H := scalarPlannerPrecision_exists hβ
      (show (h.value:ℝ)/2∈Ioo (0:ℝ) 1 from ⟨by linarith [hh.1],by linarith [hh.2]⟩)
    let G := exists_confidence_level (plannerGridTolerance_pos n (zero_lt_one.trans_le hβ) hh.1)
      (plannerGridTolerance_lt_one n hβ hh.2.le)
    q.level=(countedScalarPlannerLevel β ((h.value:ℝ)/2) H).1 ∧
      q.precision=(countedPlannerBitPrecision n β (h.value:ℝ) G).1 ∧
      q.halfCopies=(countedConfidenceLevel p.value HC).1 := by
  dsimp only
  let r := (countedBinaryPrecisionRatio w h).1
  let b := (countedStandaloneBinaryGrid n w h).1
  have hR : (r.value:ℝ)=scalarPlannerPrecisionRatio β ((h.value:ℝ)/2) := by
    dsimp only [r]
    rw [countedBinaryPrecisionRatio_value,standaloneRatio_ratCast,hw]
  have hB : (b.value:ℝ)=plannerGridTolerance n β (h.value:ℝ) := by
    dsimp only [b]
    rw [countedStandaloneBinaryGrid_value,standaloneGrid_ratCast,hw]
  have hh2 : (h.value:ℝ)/2∈Ioo (0:ℝ) 1 := ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have hr : 0<r.value := by
    apply (Rat.cast_pos (K:=ℝ)).mp
    rw [hR]
    exact (scalarPlannerPrecisionRatio_mem hβ hh2).1
  have hb : 0<b.value := by
    apply (Rat.cast_pos (K:=ℝ)).mp
    rw [hB]
    exact plannerGridTolerance_pos n (zero_lt_one.trans_le hβ) hh.1
  let H := scalarPlannerPrecision_exists hβ hh2
  let G := exists_confidence_level (plannerGridTolerance_pos n (zero_lt_one.trans_le hβ) hh.1)
    (plannerGridTolerance_lt_one n hβ hh.2.le)
  have GB : ∃ j : ℕ, (1/4:ℚ)^j≤b.value :=
    (exists_quarter_pow_le_ratCast b.value).mp (by rw [hB]; exact G)
  have s := countedBinaryPublicSearch_spec r b p hr hb ((Rat.cast_pos (K:=ℝ)).mp hp.1) GB HC
  dsimp only at s
  let q := countedBinaryPublicSearch r b p
  have hqR : (1/2:ℝ)^q.level≤scalarPlannerPrecisionRatio β ((h.value:ℝ)/2) := by
    rw [←hR,←standaloneHalfPow_ratCast]
    exact Rat.cast_le.mpr s.1
  have hqL (j : ℕ) (hj : j<q.level) :
      scalarPlannerPrecisionRatio β ((h.value:ℝ)/2)<(1/2:ℝ)^j := by
    rw [←hR,←standaloneHalfPow_ratCast]
    exact Rat.cast_lt.mpr (s.2.1 j hj)
  have hLevel : q.level=(countedScalarPlannerLevel β ((h.value:ℝ)/2) H).1 := by
    apply le_antisymm
    · exact le_of_not_gt fun hn => (hqL _ hn).not_ge (countedScalarPlannerLevel_precision hβ hh2 H)
    · exact le_of_not_gt fun hn => (countedScalarPlannerLevel_least hβ hh2 H _ hn).not_ge hqR
  have hQuarter : (countedConfidenceLevel b.value GB).1 =
      (countedConfidenceLevel (plannerGridTolerance n β (h.value:ℝ)) G).1 := by
    let G' := (exists_quarter_pow_le_ratCast b.value).mpr GB
    have e := congrArg Prod.fst (countedConfidenceLevel_ratCast b.value GB G')
    have e' : (countedConfidenceLevel (b.value:ℝ) G').1 =
        (countedConfidenceLevel (plannerGridTolerance n β (h.value:ℝ)) G).1 :=
      standaloneConfidence_congr hB G' G
    exact e.symm.trans e'
  have hPrec : q.precision=(countedPlannerBitPrecision n β (h.value:ℝ) G).1 := by
    rw [show q.precision=2*(countedConfidenceLevel b.value GB).1+1 from s.2.2.1,hQuarter]
    rfl
  change q.level=(countedScalarPlannerLevel β ((h.value:ℝ)/2) H).1 ∧
    q.precision=(countedPlannerBitPrecision n β (h.value:ℝ) G).1 ∧
    q.halfCopies=(countedConfidenceLevel p.value HC).1
  exact ⟨hLevel,hPrec,s.2.2.2⟩

set_option maxHeartbeats 800000 in
/-- The native schedule meets the stochastic and rounding tolerances
and uses the exact confidence copy count. -/
theorem countedBinaryStandalonePlan_spec (y : (i : Fin n) → Fin (k i) → BinaryRational)
    (x : ScalarPlannerListState n BinaryRational) (hx : x.1.Nodup) (h p : BinaryRational)
    (hh : (h.value:ℝ)∈Ioo (0:ℝ) 1) (hp : (p.value:ℝ)∈Ioo (0:ℝ) 1)
    (HC : ∃ j : ℕ, (1/4:ℚ)^j≤p.value) :
    let yR := fun i j => ((y i j).value:ℝ)
    let xR := scalarPlannerListInterpret (scalarPlannerStateRatCast (scalarPlannerStateValueMap BinaryRational.value x))
    let β := scalarPlannerWeight yR xR.1
    let q := countedBinaryStandalonePlan (plannerStoredRows y) x h p
    let H := scalarPlannerPrecision_exists (scalarPlannerWeight_ge_one yR xR.1)
      (show (h.value:ℝ)/2∈Ioo (0:ℝ) 1 from ⟨by linarith [hh.1],by linarith [hh.2]⟩)
    let G := exists_confidence_level (plannerGridTolerance_pos n
      (zero_lt_one.trans_le (scalarPlannerWeight_ge_one yR xR.1)) hh.1)
      (plannerGridTolerance_lt_one n (scalarPlannerWeight_ge_one yR xR.1) hh.2.le)
    q.level=(countedScalarPlannerLevel β ((h.value:ℝ)/2) H).1 ∧
      q.precision=(countedPlannerBitPrecision n β (h.value:ℝ) G).1 ∧
      q.halfCopies=(countedConfidenceLevel p.value HC).1 := by
  dsimp only
  let yR := fun i j => ((y i j).value:ℝ)
  let xq := scalarPlannerStateValueMap BinaryRational.value x
  let xR := scalarPlannerListInterpret (scalarPlannerStateRatCast xq)
  let β := scalarPlannerWeight yR xR.1
  let w := standaloneBinaryWeight (plannerStoredRows y) x
  let yr := fun i j => (y i j).value
  let xL := scalarPlannerStateRatCast xq
  have hq : w.value=storedScalarPlannerWeight (plannerStoredRows yr) xq :=
    (standaloneBinaryWeight_value (plannerStoredRows y) x).trans
      (congrArg (fun r => storedScalarPlannerWeight r xq) (plannerStoredRows_valueMap BinaryRational.value y))
  have hCast := (storedScalarPlannerWeight_ratCast (plannerStoredRows yr) xq).symm.trans
    (congrArg (fun r => storedScalarPlannerWeight r xL) (plannerRowsRatCast_ofFn yr))
  have hw : (w.value:ℝ)=β :=
    (congrArg (fun q : ℚ => (q:ℝ)) hq).trans
      (hCast.trans (storedScalarPlannerWeight_value yR xL hx))
  let q := countedBinaryPublicSearch (countedBinaryPrecisionRatio w h).1 (countedStandaloneBinaryGrid n w h).1 p
  have he := standaloneSearch_spec n w h p β hw (scalarPlannerWeight_ge_one yR xR.1) hh hp HC
  dsimp only at he
  have hL : (countedBinaryStandalonePlan (plannerStoredRows y) x h p).level=q.level := by
    simp only [countedBinaryStandalonePlan,q,w,standaloneBinaryWeight]
  have hB : (countedBinaryStandalonePlan (plannerStoredRows y) x h p).precision=q.precision := by
    simp only [countedBinaryStandalonePlan,q,w,standaloneBinaryWeight]
  have hA : (countedBinaryStandalonePlan (plannerStoredRows y) x h p).halfCopies=q.halfCopies := by
    simp only [countedBinaryStandalonePlan,q,w,standaloneBinaryWeight]
  exact ⟨hL.trans he.1,hB.trans he.2.1,hA.trans he.2.2⟩

def standaloneGridHeight (n W B : ℕ) : ℕ := W+B+(10*n+4)+2

private lemma standaloneGrid_leaves (n W B : ℕ) (β h : BinaryRational)
    (hβ : RationalHeight β.value W) (hh : RationalHeight h.value B) :
    (standaloneBinaryGridExpr β h (countedCalibrationNat (10*n+4)).1).leavesFit
      (standaloneGridHeight n W B) := by
  let D := standaloneGridHeight n W B
  have h3 : RationalHeight (3:BinaryRational).value D := by
    rw [show (3:BinaryRational).value=(3:ℚ) from BinaryRational.ofRat_value 3]
    exact (rationalHeight_natCast 3 2 (by decide)).mono (by dsimp only [D,standaloneGridHeight]; omega)
  have h4 : RationalHeight (4:BinaryRational).value D := by
    rw [show (4:BinaryRational).value=(4:ℚ) from BinaryRational.ofRat_value 4]
    exact (rationalHeight_natCast 4 2 (by decide)).mono (by dsimp only [D,standaloneGridHeight]; omega)
  have hN : RationalHeight (countedCalibrationNat (10*n+4)).1.value D := by
    rw [countedCalibrationNat_value]
    exact (rationalHeight_natCast _ (10*n+4) (Nat.lt_two_pow_self.le)).mono
      (by dsimp only [D,standaloneGridHeight]; omega)
  exact ⟨⟨h3,hh.mono (by dsimp only [D,standaloneGridHeight]; omega)⟩,
    ⟨⟨h4,hβ.mono (by dsimp only [D,standaloneGridHeight]; omega)⟩,hN⟩⟩

lemma countedStandaloneBinaryGrid_height (n W B : ℕ) (β h : BinaryRational)
    (hβ : RationalHeight β.value W) (hh : RationalHeight h.value B) :
    RationalHeight (countedStandaloneBinaryGrid n β h).1.value (9*(standaloneGridHeight n W B+1)) := by
  unfold countedStandaloneBinaryGrid
  dsimp only
  rw [evaluate_value]
  exact value_height _ _ (standaloneGrid_leaves n W B β h hβ hh)

lemma countedStandaloneBinaryGrid_work (n W B : ℕ) (β h : BinaryRational)
    (hβ : RationalHeight β.value W) (hh : RationalHeight h.value B) :
    (countedStandaloneBinaryGrid n β h).2≤
      3*(10*n+4+1)+3+9*workUnit 9 (standaloneGridHeight n W B)+5 := by
  have hN := countedCalibrationNat_work (10*n+4) (10*n+4) Nat.lt_two_pow_self.le
  have hE := evaluate_work (standaloneBinaryGridExpr β h (countedCalibrationNat (10*n+4)).1) 9
    (standaloneGridHeight n W B) (standaloneGrid_leaves n W B β h hβ hh) (by rfl)
  exact Nat.add_le_add_right (Nat.add_le_add hN hE) 5

def standaloneBinaryPlanWorkBound (n m B : ℕ) : ℕ :=
  let W := n*(2*m+3)
  let G := standaloneGridHeight n W B
  let D := 2*B+2*W+13
  n*binaryRowProbabilityWorkBound m B m+3*n+1+
    binaryFrameWorkBound n (2*m) B B+(5*(3600*(D+2)^3)+8)+
    (3*(10*n+4+1)+3+9*workUnit 9 G+5)+binaryPublicSearchWorkBound (D+9*(G+1)+B)+7

theorem countedBinaryStandalonePlan_work (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational) (m B : ℕ) (hB : 2≤B)
    (hRows : ∀ i, (rows.get i).length≤m) (hy : ∀ i y, y∈rows.get i → RationalHeight y.value B)
    (hx : x.1.Nodup) (hu : RationalHeight x.2.1.value B) (hz : RationalHeight x.2.2.value B)
    (hh : RationalHeight h.value B) (hp : RationalHeight p.value B) :
    (countedBinaryStandalonePlan rows x h p).work≤standaloneBinaryPlanWorkBound n m B := by
  let c := countedBinaryPlannerProbabilities rows
  let q := plannerProbabilityRead c.1
  let f := countedBinaryPlannerFrame q x
  let β := f.1.weight
  let W := n*(2*m+3)
  let G := standaloneGridHeight n W B
  let D := 2*B+2*W+13
  have hc := countedBinaryPlannerProbabilities_work rows m B m hRows Nat.lt_two_pow_self.le hy
  have hq (i : Fin n) : RationalHeight (q i).value (2*m) := by
    have he : q i=(countedBinaryRowProbability (rows.get i)).1 := by
      simp [q,c,plannerProbabilityRead,countedBinaryPlannerProbabilities,Vector.get]
    rw [he]
    exact countedBinaryRowProbability_height (rows.get i) m ((hRows i).trans Nat.lt_two_pow_self.le)
  have hf := countedBinaryPlannerFrame_work q x (2*m) B B hx hq hu hz hB
  have hW : RationalHeight β.value W := by
    have hL : x.1.length≤n := by
      simpa only [List.toFinset_card_of_nodup hx,Fintype.card_fin] using Finset.card_le_univ x.1.toFinset
    have hA : (countedBinaryPlannerActive q x.1).1.length≤n := by
      rw [countedBinaryPlannerActive_value]
      exact (countedPlannerActive_length q x.1).trans hL
    exact (countedBinaryPlannerWeight_height q _ (2*m) hq).mono (Nat.mul_le_mul_right _ hA)
  have hr := countedBinaryPrecisionRatio_work β h W B hW hh
  have hg := countedStandaloneBinaryGrid_work n W B β h hW hh
  have hs := countedBinaryPublicSearch_work (countedBinaryPrecisionRatio β h).1
    (countedStandaloneBinaryGrid n β h).1 p (D+9*(G+1)+B)
      ((countedBinaryPrecisionRatio_height β h W B hW hh).mono (by omega))
      ((countedStandaloneBinaryGrid_height n W B β h hW hh).mono (by omega)) (hp.mono (by omega))
  change c.2+f.2+(countedBinaryPrecisionRatio β h).2+(countedStandaloneBinaryGrid n β h).2+
    (countedBinaryPublicSearch (countedBinaryPrecisionRatio β h).1 (countedStandaloneBinaryGrid n β h).1 p).work+7≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc hf) hr) hg) hs) 7

theorem countedBinaryStandaloneQuery_work (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational) (m B : ℕ) (hB : 2≤B)
    (hRows : ∀ i, (rows.get i).length≤m) (hy : ∀ i y, y∈rows.get i → RationalHeight y.value B)
    (hx : x.1.Nodup) (hu : RationalHeight x.2.1.value B) (hz : RationalHeight x.2.2.value B)
    (hh : RationalHeight h.value B) (hp : RationalHeight p.value B)
    (seed : StandaloneBinarySeed n (countedBinaryStandalonePlan rows x h p)) :
    let s := countedBinaryStandalonePlan rows x h p
    (countedBinaryStandaloneQuery rows x h p seed).work≤standaloneBinaryPlanWorkBound n m B+
      binaryScalarQueryWorkBound n m B m B B s.precision s.level s.halfCopies+3 := by
  dsimp only
  let s := countedBinaryStandalonePlan rows x h p
  have hPlan := countedBinaryStandalonePlan_work rows x h p m B hB hRows hy hx hu hz hh hp
  have hQ := countedBinaryScalarQueryAtLevel_work rows x s.precision s.level s.halfCopies s.level m B m B B
    seed le_rfl Nat.lt_two_pow_self.le hRows hy hx hu hz hB
  exact Nat.add_le_add_right (Nat.add_le_add hPlan hQ) 3

variable [∀ i, NeZero (k i)]

/-- The binary query implements the empirical continuation guarantee on
the actual finite fair-bit arrays, at the data-selected schedule. -/
theorem countedBinaryStandaloneQuery_correct (y : (i : Fin n) → Fin (k i) → BinaryRational)
    (hy : ∀ i j, 0≤((y i j).value:ℝ)) (hcap : ∀ i j, ((y i j).value:ℝ)≤1)
    (x : ScalarPlannerListState n BinaryRational) (hx : x.1.Nodup) (h p : BinaryRational)
    (hh : (h.value:ℝ)∈Ioo (0:ℝ) 1) (hp : (p.value:ℝ)∈Ioo (0:ℝ) (1/2))
    (m B : ℕ) (hB : 2≤B) (hk : ∀ i, k i≤m) (hY : ∀ i j, RationalHeight (y i j).value B)
    (hu : RationalHeight x.2.1.value B) (hz : RationalHeight x.2.2.value B) :
    let rows := plannerStoredRows y
    let plan := countedBinaryStandalonePlan rows x h p
    let Q := countedBinaryStandaloneQuery rows x h p
    let v := scalarPlannerValue (fun i j => ((y i j).value:ℝ)) hy
      (scalarPlannerListInterpret (scalarPlannerStateRatCast (scalarPlannerStateValueMap BinaryRational.value x)))
    Measurable (fun seed => ((Q seed).value.value:ℝ)) ∧
      (standaloneBinarySeedLaw n plan).real {seed | (h.value:ℝ)< |((Q seed).value.value:ℝ)-v|}≤(p.value:ℝ) := by
  dsimp only
  let rows := plannerStoredRows y
  let plan := countedBinaryStandalonePlan rows x h p
  let xq := scalarPlannerStateValueMap BinaryRational.value x
  let xR := scalarPlannerListInterpret (scalarPlannerStateRatCast xq)
  let yr := fun i j => (y i j).value
  let yR := fun i j => (yr i j:ℝ)
  let β := scalarPlannerWeight yR xR.1
  let v := scalarPlannerValue yR hy xR
  have hp1 : (p.value:ℝ)<1 := hp.2.trans (by norm_num)
  let HC := (exists_quarter_pow_le_ratCast p.value).mp (exists_confidence_level hp.1 hp1)
  have hβ : 1≤β := scalarPlannerWeight_ge_one _ _
  have hh2 : (h.value:ℝ)/2∈Ioo (0:ℝ) 1 := ⟨by linarith [hh.1],by linarith [hh.2]⟩
  let H := scalarPlannerPrecision_exists hβ hh2
  let G := exists_confidence_level (plannerGridTolerance_pos n (zero_lt_one.trans_le hβ) hh.1)
    (plannerGridTolerance_lt_one n hβ hh.2.le)
  have hs := countedBinaryStandalonePlan_spec y x hx h p hh ⟨hp.1,hp1⟩ HC
  dsimp only at hs
  have hLevel : plan.level=(countedScalarPlannerLevel β ((h.value:ℝ)/2) H).1 := hs.1
  have hPrec : plan.precision=(countedPlannerBitPrecision n β (h.value:ℝ) G).1 := hs.2.1
  have hR : 25*β^2*(1/2:ℝ)^plan.level≤((h.value:ℝ)/2)^2/64 := by
    rw [hLevel]
    exact countedScalarPlannerLevel_error hβ hh2 H
  have hGrid : β*((10*(n:ℝ)+4)/(3*((2^plan.precision:ℕ):ℝ)))≤(h.value:ℝ)/4 := by
    rw [hPrec]
    exact (countedPlannerBitPrecision_correct n hβ hh.1 hh.2.le G).2.1
  have hQ := countedBinaryScalarQueryAtLevel_correct y hy hcap x hx plan.precision plan.level
    (h.value:ℝ) p.value hh.1 hp.1 hp1 HC hR hGrid m B m B B hk Nat.lt_two_pow_self.le hY hu hz hB
  dsimp only at hQ
  have hTransfer (a : ℕ) (ha : a=(countedConfidenceLevel p.value HC).1) :
      let Q := countedBinaryScalarQueryAtLevel rows x plan.precision plan.level a
      Measurable (fun seed => ((Q seed).value.value:ℝ)) ∧
        (Measure.pi (fun _ : Fin (2*a+1) => multilevelTreeLaw (plannerFairSeedLaw n plan.precision) plan.level)).real
          {seed | (h.value:ℝ)< |((Q seed).value.value:ℝ)-v|}≤(p.value:ℝ) := by
    subst a
    dsimp only
    exact ⟨hQ.1,hQ.2.1⟩
  exact hTransfer plan.halfCopies hs.2.2

end ProphetSecretary.Statistics
