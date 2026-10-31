import ProphetSecretary.Statistics.BoundedGridTransfer
import ProphetSecretary.Probability.ProbabilityMeshDenominator

/-!
# The explicit probability mesh of the bounded learner

The denominator is chosen before the unknown law. Its total moved mass is
at most μ/2, while the error of the complete k-sample/online experiment
contributes at most m⁻² to both guarantees. The denominator may depend on n
and the alphabet size; the guarantee constants do not.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def boundedGridMeshTolerance (k m : ℕ) (μ : ℝ) : ℝ :=
  min (μ/2) (1/(((k : ℝ)+2)*(m : ℝ)^2))

noncomputable def boundedGridMeshDenominator (n k m : ℕ) (G : Finset ℝ) (μ : ℝ) : ℕ :=
  probabilityMeshDenominator ((n : ℝ)*((G.card-1 : ℕ) : ℝ)) (boundedGridMeshTolerance k m μ)

lemma boundedGridMeshDenominator_positive (n k m : ℕ) (G : Finset ℝ) (μ : ℝ) :
    0<boundedGridMeshDenominator n k m G μ := probabilityMeshDenominator_positive _ _

lemma boundedGridMeshTolerance_positive (k : ℕ) {m : ℕ} (hm : 0<m) {μ : ℝ} (hμ : 0<μ) :
    0<boundedGridMeshTolerance k m μ := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  unfold boundedGridMeshTolerance
  apply lt_min
  · positivity
  · positivity

lemma atomRoundingLoss_boundedGridMesh {n k m : ℕ} (P : Instance n) (G : Finset ℝ) (hz : (0 : ℝ)∈G)
    (hm : 0<m) {μ : ℝ} (hμ : 0<μ) :
    P.atomRoundingLoss G (boundedGridMeshDenominator n k m G μ) hz≤μ/2 ∧
    ((k : ℝ)+2)*P.atomRoundingLoss G (boundedGridMeshDenominator n k m G μ) hz≤1/(m : ℝ)^2 := by
  let N := boundedGridMeshDenominator n k m G μ
  have hN : 0<N := boundedGridMeshDenominator_positive _ _ _ _ _
  have hLoss := (P.atomRoundingLoss_le G N hN hz).trans
    (probabilityMeshDenominator_bound _ _ (boundedGridMeshTolerance_positive k hm hμ))
  have hSmall := hLoss.trans (min_le_right _ _)
  have hK : (0 : ℝ)<(k : ℝ)+2 := by positivity
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hCancel : ((k : ℝ)+2)*(1/(((k : ℝ)+2)*(m : ℝ)^2))=1/(m : ℝ)^2 := by
    field_simp
  exact ⟨hLoss.trans (min_le_left _ _),by
    simpa only [hCancel] using mul_le_mul_of_nonneg_left hSmall hK.le⟩

noncomputable def boundedMeshLearner {n k : ℕ} (m : ℕ) (G : Finset ℝ)
    (hG : ∀ x∈G, 0≤x) (μ μhi ℓ : ℝ) : RankLearner n k :=
  boundedGridLearner G hG (boundedGridMeshDenominator_positive n k m G μ) (μ/2) μhi ℓ

noncomputable def boundedMeshRate (n k m : ℕ) (G : Finset ℝ)
    (hG : ∀ x∈G, 0≤x) (μ μhi ℓ : ℝ) : ℝ :=
  boundedGridRate (n:=n) (k:=k) G hG (boundedGridMeshDenominator_positive n k m G μ) (μ/2) μhi ℓ

theorem boundedMeshLearner_guarantees_at_rate {n k m : ℕ} (G : Finset ℝ)
    (hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1) (hz : (0 : ℝ)∈G)
    (hm : 0<m) {μ : ℝ} (hμ : 0<μ) (μhi ℓ : ℝ) (P : Instance n)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) (hMean : μ≤P.expectedMaximum)
    (hUpper : P.expectedMaximum≤μhi) (hCount : P.positiveCount≤ℓ) :
    boundedMeshRate n k m G (fun x hx => (hBound x hx).1) μ μhi ℓ*P.expectedMaximum-1/(m : ℝ)^2 ≤
      (boundedMeshLearner (n:=n) (k:=k) m G (fun x hx => (hBound x hx).1) μ μhi ℓ).expectedReward P ∧
    ∀ i, boundedMeshRate n k m G (fun x hx => (hBound x hx).1) μ μhi ℓ-1/(m : ℝ)^2 ≤
      (boundedMeshLearner (n:=n) (k:=k) m G (fun x hx => (hBound x hx).1) μ μhi ℓ).reachProbability P i := by
  let N := boundedGridMeshDenominator n k m G μ
  have hN := boundedGridMeshDenominator_positive n k m G μ
  have hLoss := atomRoundingLoss_boundedGridMesh (k:=k) P G hz hm hμ
  have hLower : μ/2+P.atomRoundingLoss G N hz≤P.expectedMaximum := by
    linarith only [hLoss.1,hMean]
  have h := boundedGridLearner_rounding_transfer (k:=k) G hBound hN hz (μ/2) μhi ℓ P hG hLower hUpper hCount
  change boundedMeshRate n k m G (fun x hx => (hBound x hx).1) μ μhi ℓ*P.expectedMaximum-
      ((k : ℝ)+2)*P.atomRoundingLoss G N hz≤
        (boundedMeshLearner (n:=n) (k:=k) m G (fun x hx => (hBound x hx).1) μ μhi ℓ).expectedReward P ∧
    ∀ i, boundedMeshRate n k m G (fun x hx => (hBound x hx).1) μ μhi ℓ-
      ((k : ℝ)+1)*P.atomRoundingLoss G N hz≤
        (boundedMeshLearner (n:=n) (k:=k) m G (fun x hx => (hBound x hx).1) μ μhi ℓ).reachProbability P i at h
  constructor
  · linarith only [h.1,hLoss.2]
  · intro i
    have hd := P.atomRoundingLoss_nonnegative G hG N hN hz
    nlinarith only [h.2 i,hLoss.2,hd]

end ProphetSecretary.Statistics
