import ProphetSecretary.Probability.CenteredValueScore
import ProphetSecretary.Probability.WeakCenteredScore
import ProphetSecretary.Model.LawOrder
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform stop-loss convergence for weakly convergent bounded laws

Clipping the offer gives bounded continuous premium tests at every fixed
threshold. Their expectations are uniformly 1-Lipschitz in the threshold.
A finite cover of [0,H] upgrades weak convergence to uniform convergence;
outside that interval the premiums are either zero or affine with common
slope. Thus no optimizer sequence or non-atomic law assumption is used.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical
namespace ProphetSecretary.Probability

noncomputable def boundedStopLossTest (H : ℝ≥0) (q : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => max 0 (boundedOfferValue H x-q))
    (continuous_const.max ((boundedOfferValue H).continuous.sub continuous_const)) (H+|q|)
    (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
      apply max_le (by positivity)
      have hv := (boundedOfferValue_mem_range H x).2
      have hq := neg_le_abs q
      linarith)
noncomputable def clippedStopLoss (p : ProbabilityMeasure ℝ) (H : ℝ≥0) (q : ℝ) : ℝ :=
  ∫ x, boundedStopLossTest H q x ∂(p : Measure ℝ)

lemma clippedStopLoss_eq_stopLoss (p : ProbabilityMeasure ℝ) (H : ℝ≥0)
    (hcap : ∀ᵐ x ∂(p : Measure ℝ), x ∈ Icc (0 : ℝ) H) (q : ℝ) :
    clippedStopLoss p H q = Model.stopLoss (p : Measure ℝ) q := by
  apply integral_congr_ae
  filter_upwards [hcap] with x hx
  change max 0 (boundedOfferValue H x-q) = max 0 (x-q)
  rw [boundedOfferValue_eq H hx]

lemma boundedStopLossTest_lipschitz_threshold (H : ℝ≥0) (x q r : ℝ) :
    |boundedStopLossTest H q x-boundedStopLossTest H r x| ≤ |q-r| := by
  change |max 0 (boundedOfferValue H x-q)-max 0 (boundedOfferValue H x-r)| ≤ _
  have h := abs_max_sub_max_le_abs (boundedOfferValue H x-q) (boundedOfferValue H x-r) 0
  have he : boundedOfferValue H x-q-(boundedOfferValue H x-r) = -(q-r) := by ring
  simpa only [max_comm (boundedOfferValue H x-q) 0,max_comm (boundedOfferValue H x-r) 0,he,abs_neg] using h

lemma clippedStopLoss_lipschitz_threshold (p : ProbabilityMeasure ℝ) (H : ℝ≥0) (q r : ℝ) :
    |clippedStopLoss p H q-clippedStopLoss p H r| ≤ |q-r| := by
  unfold clippedStopLoss
  rw [← integral_sub ((boundedStopLossTest H q).integrable _) ((boundedStopLossTest H r).integrable _)]
  have h := norm_integral_le_of_norm_le_const (μ := (p : Measure ℝ))
    (f := fun x => boundedStopLossTest H q x-boundedStopLossTest H r x)
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using boundedStopLossTest_lipschitz_threshold H x q r)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using h

lemma clippedStopLoss_of_nonpos (p : ProbabilityMeasure ℝ) (H : ℝ≥0) {q : ℝ} (hq : q ≤ 0) :
    clippedStopLoss p H q = (∫ x, boundedOfferValue H x ∂(p : Measure ℝ))-q := by
  have heq : (fun x => boundedStopLossTest H q x) = fun x => boundedOfferValue H x-q := by
    funext x
    exact max_eq_right (sub_nonneg.mpr (hq.trans (boundedOfferValue_mem_range H x).1))
  unfold clippedStopLoss
  rw [heq,integral_sub ((boundedOfferValue H).integrable _) (integrable_const q)]
  simp only [integral_const,probReal_univ,one_smul]

lemma clippedStopLoss_of_ge (p : ProbabilityMeasure ℝ) (H : ℝ≥0) {q : ℝ} (hq : (H : ℝ) ≤ q) :
    clippedStopLoss p H q = 0 := by
  have heq : (fun x => boundedStopLossTest H q x) = fun _ => (0 : ℝ) := by
    funext x
    exact max_eq_left (sub_nonpos.mpr ((boundedOfferValue_mem_range H x).2.trans hq))
  unfold clippedStopLoss
  rw [heq,integral_zero]

lemma clippedStopLoss_difference_of_nonpos (p r : ProbabilityMeasure ℝ) (H : ℝ≥0)
    {q : ℝ} (hq : q ≤ 0) :
    clippedStopLoss p H q-clippedStopLoss r H q = clippedStopLoss p H 0-clippedStopLoss r H 0 := by
  rw [clippedStopLoss_of_nonpos p H hq,clippedStopLoss_of_nonpos r H hq,
    clippedStopLoss_of_nonpos p H le_rfl,clippedStopLoss_of_nonpos r H le_rfl]
  ring

lemma clippedStopLoss_tendsto {Γ : Type*} {l : Filter Γ} {ps : Γ → ProbabilityMeasure ℝ}
    {p : ProbabilityMeasure ℝ} (hp : Tendsto ps l (𝓝 p)) (H : ℝ≥0) (q : ℝ) :
    Tendsto (fun m => clippedStopLoss (ps m) H q) l (𝓝 (clippedStopLoss p H q)) :=
  centeredScore_mean_tendsto hp (boundedStopLossTest H q)

/-- Uniformity is over all real thresholds, not only a fixed finite grid. -/
theorem clippedStopLoss_tendstoUniformly {Γ : Type*} {l : Filter Γ} {ps : Γ → ProbabilityMeasure ℝ}
    {p : ProbabilityMeasure ℝ} (hp : Tendsto ps l (𝓝 p)) (H : ℝ≥0) :
    TendstoUniformly (fun m q => clippedStopLoss (ps m) H q) (clippedStopLoss p H) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨s,_hsCap,hsFinite,hsCover⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) H)).finite_cover_balls (show 0 < ε/4 by positivity)
  letI : Fintype s := hsFinite.fintype
  have heach (q : s) : ∀ᶠ m in l, |clippedStopLoss (ps m) H q-clippedStopLoss p H q| < ε/2 := by
    simpa only [Real.dist_eq] using
      Metric.tendsto_nhds.mp (clippedStopLoss_tendsto hp H q) (ε/2) (by positivity)
  filter_upwards [eventually_all.mpr heach] with m hm
  have hWindow (q : ℝ) (hq : q ∈ Icc (0 : ℝ) H) :
      |clippedStopLoss (ps m) H q-clippedStopLoss p H q| < ε := by
    obtain ⟨r,hr,hrq⟩ := Set.mem_iUnion₂.mp (hsCover hq)
    have hdist : |q-r| < ε/4 := by simpa only [Metric.mem_ball,Real.dist_eq] using hrq
    have hnear := hm ⟨r,hr⟩
    have hleft := clippedStopLoss_lipschitz_threshold (ps m) H q r
    have hright := clippedStopLoss_lipschitz_threshold p H r q
    rw [abs_sub_comm r q] at hright
    have htriangle := abs_sub_le (clippedStopLoss (ps m) H q) (clippedStopLoss (ps m) H r) (clippedStopLoss p H q)
    have htriangle' := abs_sub_le (clippedStopLoss (ps m) H r) (clippedStopLoss p H r) (clippedStopLoss p H q)
    linarith only [hnear,hdist,hleft,hright,htriangle,htriangle']
  intro q
  rw [dist_comm,Real.dist_eq]
  by_cases hq0 : q ≤ 0
  · rw [clippedStopLoss_difference_of_nonpos (ps m) p H hq0]
    exact hWindow 0 ⟨le_rfl,H.coe_nonneg⟩
  · by_cases hqH : (H : ℝ) ≤ q
    · rw [clippedStopLoss_of_ge (ps m) H hqH,clippedStopLoss_of_ge p H hqH,sub_self,abs_zero]
      exact hε
    · exact hWindow q ⟨(not_le.mp hq0).le,(not_le.mp hqH).le⟩

/-- Actual cap-supported stop-loss transforms converge uniformly under weak
law convergence. Arbitrary atoms and zero-valued laws are included. -/
theorem stopLoss_tendstoUniformly_of_bounded {Γ : Type*} {l : Filter Γ}
    {ps : Γ → ProbabilityMeasure ℝ} {p : ProbabilityMeasure ℝ} (hp : Tendsto ps l (𝓝 p)) (H : ℝ≥0)
    (hps : ∀ m, ∀ᵐ x ∂(ps m : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hpCap : ∀ᵐ x ∂(p : Measure ℝ), x ∈ Icc (0 : ℝ) H) :
    TendstoUniformly (fun m q => Model.stopLoss (ps m : Measure ℝ) q) (Model.stopLoss (p : Measure ℝ)) l := by
  have hs : (fun m q => Model.stopLoss (ps m : Measure ℝ) q) = fun m q => clippedStopLoss (ps m) H q := by
    funext m q
    exact (clippedStopLoss_eq_stopLoss (ps m) H (hps m) q).symm
  have h : Model.stopLoss (p : Measure ℝ) = clippedStopLoss p H := by
    funext q
    exact (clippedStopLoss_eq_stopLoss p H hpCap q).symm
  rw [hs,h]
  exact clippedStopLoss_tendstoUniformly hp H

end ProphetSecretary.Probability
