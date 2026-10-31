import ProphetSecretary.Model.EmpiricalCapPolicy
import ProphetSecretary.Model.TrainingZeroSimulation
import ProphetSecretary.Statistics.FinitePriorLearner
import ProphetSecretary.Reach.MarkovStrict

/-!
# An empirical policy on a selected training block

The scalar selector can use the entire visible training observation, while
the empirical law uses the specified block. The generic prefix learner
implements this callback from exactly the observed prefix; its ONLINE
column is never requested. Statistical independence of the chosen block
is a separate product-law obligation.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model FinitePrior

variable {n m N : ℕ} {Seed : Type} [MeasurableSpace Seed]

def empiricalBlockRead (e : Fin m → Fin (N+1)) (a : ValueArray n N) : Reservoir n m :=
  fun i j => a (i,e j)

lemma measurable_empiricalBlockRead (e : Fin m → Fin (N+1)) : Measurable (empiricalBlockRead (n:=n) e) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_lambda _ (fun j => measurable_pi_apply (i,e j))

def empiricalBlockSeedMap (e : Fin m → Fin (N+1)) (p : ValueArray n N × Seed) :
    Reservoir n m × (ValueArray n N × Seed) := (empiricalBlockRead e p.1,p)

lemma measurable_empiricalBlockSeedMap (e : Fin m → Fin (N+1)) :
    Measurable (empiricalBlockSeedMap (n:=n) (Seed:=Seed) e) :=
  ((measurable_empiricalBlockRead e).comp measurable_fst).prodMk measurable_id

variable [NeZero m]

noncomputable def empiricalBlockPolicy (e : Fin m → Fin (N+1)) (Z : ValueArray n N × Seed → ℝ) :
    Policy (ValueArray n N × Seed) n :=
  (empiricalCapSelectedPolicy (fun q : Reservoir n m × (ValueArray n N × Seed) => Z q.2)).comapSeed
    (empiricalBlockSeedMap e)

lemma empiricalBlockPolicy_isMeasurable (e : Fin m → Fin (N+1))
    {Z : ValueArray n N × Seed → ℝ} (hZ : Measurable Z) : (empiricalBlockPolicy e Z).IsMeasurable :=
  Policy.comapSeed_isMeasurable (measurable_empiricalBlockSeedMap e)
    (empiricalCapSelectedPolicy (fun q : Reservoir n m × (ValueArray n N × Seed) => Z q.2))
    (empiricalCapSelectedPolicy_isMeasurable (hZ.comp measurable_snd))

omit [MeasurableSpace Seed] in
lemma empiricalBlockPolicy_decide (e : Fin m → Fin (N+1)) (Z : ValueArray n N × Seed → ℝ)
    (p : ValueArray n N × Seed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (empiricalBlockPolicy e Z).decide p t i x H =
      decide (0<x ∧ empiricalCapThreshold (empiricalBlockRead e p.1) (Z p) (unseen H) t i≤x) := rfl

omit [MeasurableSpace Seed] in
lemma empiricalBlockPolicy_accepts_cap (e : Fin m → Fin (N+1)) (Z : ValueArray n N × Seed → ℝ)
    (p : ValueArray n N × Seed) {t : ℝ} (ht : 0≤t) (hz0 : 0≤Z p) (hz : Z p≤1/4)
    (i : Fin n) (H : History n) : (empiricalBlockPolicy e Z).decide p t i 1 H=true :=
  empiricalCapSelectedPolicy_accepts_one (fun q : Reservoir n m × (ValueArray n N × Seed) => Z q.2) (empiricalBlockSeedMap e p) ht hz0 hz i H

omit [MeasurableSpace Seed] in
lemma empiricalBlockPolicy_rejects_zero (e : Fin m → Fin (N+1)) (Z : ValueArray n N × Seed → ℝ)
    (p : ValueArray n N × Seed) (t : ℝ) (i : Fin n) (H : History n) :
    (empiricalBlockPolicy e Z).decide p t i 0 H=false :=
  empiricalCapSelectedPolicy_rejects_zero (fun q : Reservoir n m × (ValueArray n N × Seed) => Z q.2) (empiricalBlockSeedMap e p) t i H

omit [MeasurableSpace Seed] in
lemma empiricalBlockPolicy_deletionMonotone (e : Fin m → Fin (N+1)) (Z : ValueArray n N × Seed → ℝ) :
    DeletionMonotoneAcceptance (fun p A t i x =>
      decide (0<x ∧ empiricalCapThreshold (empiricalBlockRead e p.1) (Z p) A t i≤x)) := by
  intro p t ht i x hx A B hi hAB hAccept
  exact empiricalCapSelectedPolicy_deletionMonotone (fun q : Reservoir n m × (ValueArray n N × Seed) => Z q.2)
    (empiricalBlockSeedMap e p) t ht i x hx A B hi hAB hAccept

theorem empiricalBlockPolicy_meanDuration_le_reach (e : Fin m → Fin (N+1))
    {Z : ValueArray n N × Seed → ℝ} (hZ : Measurable Z)
    (P : Instance n) (D : Measure (ValueArray n N × Seed)) [IsProbabilityMeasure D] (i : Fin n) :
    (empiricalBlockPolicy e Z).meanDuration P D≤(empiricalBlockPolicy e Z).reachProbability P D i :=
  markovPolicy.meanDuration_le_reachProbability _ (empiricalBlockPolicy_deletionMonotone e Z)
    (empiricalBlockPolicy_isMeasurable e hZ) P D i

end ProphetSecretary.Statistics
