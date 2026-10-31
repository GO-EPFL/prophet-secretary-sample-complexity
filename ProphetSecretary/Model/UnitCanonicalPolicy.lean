import ProphetSecretary.Model.BellmanOptimal

/-!
# Canonical scalar policies at normalized endpoint weights

For a positive reward coefficient this is the actual continuation-threshold
policy. At zero reward weight it waits until the end, which attains the
optimal duration objective. Both branches use independent trivial randomness.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def Instance.unitCanonicalPolicy (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (lam : ℝ) (hlam : lam∈Icc (0:ℝ) 1) : RandomizedPolicy n :=
  if h : 0<lam then P.valuePolicy hP h.le (sub_nonneg.mpr hlam.2) else RandomizedPolicy.waiting n

lemma Instance.unitCanonicalPolicy_eq_valuePolicy (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam : ℝ} (hlam : lam∈Icc (0:ℝ) 1) (hPos : 0<lam) :
    P.unitCanonicalPolicy hP lam hlam=P.valuePolicy hP hlam.1 (sub_nonneg.mpr hlam.2) := by
  exact dif_pos hPos

theorem Instance.unitCanonicalPolicy_optimal (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (lam : ℝ) (hlam : lam∈Icc (0:ℝ) 1) :
    (P.unitCanonicalPolicy hP lam hlam).scalarObjective P lam (1-lam)=optimalScalarValue P lam (1-lam) := by
  by_cases hPos : 0<lam
  · rw [P.unitCanonicalPolicy_eq_valuePolicy hP hlam hPos]
    exact P.valuePolicy_optimal hP hPos (sub_nonneg.mpr hlam.2)
  · have hZero : lam=0 := le_antisymm (not_lt.mp hPos) hlam.1
    have hPolicy : P.unitCanonicalPolicy hP lam hlam=RandomizedPolicy.waiting n := dif_neg hPos
    rw [hPolicy,RandomizedPolicy.waiting_scalarObjective,hZero]
    exact (optimalScalarValue_zero_rewardWeight P (by norm_num : (0:ℝ)≤1-0)).symm
end ProphetSecretary.Model
