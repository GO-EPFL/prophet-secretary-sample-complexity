import ProphetSecretary.Statistics.PlannerWeights

/-!
# Cancellation in the weighted planner recursion

The kernel's child weight cancels the normalization of the child payoff.
The remaining coefficient is the original positive probability divided by
the parent weight, as required by `alg:weighted-recursion`.
-/

namespace ProphetSecretary.Statistics

variable {ι : Type*} [DecidableEq ι]

lemma plannerKernelWeight_cancel (A : Finset ι) (p : ι → ℝ)
    (hA : A.Nonempty) (hp : ∀ j ∈ A, 0 < p j) (i : ι) (B : Finset ι)
    (hB : B ⊆ A) (s : ℝ) :
    plannerContraction A p * (plannerKernelDensity A p i B s / plannerWeight B p) =
      (p i / plannerWeight A p) * s^B.card * (1-s)^((A.erase i).card-B.card) := by
  have hβ : plannerWeight A p ≠ 0 :=
    (plannerWeight_pos A p (fun j hj => (hp j hj).le)).ne'
  have hδ : plannerWeight A p - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (one_lt_plannerWeight A p hA hp))
  have hβB : plannerWeight B p ≠ 0 :=
    (plannerWeight_pos B p (fun j hj => (hp j (hB hj)).le)).ne'
  unfold plannerContraction plannerKernelDensity
  field_simp

lemma plannerKernelWeight_cancel_gain (A : Finset ι) (p : ι → ℝ)
    (hA : A.Nonempty) (hp : ∀ j ∈ A, 0 < p j) (i : ι) (B : Finset ι)
    (hB : B ⊆ A) (s g : ℝ) :
    plannerContraction A p * plannerKernelDensity A p i B s * (g / plannerWeight B p) =
      (p i / plannerWeight A p) * s^B.card * (1-s)^((A.erase i).card-B.card) * g := by
  calc
    _ = (plannerContraction A p * (plannerKernelDensity A p i B s / plannerWeight B p))*g := by ring
    _ = _ := by rw [plannerKernelWeight_cancel A p hA hp i B hB s]

end ProphetSecretary.Statistics
