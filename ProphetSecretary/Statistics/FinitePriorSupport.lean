import ProphetSecretary.Statistics.FinitePriorGameExpectation

/-!
# Removing zero-weight atoms from a finite prior

Only positive-weight atoms are retained, without changing any Bayes payoff.
This permits a response theorem for one first-moment class to be applied to
an actual class-restricted posterior even when its original atom list also
contains zero-weight atoms outside that class.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

abbrev PositiveAtom (F : FinitePrior n) := {θ : Fin F.size // 0<F.weight θ}

noncomputable def positiveAtomEquiv (F : FinitePrior n) :
    Fin (Fintype.card F.PositiveAtom) ≃ F.PositiveAtom := (Fintype.equivFin F.PositiveAtom).symm

lemma sum_positiveAtoms (F : FinitePrior n) {A : Type*} [AddCommMonoid A]
    (f : Fin F.size → A) (hZero : ∀ θ, F.weight θ=0 → f θ=0) :
    (∑ θ : F.PositiveAtom, f θ)=∑ θ : Fin F.size, f θ := by
  have hOther : (∑ θ : {θ : Fin F.size // ¬0<F.weight θ}, f θ)=0 := by
    apply Finset.sum_eq_zero
    intro θ _
    exact hZero θ (le_antisymm (not_lt.mp θ.property) (show (0 : NNReal)≤F.weight θ from bot_le))
  have h := Fintype.sum_subtype_add_sum_subtype (fun θ : Fin F.size => 0<F.weight θ) f
  rw [hOther,add_zero] at h
  exact h

noncomputable def positivePrior (F : FinitePrior n) : FinitePrior n where
  size := Fintype.card F.PositiveAtom
  weight θ := F.weight (F.positiveAtomEquiv θ)
  weight_sum := by
    calc
      _ = ∑ θ : F.PositiveAtom, F.weight θ := Fintype.sum_equiv F.positiveAtomEquiv _ _ (fun _ => rfl)
      _ = ∑ θ : Fin F.size, F.weight θ := F.sum_positiveAtoms F.weight (fun _ h => h)
      _ = 1 := F.weight_sum
  offerInstance θ := F.offerInstance (F.positiveAtomEquiv θ)
  target θ := F.target (F.positiveAtomEquiv θ)

lemma positivePrior_weight_positive (F : FinitePrior n) (θ : Fin F.positivePrior.size) :
    0<F.positivePrior.weight θ := (F.positiveAtomEquiv θ).property

lemma sum_positivePrior_weighted (F : FinitePrior n) (g : Fin F.size → ℝ) :
    (∑ θ : Fin F.positivePrior.size, (F.positivePrior.weight θ : ℝ)*g (F.positiveAtomEquiv θ))=
      ∑ θ : Fin F.size, (F.weight θ : ℝ)*g θ := by
  change (∑ θ : Fin (Fintype.card F.PositiveAtom), (F.weight (F.positiveAtomEquiv θ) : ℝ)*g (F.positiveAtomEquiv θ))=_
  calc
    _ = ∑ θ : F.PositiveAtom, (F.weight θ : ℝ)*g θ := Fintype.sum_equiv F.positiveAtomEquiv _ _ (fun _ => rfl)
    _ = _ := F.sum_positiveAtoms (fun θ => (F.weight θ : ℝ)*g θ) (fun θ h => by rw [h,NNReal.coe_zero,zero_mul])

lemma positivePrior_supported (F : FinitePrior n) {Q : Instance n → Option (Fin n) → Prop}
    (hQ : ∀ θ, 0<F.weight θ → Q (F.offerInstance θ) (F.target θ)) :
    ∀ θ : Fin F.positivePrior.size, Q (F.positivePrior.offerInstance θ) (F.positivePrior.target θ) :=
  fun θ => hQ (F.positiveAtomEquiv θ) (F.positiveAtomEquiv θ).property

/-- Equality holds for the actual learner's full training and online payoff. -/
theorem positivePrior_targetGamePayoff (F : FinitePrior n) {d : ℕ} (L : Learner n d) (C : ℝ) :
    (∑ θ : Fin F.positivePrior.size, (F.positivePrior.weight θ : ℝ)*
      L.targetGamePayoff (F.positivePrior.offerInstance θ) (F.positivePrior.target θ) C)=
    ∑ θ : Fin F.size, (F.weight θ : ℝ)*L.targetGamePayoff (F.offerInstance θ) (F.target θ) C :=
  F.sum_positivePrior_weighted (fun θ => L.targetGamePayoff (F.offerInstance θ) (F.target θ) C)

end ProphetSecretary.Statistics.FinitePrior
