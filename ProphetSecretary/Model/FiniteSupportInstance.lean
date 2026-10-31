import ProphetSecretary.Model.FiniteAlphabetInstance
import ProphetSecretary.Model.Continuation
import ProphetSecretary.Probability.FiniteSupportLaw

/-!
# Finite-support instances and the finite alphabet representation

The independent instance obtained from each marginal's actual singleton
masses is the original instance itself. The fixed alphabet may include
zero-probability atoms, in particular the cap and zero.
-/

open MeasureTheory Set
namespace ProphetSecretary.Model
open ProphetSecretary.Probability

variable {n : ℕ}

lemma finiteSupportInstance_eq (P : Instance n) (G : Finset ℝ) (hNonneg : ∀ x∈G, 0≤x)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) :
    finiteAlphabetInstance (fun a : G => a.val) (fun a => hNonneg a.val a.property)
      (fun i a => (P.law i).real {a.val}) (fun i => finiteSupport_weights_simplex (P.law i) G (hG i))=P := by
  apply Instance.eq_of_law_eq
  funext i
  exact finiteSupport_map_law (P.law i) G (hG i)

end ProphetSecretary.Model
