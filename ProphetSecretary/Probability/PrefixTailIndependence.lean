import ProphetSecretary.Probability.FiniteCoordinateIndependence
import Mathlib.Probability.Independence.InfinitePi

/-!
# Prefix--tail independence of an actual independent sequence

Finite disjoint coordinate independence is upgraded to the complete infinite
tail observation. The latter is constructed as independent auxiliary data for
causal omission simulation, rather than assumed as an interface.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

lemma indepFun_prefix_tail {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : ℕ → Ω → α}
    (hI : iIndepFun f P) (hf : ∀ i, Measurable (f i)) (N : ℕ) :
    IndepFun (fun ω => fun i : Fin N => f i.val ω) (fun ω => fun j : ℕ => f (j+N) ω) P := by
  apply indepFun_of_finite_coordinates (P := P)
    (X := fun ω => fun i : Fin N => f i.val ω) (Y := fun ω => fun j : ℕ => f (j+N) ω)
    (measurable_pi_lambda _ (fun i : Fin N => hf i.val)) (measurable_pi_lambda _ (fun j : ℕ => hf (j+N)))
  intro I J
  let S : Finset ℕ := I.image Fin.val
  let T : Finset ℕ := J.image (fun j => j+N)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro k hkS hkT
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hkS
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hkT
    have hin := i.isLt
    omega
  have hfinite := hI.indepFun_finset S T hd hf
  let left : (S → α) → I → α := fun z i => z ⟨i.val.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  let right : (T → α) → J → α := fun z j => z ⟨j.val+N,Finset.mem_image.mpr ⟨j.val,j.property,rfl⟩⟩
  have hleft : Measurable left := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hright : Measurable right := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hcomp := hfinite.comp hleft hright
  change IndepFun (fun ω => fun i : I => f i.val.val ω) (fun ω => fun j : J => f (j.val+N) ω) P at hcomp
  exact hcomp

end ProphetSecretary.Probability
