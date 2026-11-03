import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Combining polynomial work estimates

Each estimate uses an explicit coefficient and exponent. The closure
lemmas combine those witnesses without expanding powers of the input size.
-/

namespace ProphetSecretary.Analysis

def HasPolynomialWorkBound {α : Type*} (size work : α → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ x, work x≤C*(size x)^d

namespace HasPolynomialWorkBound

variable {α : Type*} {N F G : α → ℕ}

lemma const (N : α → ℕ) (c : ℕ) :
    HasPolynomialWorkBound N (fun _ => c) :=
  ⟨c,0,fun _ => by simp⟩

lemma size (N : α → ℕ) : HasPolynomialWorkBound N N :=
  ⟨1,1,fun _ => by simp⟩

lemma of_le (h : HasPolynomialWorkBound N G) (hFG : ∀ x, F x≤G x) :
    HasPolynomialWorkBound N F := by
  obtain ⟨C,d,h⟩ := h
  exact ⟨C,d,fun x => (hFG x).trans (h x)⟩

lemma add (hN : ∀ x, 0<N x) (hF : HasPolynomialWorkBound N F) (hG : HasPolynomialWorkBound N G) :
    HasPolynomialWorkBound N (fun x => F x+G x) := by
  obtain ⟨C,d,hF⟩ := hF
  obtain ⟨D,e,hG⟩ := hG
  refine ⟨C+D,max d e,fun x => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((hF x).trans (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (hN x) (le_max_left _ _))))
    ((hG x).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right (hN x) (le_max_right _ _))))

lemma mul (hF : HasPolynomialWorkBound N F) (hG : HasPolynomialWorkBound N G) :
    HasPolynomialWorkBound N (fun x => F x*G x) := by
  obtain ⟨C,d,hF⟩ := hF
  obtain ⟨D,e,hG⟩ := hG
  refine ⟨C*D,d+e,fun x => ?_⟩
  calc
    _ ≤ (C*(N x)^d)*(D*(N x)^e) := Nat.mul_le_mul (hF x) (hG x)
    _ = _ := by rw [pow_add]; ac_rfl

lemma pow (hF : HasPolynomialWorkBound N F) (k : ℕ) :
    HasPolynomialWorkBound N (fun x => (F x)^k) := by
  obtain ⟨C,d,hF⟩ := hF
  refine ⟨C^k,d*k,fun x => ?_⟩
  calc
    _ ≤ (C*(N x)^d)^k := Nat.pow_le_pow_left (hF x) k
    _ = _ := by rw [mul_pow,pow_mul]

lemma of_real_bound (C : ℝ) (d : ℕ) (h : ∀ x, (F x : ℝ)≤C*(N x : ℝ)^d) :
    HasPolynomialWorkBound N F := by
  refine ⟨⌈C⌉₊,d,fun x => ?_⟩
  have h' := (h x).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity : (0 : ℝ)≤(N x : ℝ)^d))
  exact_mod_cast h'

end HasPolynomialWorkBound

end ProphetSecretary.Analysis
