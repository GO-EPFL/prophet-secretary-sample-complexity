import ProphetSecretary.Analysis.PolynomialWorkBound
import ProphetSecretary.Statistics.BinaryScalarQuery

/-!
# Polynomial closure of binary scalar work

The scalar query bound is a polynomial in its public dimensions, input
heights, precision, number of copies, and full tree factor.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

private lemma binaryQueryWorkAdd {α : Type*} {N F G : α → ℕ}
    [Fact (∀ x, 0<N x)] (hF : HasPolynomialWorkBound N F) (hG : HasPolynomialWorkBound N G) :
    HasPolynomialWorkBound N (fun x => F x+G x) :=
  HasPolynomialWorkBound.add Fact.out hF hG

local infixl:65 " +ₚ " => binaryQueryWorkAdd
local infixl:70 " *ₚ " => HasPolynomialWorkBound.mul
local infixr:80 " ^ₚ " => HasPolynomialWorkBound.pow

theorem binaryScalarQueryWorkBound_polynomial {α : Type*} {N n m Y M U Z b R a : α → ℕ}
    (hN : ∀ x, 0<N x) (hn : HasPolynomialWorkBound N n) (hm : HasPolynomialWorkBound N m)
    (hY : HasPolynomialWorkBound N Y) (hM : HasPolynomialWorkBound N M)
    (hU : HasPolynomialWorkBound N U) (hZ : HasPolynomialWorkBound N Z)
    (hb : HasPolynomialWorkBound N b) (ha : HasPolynomialWorkBound N a)
    (hExp : HasPolynomialWorkBound N (fun x => (16:ℕ)^R x)) :
    HasPolynomialWorkBound N (fun x => binaryScalarQueryWorkBound (n x) (m x) (Y x) (M x)
      (U x) (Z x) (b x) (R x) (a x)) := by
  letI : Fact (∀ x, 0<N x) := ⟨hN⟩
  let c := HasPolynomialWorkBound.const N
  have hr : HasPolynomialWorkBound N R :=
    hExp.of_le (fun x => (Nat.lt_two_pow_self (n:=R x)).le.trans
      (Nat.pow_le_pow_left (by decide : 2≤16) _))
  have hF : HasPolynomialWorkBound N (fun x => (4:ℕ)^R x) :=
    hExp.of_le (fun _ => Nat.pow_le_pow_left (by decide) _)
  have hn1 := hn +ₚ c 1
  have hP := c 2 *ₚ hM
  have hW := hn *ₚ (hP +ₚ c 3)
  have hRow := c 1 +ₚ hm *ₚ (c 3400 *ₚ (hY +ₚ c 2) ^ₚ 3 +ₚ c 5) +ₚ
    c 2 *ₚ (c 1 +ₚ c 2 *ₚ hm) +ₚ c 3600 *ₚ (hM +ₚ c 2) ^ₚ 3 +ₚ c 10
  have hA := c 1 +ₚ hn *ₚ (c 3400 *ₚ (hP +ₚ c 2) ^ₚ 3 +ₚ c 5)
  have hWeight := c 1 +ₚ hn *ₚ (c 3 *ₚ (c 3600 *ₚ (hW +ₚ hP +ₚ c 5) ^ₚ 3) +ₚ c 5)
  have hFrame := hA +ₚ hWeight +ₚ c 9 *ₚ
    (c 3600 *ₚ (hU +ₚ hZ +ₚ c 2 *ₚ hW +ₚ hP +ₚ c 10 +ₚ c 2) ^ₚ 3) +ₚ c 24
  have hTime := hU +ₚ hr *ₚ hb
  have hPrimitive := hZ +ₚ hU +ₚ hr *ₚ hb +ₚ c 2 *ₚ hW +ₚ hm *ₚ (hY +ₚ c 1) +ₚ c 2 *ₚ hM +ₚ c 5
  have hE := c 64 *ₚ (hPrimitive +ₚ hr +ₚ c 1) *ₚ hExp
  have hOperand := hU +ₚ hr *ₚ hb +ₚ hZ +ₚ c 4 *ₚ hW +ₚ hm *ₚ (hY +ₚ c 1) +ₚ
    c 2 *ₚ hM +ₚ hE +ₚ c 11
  have hFrameChild := hA +ₚ hWeight +ₚ c 9 *ₚ
    (c 3600 *ₚ (hTime +ₚ hZ +ₚ c 2 *ₚ hW +ₚ hP +ₚ c 10 +ₚ c 2) ^ₚ 3) +ₚ c 24
  have hSamplerSize := c 100 *ₚ hn1 ^ₚ 3
  have hLiteral := (hP +ₚ hb) +ₚ hn +ₚ c 2
  have hSamD := (hLiteral +ₚ c 1) *ₚ hSamplerSize
  have hSamUnit := (hSamplerSize +ₚ hSamplerSize *ₚ (c 3500 *ₚ (hSamD +ₚ c 2) ^ₚ 3) +ₚ
    c 3400 *ₚ (hSamD +ₚ c 2) ^ₚ 3 +ₚ c 5) +ₚ c 100 *ₚ (hSamD +ₚ c 1 +ₚ c 1) ^ₚ 3 +ₚ
    c 2 *ₚ hn +ₚ c 10
  have hSampler := (c 1 +ₚ c 2 *ₚ hn) +ₚ (c 1 +ₚ hn *ₚ hSamUnit) +ₚ
    (c 1 +ₚ hn *ₚ (hSamUnit +ₚ c 3)) +ₚ (c 1 +ₚ c 2 *ₚ hn) +ₚ (c 1 +ₚ hn *ₚ hSamUnit) +ₚ hSamUnit +ₚ
    (c 1 +ₚ hn *ₚ (hSamUnit +ₚ c 3)) +ₚ (c 1 +ₚ c 3 *ₚ hn) +ₚ (c 1 +ₚ c 2 *ₚ hn) +ₚ c 10
  have hCoordinates := c 3 *ₚ hn +ₚ c 2
  have hSeed := hCoordinates *ₚ (c 2 *ₚ hb +ₚ c 100 *ₚ (hb +ₚ c 2) ^ₚ 3 +ₚ c 5) +ₚ c 15 *ₚ hn1
  have hEV := hW +ₚ hE
  have hEx := hm *ₚ (hY +ₚ c 1) +ₚ c 2 *ₚ hM +ₚ hEV +ₚ c 1
  have hS := hm *ₚ (hY +ₚ c 1) +ₚ hM +ₚ hEV +ₚ hY +ₚ c 4
  have hPay := hA +ₚ hWeight +ₚ c 2 *ₚ
    (c 3600 *ₚ (hEx +ₚ hW +ₚ hE +ₚ c 2) ^ₚ 3) +ₚ
    (c 4 +ₚ hm *ₚ (c 5 *ₚ (c 3500 *ₚ (hS +ₚ c 1) ^ₚ 3) +ₚ c 12) +ₚ c 3300 *ₚ (hS +ₚ c 1) ^ₚ 3) +ₚ
    c 100 *ₚ (hEx +ₚ c 2) ^ₚ 3 +ₚ c 4 *ₚ hm +ₚ c 10
  have hCallback := hFrameChild +ₚ hSampler +ₚ hSeed +ₚ c 3 *ₚ
    (c 3600 *ₚ (hTime +ₚ hb +ₚ c 2) ^ₚ 3) +ₚ c 8 +ₚ hPay +ₚ c 20
  have hTreeA := c 2 *ₚ hOperand +ₚ c 2 *ₚ hr +ₚ c 5
  have hTreeQ := hF *ₚ (hTreeA +ₚ c 1) +ₚ c 2 *ₚ hr
  have hTreeU := hOperand +ₚ hTreeQ +ₚ hr *ₚ (hTreeQ +ₚ c 1) +ₚ c 3
  have hTreeW := c 2 *ₚ (hF +ₚ hr) +ₚ c 11
  have hTreeM := hTreeW *ₚ (c 3600 *ₚ ((hTreeU +ₚ c 1) *ₚ hTreeW +ₚ c 2) ^ₚ 3)
  have hTreeC := c 3600 *ₚ (hTreeU +ₚ c 2) ^ₚ 3
  have hTreeUnit := hCallback +ₚ hF *ₚ (c 2 *ₚ hCallback +ₚ c 2) +ₚ c 8 *ₚ hF +ₚ c 4 +ₚ hTreeM +ₚ
    (c 8 *ₚ hr +ₚ c 4 +ₚ hTreeM) +ₚ
    hr *ₚ (hF *ₚ (c 4 *ₚ hCallback +ₚ hTreeC +ₚ c 6) +ₚ c 8 *ₚ hF +ₚ c 4 +ₚ hTreeM) +ₚ hTreeM +ₚ c 8
  have hV := hW +ₚ hE +ₚ hU +ₚ hZ +ₚ c 3
  have hCub := c 3600 *ₚ (hV +ₚ c 2) ^ₚ 3
  have hSingle := hTreeUnit *ₚ (c 4 *ₚ hExp) +ₚ hCub +ₚ c 3
  have hCopies := c 2 *ₚ ha +ₚ c 1
  have hCopies1 := c 2 *ₚ ha +ₚ c 2
  exact
    hn *ₚ hRow +ₚ c 3 *ₚ hn +ₚ c 1 +ₚ hFrame +ₚ c 2 *ₚ hCopies1 ^ₚ 2 *ₚ
      (c 3400 *ₚ (hV +ₚ c 2) ^ₚ 3 +ₚ c 5) +ₚ hCopies *ₚ hSingle +ₚ c 6 *ₚ hCopies1 +ₚ c 2 +ₚ
    c 2 *ₚ hCub +ₚ c 7

end ProphetSecretary.Statistics
