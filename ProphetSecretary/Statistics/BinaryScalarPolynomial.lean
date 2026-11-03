import ProphetSecretary.Statistics.BinaryFairBankCall
import ProphetSecretary.Analysis.PolynomialWorkBound

/-!
# Polynomial dependence of the measured scalar bit work

The exponential term is isolated as (16^R). Once that term is bounded,
all scalar tree, sampler, row scan, median and binary normalization costs
are polynomials of the supplied dimension and operand-width parameters.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

variable {α : Type*} {N : α → ℕ}

private lemma add_bound {F G : α → ℕ} [Fact (∀ x, 0<N x)]
    (hF : HasPolynomialWorkBound N F) (hG : HasPolynomialWorkBound N G) :
    HasPolynomialWorkBound N (fun x => F x+G x) :=
  HasPolynomialWorkBound.add Fact.out hF hG

local infixl:65 " +ₚ " => add_bound
local infixl:70 " *ₚ " => HasPolynomialWorkBound.mul
local infixr:80 " ^ₚ " => HasPolynomialWorkBound.pow

theorem binaryScalarBudgets_polynomial (hN : ∀ x, 0<N x)
    {n m Y M U Z b R a H : α → ℕ}
    (hn : HasPolynomialWorkBound N n) (hm : HasPolynomialWorkBound N m)
    (hY : HasPolynomialWorkBound N Y) (hM : HasPolynomialWorkBound N M)
    (hU : HasPolynomialWorkBound N U) (hZ : HasPolynomialWorkBound N Z)
    (hb : HasPolynomialWorkBound N b) (hR : HasPolynomialWorkBound N R)
    (ha : HasPolynomialWorkBound N a) (hH : HasPolynomialWorkBound N H)
    (hExp : HasPolynomialWorkBound N (fun x => (16 : ℕ)^(R x))) :
    HasPolynomialWorkBound N (fun x => binaryScalarQueryWorkBound
      (n x) (m x) (Y x) (M x) (U x) (Z x) (b x) (R x) (a x)) ∧
    HasPolynomialWorkBound N (fun x => binaryFairBankWorkBound
      (n x) (m x) (Y x) (M x) (U x) (Z x) (b x) (R x) (a x) (H x)) ∧
    HasPolynomialWorkBound N (fun x => finiteFairBankOutputHeight
      (n x) (m x) (Y x) (M x) (U x) (Z x) (b x) (R x)) := by
  letI : Fact (∀ x, 0<N x) := ⟨hN⟩
  let c := HasPolynomialWorkBound.const N
  let op {D : α → ℕ} (hD : HasPolynomialWorkBound N D) :
      HasPolynomialWorkBound N (fun x => 3600*(D x+2)^3) :=
    c 3600 *ₚ (hD +ₚ c 2) ^ₚ 3
  have hF : HasPolynomialWorkBound N (fun x => (4 : ℕ)^(R x)) :=
    hExp.of_le (fun _ => Nat.pow_le_pow_left (by decide) _)
  have hn1 := hn +ₚ c 1
  have hp := c 2 *ₚ hM
  have hW := hn *ₚ (hp +ₚ c 3)
  have hYsum := hm *ₚ (hY +ₚ c 1)
  have hTime := hU +ₚ hR *ₚ hb
  have hPrim : HasPolynomialWorkBound N
      (fun x => plannerPrimitiveHeight (n x) (m x) (Y x) (M x) (2*M x) (U x) (Z x) (b x) (R x)) :=
    hZ +ₚ hU +ₚ hR *ₚ hb +ₚ c 2 *ₚ hW +ₚ hYsum +ₚ c 2 *ₚ hM +ₚ c 5
  have hVal : HasPolynomialWorkBound N
      (fun x => binaryEmpiricalValueHeight (n x) (m x) (Y x) (M x) (2*M x) (U x) (Z x) (b x) (R x)) :=
    c 64 *ₚ (hPrim +ₚ hR +ₚ c 1) *ₚ hExp
  have hArg : HasPolynomialWorkBound N
      (fun x => binaryEmpiricalOperandHeight (n x) (m x) (Y x) (M x) (2*M x) (U x) (Z x) (b x) (R x)) :=
    hU +ₚ hR *ₚ hb +ₚ hZ +ₚ c 4 *ₚ hW +ₚ hYsum +ₚ c 2 *ₚ hM +ₚ hVal +ₚ c 11
  let hFilter := c 1 +ₚ hn *ₚ (c 3400 *ₚ (hp +ₚ c 2) ^ₚ 3 +ₚ c 5)
  let hWeight := c 1 +ₚ hn *ₚ (c 3 *ₚ op (hW +ₚ hp +ₚ c 3) +ₚ c 5)
  let frame {A : α → ℕ} (hA : HasPolynomialWorkBound N A) :
      HasPolynomialWorkBound N (fun x => binaryFrameWorkBound (n x) (2*M x) (A x) (Z x)) :=
    hFilter +ₚ hWeight +ₚ c 9 *ₚ op (hA +ₚ hZ +ₚ c 2 *ₚ hW +ₚ hp +ₚ c 10) +ₚ c 24
  have hPayV := hW +ₚ hVal
  have hPayE := hYsum +ₚ c 2 *ₚ hM +ₚ hPayV +ₚ c 1
  have hPayS := hYsum +ₚ hM +ₚ hPayV +ₚ hY +ₚ c 4
  have hPay : HasPolynomialWorkBound N (fun x =>
      binaryPayoffWorkBound (n x) (m x) (2*M x) (M x) (Y x)
        (binaryEmpiricalValueHeight (n x) (m x) (Y x) (M x) (2*M x) (U x) (Z x) (b x) (R x))) :=
    hFilter +ₚ hWeight +ₚ c 2 *ₚ op (hPayE +ₚ hW +ₚ hVal) +ₚ
      (c 4 +ₚ hm *ₚ (c 5 *ₚ (c 3500 *ₚ (hPayS +ₚ c 1) ^ₚ 3) +ₚ c 12) +ₚ
        c 3300 *ₚ (hPayS +ₚ c 1) ^ₚ 3) +ₚ c 100 *ₚ (hPayE +ₚ c 2) ^ₚ 3 +ₚ c 4 *ₚ hm +ₚ c 10
  have hSamplerW := c 100 *ₚ hn1 ^ₚ 3
  have hSamplerB := (hp +ₚ hb) +ₚ hn +ₚ c 2
  have hSamplerD := (hSamplerB +ₚ c 1) *ₚ hSamplerW +ₚ c 1
  have hSamplerQ := ((hSamplerB +ₚ c 1) *ₚ hSamplerW +ₚ c 2) ^ₚ 3
  have hSamplerUnit := (hSamplerW +ₚ hSamplerW *ₚ (c 3500 *ₚ hSamplerQ) +ₚ c 3400 *ₚ hSamplerQ +ₚ c 5) +ₚ
    c 100 *ₚ (hSamplerD +ₚ c 1) ^ₚ 3 +ₚ c 2 *ₚ hn +ₚ c 10
  have hSampler : HasPolynomialWorkBound N (fun x => binarySamplerWorkBound (n x) (2*M x+b x)) :=
    (c 1 +ₚ c 2 *ₚ hn) +ₚ (c 1 +ₚ hn *ₚ hSamplerUnit) +ₚ
      (c 1 +ₚ hn *ₚ (hSamplerUnit +ₚ c 3)) +ₚ (c 1 +ₚ c 2 *ₚ hn) +ₚ
      (c 1 +ₚ hn *ₚ hSamplerUnit) +ₚ hSamplerUnit +ₚ
      (c 1 +ₚ hn *ₚ (hSamplerUnit +ₚ c 3)) +ₚ (c 1 +ₚ c 3 *ₚ hn) +ₚ
      (c 1 +ₚ c 2 *ₚ hn) +ₚ c 10
  have hSeed : HasPolynomialWorkBound N (fun x => binaryFairSeedWorkBound (n x) (b x)) :=
    (c 3 *ₚ hn +ₚ c 2) *ₚ (c 2 *ₚ hb +ₚ c 100 *ₚ (hb +ₚ c 2) ^ₚ 3 +ₚ c 5) +ₚ c 15 *ₚ hn1
  have hCallback : HasPolynomialWorkBound N (fun x => binaryEmpiricalCallbackWork
      (n x) (m x) (Y x) (M x) (2*M x) (U x) (Z x) (b x) (R x)) :=
    frame hTime +ₚ hSampler +ₚ hSeed +ₚ c 3 *ₚ op (hU +ₚ hR *ₚ hb +ₚ hb) +ₚ c 8 +ₚ hPay +ₚ c 20
  have hA := c 2 *ₚ hArg +ₚ c 2 *ₚ hR +ₚ c 5
  have hQ := hF *ₚ (hA +ₚ c 1) +ₚ c 2 *ₚ hR
  have hX := hArg +ₚ hQ +ₚ hR *ₚ (hQ +ₚ c 1) +ₚ c 3
  have hWarr := c 2 *ₚ (hF +ₚ hR) +ₚ c 11
  have hMem := hWarr *ₚ op ((hX +ₚ c 1) *ₚ hWarr)
  have hTree : HasPolynomialWorkBound N (fun x => binaryEmpiricalTreeWorkBound
      (n x) (m x) (Y x) (M x) (2*M x) (U x) (Z x) (b x) (R x)) :=
    (hCallback +ₚ hF *ₚ (c 2 *ₚ hCallback +ₚ c 2) +ₚ c 8 *ₚ hF +ₚ c 4 +ₚ hMem +ₚ
      (c 8 *ₚ hR +ₚ c 4 +ₚ hMem) +ₚ
      hR *ₚ (hF *ₚ (c 4 *ₚ hCallback +ₚ op hX +ₚ c 6) +ₚ c 8 *ₚ hF +ₚ c 4 +ₚ hMem) +ₚ
      hMem +ₚ c 8) *ₚ (c 4 *ₚ hExp)
  have hQueryV := hn *ₚ (c 2 *ₚ hM +ₚ c 3) +ₚ hVal +ₚ hU +ₚ hZ +ₚ c 3
  have hS := hTree +ₚ op hQueryV +ₚ c 3
  have hRow : HasPolynomialWorkBound N (fun x => binaryRowProbabilityWorkBound (m x) (Y x) (M x)) :=
    c 1 +ₚ hm *ₚ (c 3400 *ₚ (hY +ₚ c 2) ^ₚ 3 +ₚ c 5) +ₚ c 2 *ₚ (c 1 +ₚ c 2 *ₚ hm) +ₚ op hM +ₚ c 10
  have hQuery : HasPolynomialWorkBound N (fun x => binaryScalarQueryWorkBound
      (n x) (m x) (Y x) (M x) (U x) (Z x) (b x) (R x) (a x)) :=
    hn *ₚ hRow +ₚ c 3 *ₚ hn +ₚ c 1 +ₚ frame hU +ₚ
      c 2 *ₚ (c 2 *ₚ ha +ₚ c 2) ^ₚ 2 *ₚ (c 3400 *ₚ (hQueryV +ₚ c 2) ^ₚ 3 +ₚ c 5) +ₚ
      (c 2 *ₚ ha +ₚ c 1) *ₚ hS +ₚ c 6 *ₚ (c 2 *ₚ ha +ₚ c 2) +ₚ c 2 +ₚ c 2 *ₚ op hQueryV +ₚ c 7
  have hRows : HasPolynomialWorkBound N (fun x => binaryCalibrationRowsWorkBound (n x) (m x) (Y x)) :=
    hn *ₚ hm *ₚ (c 2 *ₚ op hY +ₚ c 2) +ₚ c 6 *ₚ hn *ₚ (hm +ₚ c 1) +ₚ c 2
  have hD := c 2 *ₚ hH +ₚ c 2 *ₚ hW +ₚ c 13
  exact ⟨hQuery,hRows +ₚ hn *ₚ hRow +ₚ c 3 *ₚ hn +ₚ c 1 +ₚ frame hU +ₚ
      c 5 *ₚ op hD +ₚ c 8 +ₚ (c 1 +ₚ hR *ₚ (c 7000 *ₚ (hD +ₚ hR +ₚ c 4) ^ₚ 3 +ₚ c 5)) +ₚ hQuery +ₚ c 8,
    hn *ₚ (c 2 *ₚ hM +ₚ c 3) +ₚ hVal +ₚ c 3⟩

end ProphetSecretary.Statistics.Calibration
