import ProphetSecretary.Statistics.CalibratedOuter.Work
import ProphetSecretary.Statistics.CalibratedOuter.MarkAllocation
import ProphetSecretary.Statistics.CalibratedPolynomialWork

/-!
# Polynomial overhead of the outer arithmetic execution

This accounts for reading the three blocks, reserving their marks, computing
the cutoff and pilot, transforming the inner training data, and displaying
the observations. Inner preparation and decisions are counted separately.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration

noncomputable def outerArithmeticOverhead (n m : ℕ) : ℕ :=
  let q := outerPilotRounds m
  let k := outerSampleBudget m
  let S := outerMarkSlotCount n m
  8*(n+1)*(k+1)+5*(S+1)+
    10*(m+1)*(n+1)+20*(q+1)^2*(n+1)+5+n*(2*m)*(4*m+21)+
    n*((n+1)*(4*m+24)+9)+10

theorem outerArithmeticOverhead_poly (n m : ℕ) :
    outerArithmeticOverhead n m≤10000000000*(n+m+2)^3 := by
  let N := n+m+2
  let Q := outerPilotRounds m
  let k := outerSampleBudget m
  let S := outerMarkSlotCount n m
  have hN : 0<N := by dsimp [N]; omega
  have hn : n+1≤N := by dsimp [N]; omega
  have hm : m+1≤N := by dsimp [N]; omega
  have hQ : Q+1≤12001*N := by
    have h := clog_two_le_self (2*m)
    unfold Q outerPilotRounds outerPilotRank
    dsimp [N]
    omega
  have hk : k+1≤12004*N := by
    have h := clog_two_le_self (2*m)
    rw [show k=3*m+6000*Nat.clog 2 (2*m) from outerSampleBudget_eq m]
    dsimp [N]
    omega
  have hS : S+1≤12005*N^2 := by
    change n*(k+1)+1≤_
    have h := Nat.mul_le_mul (show n≤N by omega) hk
    have h₁ : N*(12004*N)=12004*N^2 := by ring
    rw [h₁] at h
    have h₂ : 1≤N^2 := Nat.one_le_pow _ _ hN
    omega
  have h2 : N^2≤N^3 := Nat.pow_le_pow_right hN (by omega)
  have h3 : 1≤N^3 := Nat.one_le_pow _ _ hN
  have hRead : 8*(n+1)*(k+1)≤96032*N^3 := by
    calc
      _ ≤ 8*N*(12004*N) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) hk
      _ = 96032*N^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have hTags : 5*(S+1)≤60025*N^3 := by
    calc
      _ ≤ 5*(12005*N^2) := Nat.mul_le_mul_left _ hS
      _ = 60025*N^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have hCut : 10*(m+1)*(n+1)≤10*N^3 := by
    calc
      _ ≤ 10*N*N := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm) hn
      _ = 10*N^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have hPilot : 20*(Q+1)^2*(n+1)≤2880480020*N^3 := by
    calc
      _ ≤ 20*(12001*N)^2*N :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _)) hn
      _ = _ := by ring
  have hDisplay : n*(2*m)*(4*m+21)≤50*N^3 := by
    have h : 4*m+21≤25*N := by dsimp [N]; omega
    calc
      _ ≤ N*(2*N)*(25*N) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) h
      _ = _ := by ring
  have hOnline : n*((n+1)*(4*m+24)+9)≤37*N^3 := by
    have h : 4*m+24≤28*N := by dsimp [N]; omega
    have h' := Nat.mul_le_mul hn h
    have hx : N*(28*N)=28*N^2 := by ring
    rw [hx] at h'
    have hN2 : 1≤N^2 := Nat.one_le_pow _ _ hN
    calc
      _ ≤ N*(37*N^2) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  unfold outerArithmeticOverhead
  change 8*(n+1)*(k+1)+5*(S+1)+
    10*(m+1)*(n+1)+20*(Q+1)^2*(n+1)+5+n*(2*m)*(4*m+21)+
    n*((n+1)*(4*m+24)+9)+10 ≤ 10000000000*N^3
  omega

end ProphetSecretary.Statistics.Calibration
