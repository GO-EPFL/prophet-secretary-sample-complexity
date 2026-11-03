import ProphetSecretary.Statistics.CalibrationCovariance
import ProphetSecretary.Analysis.LargeFirstMomentSurplus

/-!
# Averaging and absorbing calibration errors

The bounded-first-moment class uses a quadratic absorption inequality.
The large-first-moment class uses its uniform scalar-gap floor against
the slower logarithmic and square-root errors.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Analysis

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_calibration_reward_master (D : Measure Ω) [IsProbabilityMeasure D]
    {F r zg e R : Ω → ℝ} (hF : Integrable F D) (hr : Integrable r D)
    (hzg : Integrable zg D) (he : Integrable e D) (hR : Integrable R D) (mu cM : ℝ)
    (hPoint : ∀ᵐ x ∂D, mu*F x-5*r x-zg x-(1/4)*e x≤R x-cM) :
    mu*(∫ x,F x ∂D)-5*(∫ x,r x ∂D)-(∫ x,zg x ∂D)-(1/4)*(∫ x,e x ∂D)≤(∫ x,R x ∂D)-cM := by
  have hA := (hF.const_mul mu).sub (hr.const_mul 5)
  have hB := hA.sub hzg
  have hC := hB.sub (he.const_mul (1/4))
  have h := integral_mono_ae hC (hR.sub (integrable_const cM)) hPoint
  change (∫ x, mu*F x-5*r x-zg x-(1/4)*e x ∂D)≤∫ x,R x-cM ∂D at h
  rw [integral_sub (f := fun x => mu*F x-5*r x-zg x) (g := fun x => (1/4)*e x) hB (he.const_mul (1/4)),
    integral_sub (f := fun x => mu*F x-5*r x) (g := zg) hA hzg,
    integral_sub (f := fun x => mu*F x) (g := fun x => 5*r x) (hF.const_mul mu) (hr.const_mul 5),
    integral_sub (f := R) (g := fun _ => cM) hR (integrable_const cM),integral_const,probReal_univ,one_smul,
    integral_const_mul,integral_const_mul,integral_const_mul] at h
  exact h

lemma expected_gap_ge_ratio_slack {n : ℕ} (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    (D : Measure Ω) [IsProbabilityMeasure D] {mu : ℝ} (hmu : mu≤1) (hM : mu≤P.expectedMaximum)
    {l : Ω → ℝ} (hl : ∀ x,l x∈Icc (0 : ℝ) 1)
    (hF : Integrable (fun x => normalizedScalarGap P (l x)) D) :
    mu*(P.optimalScalarRatio-optimalCompetitiveRatio)≤∫ x,normalizedScalarGap P (l x) ∂D := by
  let d := P.optimalScalarRatio-optimalCompetitiveRatio
  have hd : 0≤d := sub_nonneg.mpr (P.optimalScalarRatio_bounds hP).1
  have h (x : Ω) : mu*d≤normalizedScalarGap P (l x) := by
    have hB := P.scalarRatio_denominator_ge hmu hM (hl x)
    have hR := P.ratioSlack_mul_benchmark_le_gap hP (hl x)
    exact (mul_le_mul_of_nonneg_right hB hd).trans (by simpa only [d,mul_comm] using hR)
  have hI := integral_mono (integrable_const (mu*d)) hF h
  simpa only [integral_const,probReal_univ,one_smul,d] using hI

/-- Square completion retains constants independent of the instance and sample count. -/
lemma calibration_square_absorption {mu m G A B : ℝ} (hmu : 0<mu) (hm : 0<m)
    (hG : 0≤G) :
    -(A^2/(4*mu)+B)/m ≤ mu*G-A*Real.sqrt (G/m)-B/m := by
  let y := Real.sqrt (G/m)
  have hy : y^2=G/m := Real.sq_sqrt (div_nonneg hG hm.le)
  have hEq : m*y^2=G := by rw [hy,mul_div_cancel₀ _ hm.ne']
  apply (div_le_iff₀ hm).mpr
  have h := sq_nonneg (y*m-A/(2*mu))
  have hN := mul_nonneg hmu.le h
  have hId : mu*(y*m-A/(2*mu))^2=
      mu*G*m-A*y*m+A^2/(4*mu) := by
    rw [show G=m*y^2 from hEq.symm]
    field_simp [hmu.ne']
    ring
  rw [hId] at hN
  have hB : B/m*m=B := div_mul_cancel₀ _ hm.ne'
  change -(A^2/(4*mu)+B)≤(mu*G-A*y-B/m)*m
  calc
    _ ≤ mu*G*m-A*y*m-B := by linarith only [hN]
    _ = _ := by rw [sub_mul,sub_mul,hB]

lemma calibration_lowMoment_reward_rate {mu m G Δ ER cM KR Kt Kz : ℝ}
    (hmu : 0<mu) (hm : 0<m) (hG : 0≤G) (hΔG : mu*Δ≤G)
    (hKt : 0≤Kt)
    {reg cov err : ℝ} (hReg : reg≤KR/m)
    (hCov : cov≤Kz*Real.sqrt (G/m)+1/(4*m))
    (hErr : err≤Kt*Real.sqrt (Δ/m)+Kt/m)
    (hMaster : mu*G-5*reg-cov-(1/4)*err≤ER-cM) :
    -( (Kz+Kt/(4*Real.sqrt mu))^2/(4*mu)+(5*KR+1/4+Kt/4))/m ≤ ER-cM := by
  have hΔ' : Δ/m≤(G/m)/mu := by
    apply (le_div_iff₀ hmu).mpr
    have hh := div_le_div_of_nonneg_right hΔG hm.le
    convert hh using 1
    ring
  have hR := Real.sqrt_le_sqrt hΔ'
  rw [Real.sqrt_div (div_nonneg hG hm.le)] at hR
  have hE := mul_le_mul_of_nonneg_left hR hKt
  have hRμ : Real.sqrt mu≠0 := (Real.sqrt_pos.mpr hmu).ne'
  have hErr' : err≤(Kt/Real.sqrt mu)*Real.sqrt (G/m)+Kt/m := by
    calc
      _ ≤ _ := hErr
      _ ≤ Kt*(Real.sqrt (G/m)/Real.sqrt mu)+Kt/m := add_le_add_left hE _
      _ = _ := by ring
  have h := calibration_square_absorption (A:=Kz+Kt/(4*Real.sqrt mu)) (B:=5*KR+1/4+Kt/4)
    hmu hm hG
  have hS : (Kz+Kt/(4*Real.sqrt mu))*Real.sqrt (G/m)+(5*KR+1/4+Kt/4)/m =
      5*(KR/m)+(Kz*Real.sqrt (G/m)+1/(4*m))+(1/4)*((Kt/Real.sqrt mu)*Real.sqrt (G/m)+Kt/m) := by
    ring
  have hBound := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hReg (by norm_num : (0 : ℝ)≤5)) hCov)
    (mul_le_mul_of_nonneg_left hErr' (by norm_num : (0 : ℝ)≤1/4))
  rw [← hS] at hBound
  linarith only [h,hMaster,hBound]

/-- A fixed sample threshold works for every large-first-moment instance. -/
theorem exists_calibration_highMoment_threshold {mu κ KR Kt : ℝ} (hmu : 0<mu) (hκ : 0<κ)
    (hKR : 0≤KR) (hKt : 0≤Kt) :
    ∃ m0 : ℕ, 65536≤m0 ∧ ∀ m : ℕ, m0≤m →
      0≤mu*κ/(1+2*Real.log (m : ℝ))^4-
        5*KR*(1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)))/(m : ℝ)-
        (1/2+Kt/4)/Real.sqrt (m : ℝ) := by
  let A := 5*KR+Kt/4+1
  have hA : 0<A := by dsimp [A]; positivity
  obtain ⟨m0,hm0,hThreshold⟩ :=
    exists_largeFirstMomentSurplus_threshold (A:=mu*κ/A) (K:=1) (by positivity) zero_le_one
  refine ⟨m0,hm0,?_⟩
  intro m hm
  have hmPos : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hmOne : (1 : ℝ)≤m := by exact_mod_cast (show 1≤m by omega)
  have hLog : 0≤2*Real.log (m : ℝ) := mul_nonneg (by norm_num) (Real.log_nonneg hmOne)
  let F := (1+2*Real.log (m : ℝ))^4
  let E := 1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ))
  have hE : 0≤E := by dsimp [E]; positivity
  have hR : 0<Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmPos
  have hB : 5*KR≤A := by dsimp [A]; linarith
  have hC : 1/2+Kt/4≤A := by dsimp [A]; linarith
  have h1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB hE) hmPos.le
  have h2 := div_le_div_of_nonneg_right hC hR.le
  have h := mul_nonneg hA.le (hThreshold m hm)
  change 0≤A*(mu*κ/A/F-1*E/(m : ℝ)-1/Real.sqrt (m : ℝ)) at h
  have he : A*(mu*κ/A/F-1*E/(m : ℝ)-1/Real.sqrt (m : ℝ))=
      mu*κ/F-A*E/(m : ℝ)-A/Real.sqrt (m : ℝ) := by
    field_simp [hA.ne']
  rw [he] at h
  change 0≤mu*κ/F-5*KR*E/(m : ℝ)-(1/2+Kt/4)/Real.sqrt (m : ℝ)
  linarith only [h,h1,h2]

end ProphetSecretary.Statistics.Calibration
