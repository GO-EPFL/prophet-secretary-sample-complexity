import ProphetSecretary.Limiting.CountableDurationValueConstancy
import ProphetSecretary.Limiting.FirstAcceptanceTimeUniqueness

/-!
# Constancy of the selected occurrence under individual mean contraction

On the actual distinct-clock event, equal stopping durations identify equal
selected occurrences, including the terminal no-selection case. Combining
this fact with the zero-response duration theorem proves the corresponding
selected-occurrence assertion in the first step of `lem:nonzero`.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

lemma CountableRule.selectedCode_replaceIndividualValue_eq_of_duration_eq
    (π : CountableRule Seed) (i : ℕ) (v : CompleteWorld Seed) (x : ℝ)
    (hInjective : Set.InjOn (fun c : Candidate => (candidatePoint v c).1) {c | candidatePresent v c})
    (hTimes : ∀ c : Candidate, candidatePresent v c → (candidatePoint v c).1 ∈ Ioo (0 : ℝ) 1)
    (hDuration : π.durationAtValue i (v,x)=π.realizedDuration v) :
    FirstAcceptance.selectedCode π.codeAccepted codeTime (replaceIndividualValue i (v,x))=
      FirstAcceptance.selectedCode π.codeAccepted codeTime v := by
  let ξ := replaceIndividualValue i (v,x)
  let A : CompleteWorld Seed → ℕ → Prop := fun _ => π.codeAccepted ξ
  have hTransfer := FirstAcceptance.selectedCode_timeScale
    (A := π.codeAccepted) (u := codeTime) (ω := ξ)
    (B := A) (v := codeTime) (ξ := v) (h := 1) zero_lt_one
    (fun _ => Iff.rfl) (fun k _ => by simpa only [one_mul] using (codeTime_replaceIndividualValue i (v,x) k).symm)
  have hDurationTransfer : FirstAcceptance.stoppingTime A codeTime v=π.realizedDuration ξ := by
    unfold CountableRule.realizedDuration FirstAcceptance.stoppingTime
    rw [hTransfer]
    split_ifs
    · rfl
    · exact (codeTime_replaceIndividualValue i (v,x) _).symm
  have hA (k : ℕ) (hk : A v k) : codePresent v k :=
    (candidatePresent_replaceIndividualValue i (v,x) _).mp hk.1
  have hC (k : ℕ) (hk : π.codeAccepted v k) : codePresent v k := hk.1
  have hTime (k : ℕ) (hk : codePresent v k) : codeTime v k < 1 := (hTimes _ hk).2
  have hInj : Set.InjOn (codeTime v) {k | codePresent v k} := by
    intro k hk l hl hEq
    exact candidateEnumeration.symm.injective (hInjective hk hl hEq)
  have hEqual : FirstAcceptance.stoppingTime A codeTime v=π.realizedDuration v :=
    hDurationTransfer.trans hDuration
  exact hTransfer.symm.trans
    (FirstAcceptance.selectedCode_eq_of_stoppingTime_eq A π.codeAccepted codeTime v (codePresent v) hA hC hTime hInj hEqual)

theorem canonical_selectedCodeAtValue_ae_constant_on_support_hull
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ x ∈ convexHull ℝ (B.individuals i : Measure ℝ).support,
        FirstAcceptance.selectedCode (B.valueRule w c).codeAccepted codeTime (replaceIndividualValue i (v,x))=
          FirstAcceptance.selectedCode (B.valueRule w c).codeAccepted codeTime v := by
  filter_upwards [B.canonical_durationAtValue_ae_constant_on_support_hull hZero hw hc i hScores,
    B.present_candidate_times_injective (Measure.dirac ()),B.present_candidate_times_mem_Ioo (Measure.dirac ())]
    with v hv hI hT x hx
  exact (B.valueRule w c).selectedCode_replaceIndividualValue_eq_of_duration_eq i v x hI hT (hv x hx)

theorem canonical_selectedCodeAtValue_mean_ae_eq
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (fun v => FirstAcceptance.selectedCode (B.valueRule w c).codeAccepted codeTime
      (replaceIndividualValue i (v,∫ x, x ∂(B.individuals i : Measure ℝ))))
      =ᵐ[B.completeWorldLaw (Measure.dirac ())]
        FirstAcceptance.selectedCode (B.valueRule w c).codeAccepted codeTime := by
  filter_upwards [B.canonical_selectedCodeAtValue_ae_constant_on_support_hull hZero hw hc i hScores] with v hv
  exact hv _ (B.individual_mean_mem_support_hull i)

end ProphetSecretary.Limiting.CountableInstance
