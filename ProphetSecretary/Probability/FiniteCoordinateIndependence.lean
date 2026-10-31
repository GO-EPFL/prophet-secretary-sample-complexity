import Mathlib.Probability.Independence.Basic

/-!
# Independence from finite coordinate observations

The coordinate index sets may be arbitrary. Directed unions of the finite
coordinate sigma-algebras generate the full product observations.
-/

open MeasureTheory ProbabilityTheory

namespace ProphetSecretary.Probability

theorem indepFun_of_finite_coordinates {Ω ι κ A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ι → A} {Y : Ω → κ → B}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ (I : Finset ι) (J : Finset κ),
      IndepFun (fun ω => fun i : I => X ω i) (fun ω => fun j : J => Y ω j) P) : IndepFun X Y P := by
  classical
  let mX := fun I : Finset ι => ⨆ i ∈ I, MeasurableSpace.comap (fun ω => X ω i) inferInstance
  let mY := fun J : Finset κ => ⨆ j ∈ J, MeasurableSpace.comap (fun ω => Y ω j) inferInstance
  have hXm : Monotone mX := by
    intro I J hIJ
    exact iSup_le (fun i => iSup_le (fun hi => le_iSup_of_le i (le_iSup_of_le (hIJ hi) le_rfl)))
  have hYm : Monotone mY := by
    intro I J hIJ
    exact iSup_le (fun i => iSup_le (fun hi => le_iSup_of_le i (le_iSup_of_le (hIJ hi) le_rfl)))
  have hXle (I) : mX I ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup_le (fun i => iSup_le (fun _ => ((measurable_pi_apply i).comp hX).comap_le))
  have hYle (J) : mY J ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup_le (fun j => iSup_le (fun _ => ((measurable_pi_apply j).comp hY).comap_le))
  have hXfull : MeasurableSpace.comap X inferInstance = ⨆ I, mX I := by
    rw [MeasurableSpace.comap_process_pi]
    apply le_antisymm
    · apply iSup_le
      intro i
      exact le_iSup_of_le {i} (le_iSup_of_le i (le_iSup_of_le (Finset.mem_singleton_self i) le_rfl))
    · exact iSup_le (fun I => iSup_le (fun i => iSup_le (fun _ => le_iSup (fun a => MeasurableSpace.comap (fun ω => X ω a) inferInstance) i)))
  have hYfull : MeasurableSpace.comap Y inferInstance = ⨆ J, mY J := by
    rw [MeasurableSpace.comap_process_pi]
    apply le_antisymm
    · apply iSup_le
      intro j
      exact le_iSup_of_le {j} (le_iSup_of_le j (le_iSup_of_le (Finset.mem_singleton_self j) le_rfl))
    · exact iSup_le (fun J => iSup_le (fun j => iSup_le (fun _ => le_iSup (fun a => MeasurableSpace.comap (fun ω => Y ω a) inferInstance) j)))
  have hFinite (I J) : Indep (mX I) (mY J) P := by
    have hIJ := (IndepFun_iff_Indep _ _ _).mp (h I J)
    simpa only [MeasurableSpace.comap_process_pi,iSup_subtype,mX,mY] using hIJ
  have hFixed (J) : Indep (⨆ I, mX I) (mY J) P :=
    indep_iSup_of_monotone (fun I => hFinite I J) hXle (hYle J) hXm
  apply (IndepFun_iff_Indep X Y P).mpr
  rw [hXfull,hYfull]
  exact (indep_iSup_of_monotone (fun J => (hFixed J).symm) hYle (iSup_le hXle) hYm).symm

end ProphetSecretary.Probability
