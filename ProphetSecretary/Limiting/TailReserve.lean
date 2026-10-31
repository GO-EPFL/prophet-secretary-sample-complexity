import ProphetSecretary.Limiting.ExtendedTailLevels

/-!
# The reserve separating divergent and bounded tail counts

Extended rational tail limits determine a real a in [0,H]. Tail counts diverge
at every physical level 0≤x<a, and are bounded on the whole extracted sequence
at every x>a, including its finite initial segment. This is the first reserve
step in the general H-only compact-extraction proof.
-/
open MeasureTheory Set Filter
open scoped Topology Classical BigOperators
namespace ProphetSecretary.Limiting

noncomputable def divergenceLevels (l : ℚ → ENNReal) : Set ℝ :=
  {x | ∃ q : ℚ, x = (q : ℝ) ∧ 0 ≤ x ∧ l q = ⊤}
noncomputable def tailReserve (l : ℚ → ENNReal) : ℝ := sSup (insert 0 (divergenceLevels l))

lemma divergenceLevels_upper {H : ℝ} (hH : 0 ≤ H) (l : ℚ → ENNReal)
    (habove : ∀ q : ℚ, H ≤ (q : ℝ) → l q = 0) :
    ∀ x ∈ insert 0 (divergenceLevels l), x ≤ H := by
  intro x hx
  rcases hx with hx | hx
  · simpa only [hx] using hH
  · obtain ⟨q,hqx,_hx0,hqtop⟩ := hx
    by_cases hxH : x ≤ H
    · exact hxH
    · have hHq : H ≤ (q : ℝ) := by rw [← hqx]; exact (lt_of_not_ge hxH).le
      rw [habove q hHq] at hqtop
      simp at hqtop

lemma tailReserve_mem_interval {H : ℝ} (hH : 0 ≤ H) (l : ℚ → ENNReal)
    (habove : ∀ q : ℚ, H ≤ (q : ℝ) → l q = 0) : tailReserve l ∈ Icc (0 : ℝ) H := by
  have hupper := divergenceLevels_upper hH l habove
  have hbd : BddAbove (insert 0 (divergenceLevels l)) := ⟨H,hupper⟩
  exact ⟨le_csSup hbd (Or.inl rfl),csSup_le ⟨0,Or.inl rfl⟩ hupper⟩

lemma exists_divergenceLevel_above {x : ℝ} (hx0 : 0 ≤ x) (l : ℚ → ENNReal)
    (hx : x < tailReserve l) : ∃ q : ℚ, x < (q : ℝ) ∧ l q = ⊤ := by
  have hex : ∃ y ∈ insert 0 (divergenceLevels l), x < y := by
    by_contra hn
    have hu : ∀ y ∈ insert 0 (divergenceLevels l), y ≤ x := fun y hy =>
      le_of_not_gt (fun hxy => hn ⟨y,hy,hxy⟩)
    exact (not_le_of_gt hx) (csSup_le ⟨0,Or.inl rfl⟩ hu)
  obtain ⟨y,hy,hxy⟩ := hex
  rcases hy with hy | hy
  · rw [hy] at hxy
    exact False.elim ((not_lt_of_ge hx0) hxy)
  · obtain ⟨q,hqy,_hy0,hqtop⟩ := hy
    exact ⟨q,hxy.trans_eq hqy,hqtop⟩

lemma exists_finite_rational_tail_below {H x : ℝ} (hH : 0 ≤ H) (l : ℚ → ENNReal)
    (habove : ∀ q : ℚ, H ≤ (q : ℝ) → l q = 0) (hx : tailReserve l < x) :
    ∃ q : ℚ, tailReserve l < (q : ℝ) ∧ (q : ℝ) < x ∧ l q ≠ ⊤ := by
  obtain ⟨q,hqlo,hqhi⟩ := exists_rat_btwn hx
  have hupper := divergenceLevels_upper hH l habove
  have hbd : BddAbove (insert 0 (divergenceLevels l)) := ⟨H,hupper⟩
  refine ⟨q,hqlo,hqhi,?_⟩
  intro hqtop
  have hq0 : 0 ≤ (q : ℝ) := (tailReserve_mem_interval hH l habove).1.trans hqlo.le
  have hqmem : (q : ℝ) ∈ insert 0 (divergenceLevels l) := Or.inr ⟨q,rfl,hq0,hqtop⟩
  exact (not_le_of_gt hqlo) (le_csSup hbd hqmem)

/-- The two reserve-side conclusions follow from the actual extended rational
limits; no reserve behavior is put into the input data. -/
theorem tail_separator_of_rational_limits {H : ℝ} (hH : 0 ≤ H)
    (L : ℕ → ℝ → ENNReal) (hanti : ∀ m, Antitone (L m))
    (hfinite : ∀ m x, L m x < ⊤) (l : ℚ → ENNReal)
    (habove : ∀ q : ℚ, H ≤ (q : ℝ) → l q = 0)
    (hconv : ∀ q : ℚ, Tendsto (fun m => L m (q : ℝ)) atTop (𝓝 (l q))) :
    tailReserve l ∈ Icc (0 : ℝ) H ∧
      (∀ x, 0 ≤ x → x < tailReserve l → Tendsto (fun m => L m x) atTop (𝓝 ⊤)) ∧
      ∀ x, tailReserve l < x → ∃ B : ENNReal, B < ⊤ ∧ ∀ m, L m x ≤ B := by
  refine ⟨tailReserve_mem_interval hH l habove,?_,?_⟩
  · intro x hx0 hx
    obtain ⟨q,hxq,hq⟩ := exists_divergenceLevel_above hx0 l hx
    have hqt : Tendsto (fun m => L m (q : ℝ)) atTop (𝓝 ⊤) := by simpa only [hq] using hconv q
    apply tendsto_order.mpr
    constructor
    · intro C hC
      filter_upwards [(tendsto_order.mp hqt).1 C hC] with m hm
      exact hm.trans_le (hanti m hxq.le)
    · intro C hC
      exact False.elim ((not_lt_of_ge le_top) hC)
  · intro x hx
    obtain ⟨q,_hqlo,hqx,hqfinite⟩ := exists_finite_rational_tail_below hH l habove hx
    obtain ⟨C,hlC,hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hqfinite)
    obtain ⟨M,hM⟩ := eventually_atTop.mp ((tendsto_order.mp (hconv q)).2 C hlC)
    let B := C + ∑ m ∈ Finset.range M, L m x
    have hB : B < ⊤ := ENNReal.add_lt_top.mpr ⟨hCtop,ENNReal.sum_lt_top.mpr (fun m _ => hfinite m x)⟩
    refine ⟨B,hB,?_⟩
    intro m
    by_cases hm : m < M
    · have hp := Finset.single_le_sum (s := Finset.range M) (f := fun k => L k x)
        (fun k _ => bot_le) (Finset.mem_range.mpr hm)
      exact hp.trans (le_add_of_nonneg_left bot_le)
    · exact ((hanti m hqx.le).trans (hM m (not_lt.mp hm)).le).trans (le_add_of_nonneg_right bot_le)

/-- General H-only finite-instance reserve extraction, before any individual
ordering, Poisson limit construction or policy/value convergence. -/
theorem exists_finite_instance_tail_separator {H : ℝ} (hH : 0 ≤ H) (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ H) :
    ∃ (a : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ a ∈ Icc (0 : ℝ) H ∧
      (∀ x, 0 ≤ x → x < a → Tendsto (fun m => extendedTailCount (P (φ m)) x) atTop (𝓝 ⊤)) ∧
      ∀ x, a < x → ∃ B : ENNReal, B < ⊤ ∧ ∀ m, extendedTailCount (P (φ m)) x ≤ B := by
  obtain ⟨l,φ,hφ,_hlanti,hlcap,hconv⟩ := exists_finite_instance_rational_tail_limits sizes P hcap
  have hsep := tail_separator_of_rational_limits hH (fun m => extendedTailCount (P (φ m)))
    (fun m => extendedTailCount_antitone (P (φ m))) (fun m x => extendedTailCount_finite (P (φ m)) x) l hlcap hconv
  exact ⟨tailReserve l,φ,hφ,hsep⟩

end ProphetSecretary.Limiting
