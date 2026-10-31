import Mathlib.Data.Prod.Lex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Lexicographic value/tag observations

The measurable space is the ordinary product measurable space transported to
the lexicographic order type. In particular it is not an assumption about the
lexicographic order topology. Both order comparisons and finite extrema are
measurable by explicit coordinate comparisons.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Probability

abbrev TaggedValue := ℝ ×ₗ ℝ

instance taggedValueMeasurableSpace : MeasurableSpace TaggedValue :=
  MeasurableSpace.comap (ofLex : TaggedValue → ℝ × ℝ) inferInstance

lemma measurable_ofTaggedValue : Measurable (ofLex : TaggedValue → ℝ × ℝ) := comap_measurable _

lemma measurable_toTaggedValue : Measurable (toLex : ℝ × ℝ → TaggedValue) := by
  rw [measurable_comap_iff]
  change Measurable (fun x : ℝ × ℝ => x)
  exact measurable_id

noncomputable def taggedValueEquiv : (ℝ × ℝ) ≃ᵐ TaggedValue where
  toEquiv := toLex
  measurable_toFun := measurable_toTaggedValue
  measurable_invFun := measurable_ofTaggedValue

instance taggedValueMeasurableSingleton : MeasurableSingletonClass TaggedValue where
  measurableSet_singleton z := by
    have hEq : ({z} : Set TaggedValue)=(ofLex : TaggedValue → ℝ × ℝ) ⁻¹' {ofLex z} := by
      ext w
      simp only [Set.mem_singleton_iff,Set.mem_preimage]
      exact ofLex.injective.eq_iff.symm
    rw [hEq]
    exact (measurableSet_singleton _).preimage measurable_ofTaggedValue

lemma measurableSet_taggedValue_le : MeasurableSet {p : TaggedValue × TaggedValue | p.1≤p.2} := by
  have h1 := measurable_ofTaggedValue.comp (measurable_fst : Measurable (Prod.fst : TaggedValue × TaggedValue → TaggedValue))
  have h2 := measurable_ofTaggedValue.comp (measurable_snd : Measurable (Prod.snd : TaggedValue × TaggedValue → TaggedValue))
  have h := (measurableSet_lt (measurable_fst.comp h1) (measurable_fst.comp h2)).union
    ((measurableSet_eq_fun (measurable_fst.comp h1) (measurable_fst.comp h2)).inter
      (measurableSet_le (measurable_snd.comp h1) (measurable_snd.comp h2)))
  convert h using 1
  ext p
  exact Prod.Lex.le_iff

lemma measurableSet_taggedValue_lt : MeasurableSet {p : TaggedValue × TaggedValue | p.1<p.2} := by
  have h1 := measurable_ofTaggedValue.comp (measurable_fst : Measurable (Prod.fst : TaggedValue × TaggedValue → TaggedValue))
  have h2 := measurable_ofTaggedValue.comp (measurable_snd : Measurable (Prod.snd : TaggedValue × TaggedValue → TaggedValue))
  have h := (measurableSet_lt (measurable_fst.comp h1) (measurable_fst.comp h2)).union
    ((measurableSet_eq_fun (measurable_fst.comp h1) (measurable_fst.comp h2)).inter
      (measurableSet_lt (measurable_snd.comp h1) (measurable_snd.comp h2)))
  convert h using 1
  ext p
  exact Prod.Lex.lt_iff

instance taggedValueMeasurableSup : MeasurableSup₂ TaggedValue where
  measurable_sup := by
    have h : Measurable (fun p : TaggedValue × TaggedValue => if p.1≤p.2 then p.2 else p.1) :=
      measurable_snd.ite measurableSet_taggedValue_le measurable_fst
    simpa only [max_def] using h

instance taggedValueMeasurableInf : MeasurableInf₂ TaggedValue where
  measurable_inf := by
    have h : Measurable (fun p : TaggedValue × TaggedValue => if p.1≤p.2 then p.1 else p.2) :=
      measurable_fst.ite measurableSet_taggedValue_le measurable_snd
    simpa only [min_def] using h

end ProphetSecretary.Probability
