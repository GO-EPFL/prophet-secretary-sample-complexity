import ProphetSecretary.Analysis.ArithmeticExpression

/-!
# Arithmetic expressions under an ordered field embedding

Exact arithmetic and the order tests commute with a strictly monotone
field homomorphism. This permits the same expression evaluator to use
different exact storage representations.
-/

namespace ProphetSecretary.Analysis.ArithmeticExpression

variable {ι K L : Type*} [Field K] [Field L] [LinearOrder K] [LinearOrder L]

lemma eval_map_value (f : K →+* L) (hf : StrictMono f) (x : ι → K) (e : ArithmeticExpression ι) :
    f (eval x e) = eval (fun i => f (x i)) e := by
  induction e with
  | integer z => exact map_intCast f z
  | input i => rfl
  | add a b ha hb => simp only [eval,map_add,ha,hb]
  | sub a b ha hb => simp only [eval,map_sub,ha,hb]
  | mul a b ha hb => simp only [eval,map_mul,ha,hb]
  | div a b ha hb => simp only [eval,map_div₀,ha,hb]
  | minimum a b ha hb => simp only [eval,hf.monotone.map_min,ha,hb]
  | maximum a b ha hb => simp only [eval,hf.monotone.map_max,ha,hb]

end ProphetSecretary.Analysis.ArithmeticExpression
