import ProphetSecretary.Model.TrainingExecution

/-!
# Changing the independent seed of an adaptive sample requester

A pullback of the seed leaves every requested observation and every stopping
branch unchanged. The transcript equality is pathwise, including exhausted
requests and impossible training arrays, so it preserves hard budgets.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n k : ℕ} {A B : Type*}

def RequestRule.pullbackSeed (rule : RequestRule n A) (f : B → A) : RequestRule n B :=
  fun b h => rule (f b) h

lemma train_pullbackSeed (rule : RequestRule n A) (f : B → A) (b : B)
    (y : Reservoir n k) (fuel : ℕ) (h : Transcript n) :
    train (rule.pullbackSeed f) b y fuel h = train rule (f b) y fuel h := by
  induction fuel generalizing h with
  | zero => rfl
  | succ fuel ih =>
    simp only [train,RequestRule.pullbackSeed]
    split
    · rfl
    · split
      · exact ih _
      · rfl

lemma trainingTranscript_pullbackSeed (rule : RequestRule n A) (f : B → A) (b : B)
    (y : Reservoir n k) :
    trainingTranscript (rule.pullbackSeed f) b y = trainingTranscript rule (f b) y :=
  train_pullbackSeed rule f b y (n*k) []

lemma measurableRequestRule_pullbackSeed [MeasurableSpace A] [MeasurableSpace B]
    (rule : RequestRule n A) (hRule : MeasurableRequestRule rule) {f : B → A} (hf : Measurable f) :
    MeasurableRequestRule (rule.pullbackSeed f) :=
  hRule.comp ((hf.comp measurable_fst).prodMk measurable_snd)

end ProphetSecretary.Model
