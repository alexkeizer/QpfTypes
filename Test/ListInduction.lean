import Qpf.Macro.Data

/-!
## Test for induction principle generation
-/

namespace Test

data QpfList α
  | nil
  | cons : α → QpfList α → QpfList α

/-- info: 'Test.QpfList.ind' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in #print axioms QpfList.ind

-- The following test might be a bit brittle.
-- Feel free to remove if it gives too many false positives
/--
info: Test.QpfList.ind {α : Type} {motive✝ : QpfList α → Prop} (nil : motive✝ QpfList.nil)
  (cons : ∀ (x : α) (x_1 : QpfList α), motive✝ x_1 → motive✝ (QpfList.cons x x_1)) (val✝ : QpfList α) : motive✝ val✝
-/
#guard_msgs in #check QpfList.ind

end Test
