import Qpf.Examples._01_List

open MvQpf

/-
  ```lean4
  coinductive QpfStream α
  | cons : α → QpfStream α → QpfStream α
  ```
-/
namespace QpfStream
  inductive HeadT
    | cons

  /- 
    The "child" type tells us for each constructor (i.e., element of `HeadT`) and each type argument,
    how many instances of that type we need, through the cardinality of `ChildT a i`.

    In this case, the `nil` constructor takes no argument, while `cons` takes one instance of both 
    arguments, hence we use the empty and unit types, respectively.
  -/
  abbrev ChildT : HeadT → TypeVec 2
    | HeadT.cons, _ => Unit

  /- 
    We define the polynomial functor
  -/
  abbrev P := MvPFunctor.mk HeadT ChildT
  abbrev F := P.Obj


  abbrev QpfStream' := Cofix F
  abbrev QpfStream  := QpfStream'.curried

  def F.cons (a : α) (b : β) : F ![α, β] :=
    ⟨HeadT.cons, fun
      | 0, _ => b
      | 1, _ => a
    ⟩

  def corec {α β} (f : β → α × β) (b : β) : QpfStream α :=    
    Cofix.corec f' b 
    where
      f' b :=
        let (a', b') := f b
        let stream := F.cons a' b'
        cast (congrArg _ $ by 
          funext i;
          cases i;
          swap; 
          rename_i i; cases i

          case fs.fs => contradiction

          all_goals
            rfl
        ) stream



  def head (stream : QpfStream α) : α :=
    let ⟨_, children⟩ := Cofix.dest stream
    children 1 ()

  def tail (stream : QpfStream α) : QpfStream α :=
    let ⟨_, children⟩ := Cofix.dest stream
    children 0 ()


  def coinduction {R : QpfStream α → QpfStream α → Prop} 
                  (h_bisim : ∀ x y, R x y → head x = head y ∧ R (tail x) (tail y)) :
        ∀ x y, R x y → x = y :=
    Cofix.bisim_rel R h'
    where
      h' x y h_rel := by
        have h_bisim' := h_bisim _ _ h_rel
        simp [head, tail] at h_bisim';
        revert h_bisim';
        rcases Cofix.dest x with ⟨⟨_⟩, g₁⟩
        rcases Cofix.dest y with ⟨⟨_⟩, g₂⟩
        simp
        intro h₁ h₂;

        simp [MvFunctor.map, MvPFunctor.map]
        apply congrArg
        simp [TypeVec.comp]
        funext i x;
        cases x;
        cases i
        case fs i => 
          cases i
          . exact h₁
          . contradiction
        case fz => {
          simp[TypeVec.appendFun, TypeVec.splitFun]
          apply Quot.sound;
          exact h₂
        }
        
        

  /-
    We can construct and deconstruct streams without `sorryAx`
  -/
  #print axioms corec
  #print axioms head
  #print axioms tail

  /-
    Even coinduction is fully proven
  -/
  #print axioms coinduction

  /-
    However, showing that `QpfStream` is itself a Qpf requires `sorry`

    So, we cannot use `QpfStream` to define another (co)datatype yet
  -/
  def qpf : MvQpf QpfStream' 
    := inferInstance

  #print axioms qpf
  


end QpfStream