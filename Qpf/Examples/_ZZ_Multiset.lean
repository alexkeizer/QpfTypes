import Qpf

set_option pp.analyze true

#check List
#check (inferInstance : MvQPF (@TypeFun.ofCurried 1 List))

abbrev List' : TypeFun 1
  := TypeFun.ofCurried List


example {α} :
  List α = List' ![α] :=
by
  rfl

example {Γ} :
  List (Γ 0) = List' Γ :=
by
  rfl



/-- If `a ∈ as`, return `as` with (a single occurence of) `a` removed.
    Otherwise, if `a ∉ as`, return `none` -/
def List.is_rem (a : α) : List α → List α → Prop
  | b::bs, c::cs  =>    (a = c  ∧ bs = c::cs)
                      ∨ (b = c  ∧ bs.is_rem a cs)
  | _, _          => false


/-- Equates lists up-to permutation -/
def List.perm : List α → List α → Prop
  | [],    []  =>  true
  | a::as, bs  =>  ∃cs : List α, cs.is_rem a bs ∧ as.perm cs
  | _, _       =>  false

abbrev List'.perm ⦃Γ⦄ : (@TypeFun.ofCurried 1 List) Γ → (TypeFun.ofCurried List) Γ → Prop
  := List.perm

def MultiSet := MvQPF.Quot1 List'.perm

noncomputable instance : MvQPF MultiSet := MvQPF.relQuot List'.perm (
  by 
    intros Γ₁ Γ₂ a b f h₁;
    dsimp[TypeFun.ofCurried, TypeFun.reverseArgs, TypeFun.ofCurriedAux] at a b;
    induction a 
      <;> cases b
      <;> simp[List.perm, List.is_rem] at h₁;

    case nil =>
      simp[List'.perm, List.perm]

    case cons a as b bs ih =>
      rcases h₁ with ⟨_|⟨c,cs⟩, h₁, h₂⟩
      { contradiction }
      dsimp[List.perm, List'.perm];

      let cs' : List' Γ₂.reverse := f.reverse <$$> cs;
      use cs';

      constructor
      {
        simp[List.is_rem, TypeVec.last, DVec.last, Sigma.snd, MvQPF.List.box]
        
      } {
        sorry
      }


      
)