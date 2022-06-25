/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/

import Qpf.MathlibPort.Fin2
import Qpf.Util.HEq
import Qpf.Util.Vec
import Lean.Elab.Tactic.Conv


/-!

# Tuples of types, and their categorical structure.

## Features

* `TypeVec n` - n-tuples of types
* `α ⟹ β`    - n-tuples of maps
* `f ⊚ g`     - composition

Also, support functions for operating with n-tuples of types, such as:

* `append1 α β`    - append type `β` to n-tuple `α` to obtain an (n+1)-tuple
* `drop α`         - drops the last element of an (n+1)-tuple
* `last α`         - returns the last element of an (n+1)-tuple
* `appendFun f g` - appends a function g to an n-tuple of functions
* `dropFun f`     - drops the last function from an n+1-tuple
* `lastFun f`     - returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/


universe u v w

-- set_option pp.all true 



/--
n-tuples of types, as a category
-/
def TypeVec := Vec (Type _)

instance {n} : Inhabited (TypeVec.{u} n) :=
  ⟨fun _ => PUnit⟩

namespace TypeVec
  export Vec (last)

  variable {n : Nat}

  /-- An empty vector -/
  abbrev nil : TypeVec 0 := Vec.nil

  /-- arrow in the category of `typevec` -/
  -- def Arrow (α β : TypeVec n) := ∀ i : Fin2 n, α i → β i
  abbrev Arrow (α β : TypeVec n) := DVec (fun i => α i → β i)

  infixl:40 " ⟹ " => Arrow

  /-- Identity Arrow of `TypeVec` -/
  def id {α : TypeVec n} : α ⟹ α := λ i x => x

  /-- Composition of `TypeVec` Arrows -/
  def comp {α β γ : TypeVec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ :=
  λ i x => g i (f i x)

  infixr:80 " ⊚ " => TypeVec.comp   -- type as \oo

  
  @[simp] theorem id_comp {α β : TypeVec n} (f : α ⟹ β) : id ⊚ f = f := rfl

  @[simp] theorem comp_id {α β : TypeVec n} (f : α ⟹ β) : f ⊚ id = f := rfl

  theorem comp_assoc {α β γ δ : TypeVec n} (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
    (h ⊚ g) ⊚ f = h ⊚ g ⊚ f := rfl


  /-- Appends a single type to a `TypeVec` -/
  @[simp]
  abbrev append1 : TypeVec n → Type _ → TypeVec (n+1)
    := Vec.append1

  infixl:67 " ::: " => append1

  /-- drop the last type from a `TypeVec` -/
  @[simp]
  abbrev drop : TypeVec (n.succ) → TypeVec n := Vec.drop

  
  def append1_cases
    {C : TypeVec (n+1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ :=
  by rw [← @Vec.append1_drop_last _ _ γ]; apply H

  @[simp] theorem append1_cases_append1 {C : TypeVec (n+1) → Sort u}
    (H : ∀ α β, C (append1 α β)) (α β) :
    @append1_cases _ C H (append1 α β) = H α β := rfl


  def splitFun {α α' : TypeVec (n+1)}
    (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
  | (Fin2.fs i) => f i
  | Fin2.fz      => g

  def appendFun {α α' : TypeVec n} 
                {β β' : Type _} 
                (f : α ⟹ α') 
                (g : β → β') 
                  : α ::: β ⟹ α' ::: β' 
    := splitFun f g

  infixl:67 " ::: " => appendFun


  abbrev dropFun {α β : TypeVec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β 
    :=
  λ i => f i.fs

  def lastFun {α β : TypeVec (n+1)} (f : α ⟹ β) : last α → last β :=
  f Fin2.fz

  theorem eq_of_drop_last_eq {α β : TypeVec (n+1)} {f g : α ⟹ β}
    (h₀ : ∀ j, dropFun f j = dropFun g j) (h₁ : lastFun f = lastFun g) : f = g :=
  by funext i; cases i; apply h₁; apply h₀; 

  @[simp] theorem drop_fun_split_fun {α α' : TypeVec (n+1)}
    (f : drop α ⟹ drop α') (g : last α → last α') :
    dropFun (splitFun f g) = f := rfl

  def Arrow.mp {α β : TypeVec n} (h : α = β) : α ⟹ β
  | i => Eq.mp (congrFun h _)

  def Arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
  | i => Eq.mpr (congrFun h _)

  def to_Vec.append1_drop_last {α : TypeVec (n+1)} : α ⟹ drop α ::: last α :=
  Arrow.mpr (Vec.append1_drop_last _)

  /-- stitch two bits of a vector back together -/
  def from_Vec.append1_drop_last {α : TypeVec (n+1)} : drop α ::: last α ⟹ α :=
  Arrow.mp (Vec.append1_drop_last _)

  @[simp] theorem last_fun_split_fun {α α' : TypeVec (n+1)}
    (f : drop α ⟹ drop α') (g : last α → last α') :
    lastFun (splitFun f g) = g := rfl

  @[simp] theorem drop_fun_append_fun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    dropFun (f ::: g : α ::: β ⟹ _) = f := rfl

  @[simp] theorem last_fun_append_fun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    lastFun (f ::: g : α ::: β ⟹ _) = g := rfl

  theorem split_drop_fun_last_fun {α α' : TypeVec (n+1)} (f : α ⟹ α') :
    splitFun (dropFun f) (lastFun f) = f :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  theorem split_fun_inj
    {α α' : TypeVec (n+1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
    (H : splitFun f g = splitFun f' g') : f = f' ∧ g = g' :=
  by rw [← drop_fun_split_fun f g, H, ← last_fun_split_fun f g, H]; simp

  /-- The unique Arrow between empty `TypeVec`s -/
  def nil_fun {α β : TypeVec 0} : α ⟹ β :=
  λ i _ => Fin2.elim0 i

  /-- `nil_fun` is indeed the unique Arrow between `TypeVec 0`s -/
  @[simp] theorem nil_fun_uniq {α β : TypeVec 0} (f : α ⟹ β) : f = nil_fun :=
  by funext i; cases i

  @[simp] theorem nil_fun_uniq' (f : Fin2.elim0 ⟹ Fin2.elim0) : f = nil_fun :=
  by funext i; cases i

  theorem append_fun_inj {α α' : TypeVec n} {β β' : Type _} {f f' : α ⟹ α'} {g g' : β → β'} :
    (f ::: g : α ::: β ⟹ _) = (f' ::: g' : α ::: β ⟹ _)
    → f = f' ∧ g = g' :=
  split_fun_inj

  theorem split_fun_comp {α₀ α₁ α₂ : TypeVec (n+1)}
      (f₀ : drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂)
      (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
    splitFun (f₁ ⊚ f₀) (g₁ ∘ g₀) = splitFun f₁ g₁ ⊚ splitFun f₀ g₀ :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  theorem append_fun_comp_split_fun {α γ : TypeVec n} {β δ : Type _} {ε : TypeVec (n + 1)}
          (f₀ : drop ε ⟹ α) 
          (f₁ : α ⟹ γ)
          (g₀ : last ε → β) 
          (g₁ : β → δ) :
   appendFun f₁ g₁ ⊚ splitFun f₀ g₀ 
      = splitFun (α':=γ.append1 δ) (f₁ ⊚ f₀) (g₁ ∘ g₀) 
  :=
  (split_fun_comp _ _ _ _).symm

  theorem append_fun_comp {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type _}
      (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ⊚ f₀ ::: g₁ ∘ g₀  :   α₀ ::: β₀ ⟹ α₂ ::: β₂)
    = (f₁ ::: g₁  : α₁ ::: β₁ ⟹ α₂ ::: β₂) ⊚ (f₀ ::: g₀ : α₀ ::: β₀ ⟹ α₁ ::: β₁) :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  theorem append_fun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type _}
      (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = f₁ ⊚ f₀ ::: g₁ ∘ g₀ :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  theorem nil_fun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin2.elim0) : nil_fun ⊚ f₀ = f₀ :=
  funext $ λ x => Fin2.elim0 (C:= fun _ => comp nil_fun f₀ x = f₀ x) x

  theorem append_fun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type _}
      (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    @id _ α ::: g₁ ∘ g₀ = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  @[simp]
  theorem drop_fun_comp {α₀ α₁ α₂ : TypeVec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    dropFun (f₁ ⊚ f₀) = dropFun f₁ ⊚ dropFun f₀ := rfl

  @[simp]
  theorem last_fun_comp {α₀ α₁ α₂ : TypeVec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    lastFun (f₁ ⊚ f₀) = lastFun f₁ ∘ lastFun f₀ := rfl

  theorem append_fun_aux {α α' : TypeVec n} {β β' : Type _}
    (f : α ::: β ⟹ α' ::: β') : dropFun f ::: lastFun f = f :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  theorem append_fun_id_id {α : TypeVec n} {β : Type _} :
    @id n α ::: @_root_.id β = id :=
  eq_of_drop_last_eq (λ _ => rfl) rfl


  instance Subsingleton0 : Subsingleton (TypeVec 0) :=
  ⟨ λ a b => funext $ λ a => Fin2.elim0 (C:=fun _ => _) a  ⟩


  -- run_cmd mk_simp_attr `TypeVec
  -- attribute [TypeVec]

  set_option quotPrecheck false
  local prefix:0 "♯" => cast (by simp; apply congrArg <|> skip; simp <|> skip)

  def typevec_cases_nil {β : TypeVec 0 → Sort _} (f : β Fin2.elim0) :
    ∀ v, β v :=
  λ v => cast (by apply congrArg; apply Fin2.eq_fn0) f
  -- λ v => ♯ f

  def typevec_cases_cons (n : Nat) {β : TypeVec (n+1) → Sort _} (f : ∀ t (v : TypeVec n), β (v ::: t)) :
    ∀ v, β v :=
  λ v => cast (by simp) (f v.last v.drop)
  -- λ v => ♯ f v.last v.drop

  theorem typevec_cases_nil_append1 {β : TypeVec 0 → Sort _} (f : β Fin2.elim0) :
    typevec_cases_nil f Fin2.elim0 = f := rfl

  theorem typevec_cases_cons_append1 (n : Nat) {β : TypeVec (n+1) → Sort _}
        (f : ∀ t (v : TypeVec n), β (v ::: t))
        (v : TypeVec n) (α) :
    typevec_cases_cons n f (v ::: α) = f α v := rfl

  @[simp] def eq0 (f : TypeVec 0) : f = Fin2.elim0
  := by apply Fin2.eq_fn0

  /-- FIXME 
  def typevec_cases_nil₃ {β : ∀ v v' : TypeVec 0, v ⟹ v' → Sort _} (f : β Fin2.elim0 Fin2.elim0 nil_fun) :
    ∀ v v' f, β v v' f :=
  λ v v' fs => cast (
    by 
       congr
       simp [veq, v'eq]
  ) f
  begin
    refine cast _ f; congr; ext; try { intros; exact Fin2.elim0 ‹ Fin2 0 ›  }; refl
  end
  -/

  def typevec_cases_cons₃ (n : Nat) {β : ∀ v v' : TypeVec (n+1), v ⟹ v' → Sort _}
    (F : ∀ t t' (f : t → t') (v v' : TypeVec n) (fs : v ⟹ v'), β (v ::: t) (v' ::: t') (fs ::: f)) :
    ∀ v v' fs, β v v' fs :=
  by 
    intros v v'
    rw [←Vec.append1_drop_last v, ←Vec.append1_drop_last v']
    intro fs
    rw [←split_drop_fun_last_fun fs]
    apply F

  def typevec_cases_nil₂ {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort _}
    (f : β nil_fun) :
    ∀ f, β f :=
  by
    intro g
    have : g = nil_fun := by funext x; cases x
    rw [this]
    exact f

  def typevec_cases_cons₂ (n : Nat) (t t' : Type _) (v v' : TypeVec (n)) {β : (v ::: t) ⟹ (v' ::: t') → Sort _}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) :
    ∀ fs, β fs :=
  by
    intro fs
    rw [←split_drop_fun_last_fun fs]
    apply F

  theorem typevec_cases_nil₂_append_fun {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort _}
    (f : β nil_fun) :
    typevec_cases_nil₂ f nil_fun = f := rfl

  theorem typevec_cases_cons₂_append_fun (n : Nat) (t t' : Type _) (v v' : TypeVec (n)) {β : (v ::: t) ⟹ (v' ::: t') → Sort _}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) (f fs) :
    typevec_cases_cons₂ n t t' v v' F (fs ::: f) = F f fs := rfl

  /- for lifting predicates and relations -/

  /-- `predLast α p x` predicates `p` of the last element of `x : α.append1 β`. -/
  def predLast (α : TypeVec n) {β : Type _} (p : β → Prop) : ∀ ⦃i⦄, (α.append1 β) i → Prop
  | (Fin2.fs i) => λ x => true
  | Fin2.fz      => p

  /-- `relLast α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and all the other elements are equal. -/
  def relLast (α : TypeVec n) {β γ : Type _} (r : β → γ → Prop) :
    ∀ {i}, (α.append1 β) i → (α.append1 γ) i → Prop
  | (Fin2.fs i) => Eq
  | Fin2.fz      => r


open Nat


/-- `repeat n t` is a `n-length` type vector that contains `n` occurences of `t` -/
def Repeat : (n : Nat) → (t : Sort _) → TypeVec n
  | 0, t => Fin2.elim0
  | Nat.succ i, t => append1 (Repeat i t) t

/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
def Prod : {n : Nat} → (α β : TypeVec.{u} n) → TypeVec n
  | 0, α, β     => Fin2.elim0
  | n + 1, α, β => (@Prod n (drop α) (drop β)) ::: (last α × last β)

-- mathport name: «expr ⊗ »
infixl:45 " ⊗ " => TypeVec.Prod


/-- `const x α` is an arrow that ignores its source and constructs a `typevec` that
contains nothing but `x` -/
protected def const {β} (x : β) : {n : Nat} → (α : TypeVec n) → α ⟹ Repeat n β
  | succ n, α, Fin2.fs i => TypeVec.const x (drop α) _
  | succ n, α, Fin2.fz => fun _ => x

open Function (uncurry)

/-- vector of equality on a product of vectors -/
def repeatEq : ∀ {n} α : TypeVec n, α ⊗ α ⟹ Repeat _ Prop
  | 0, α => nil_fun
  | succ n, α => repeatEq (drop α) ::: uncurry Eq

theorem const_append1 {β γ} (x : γ) {n} (α : TypeVec n) :
    TypeVec.const x (α ::: β) = appendFun (TypeVec.const x α) fun _ => x := 
by
  funext i
  cases i
  repeat rfl

theorem eq_nil_fun {α β : TypeVec 0} (f : α ⟹ β) : f = nil_fun := by
  ext x <;> cases x

theorem id_eq_nil_fun {α : TypeVec 0} : @id _ α = nil_fun := by
  ext x <;> cases x

theorem const_nil {β} (x : β) (α : TypeVec 0) : TypeVec.const x α = nil_fun := by
  ext i <;> cases i <;> rfl

-- @[TypeVec]
theorem repeat_eq_append1 {β} {n} (α : TypeVec n) : 
  repeatEq (α ::: β) = splitFun (α := (α ⊗ α) ::: _ ) 
                                (α' := (Repeat n Prop) ::: _) 
                                (repeatEq α) 
                                (uncurry Eq) := 
by
  induction n <;> rfl

-- @[typevec]
theorem repeat_eq_nil (α : TypeVec 0) : repeatEq α = nil_fun := by
  ext i <;> cases i <;> rfl

/-- predicate on a type vector to constrain only the last object -/
def predLast' (α : TypeVec n) {β : Type _} (p : β → Prop) : (α ::: β) ⟹ Repeat (n + 1) Prop :=
  splitFun (TypeVec.const True α) p

/-- predicate on the product of two type vectors to constrain only their last object -/
def relLast' (α : TypeVec n) {β : Type _} (p : β → β → Prop) : (α ::: β) ⊗ (α ::: β) ⟹ Repeat (n + 1) Prop :=
  splitFun (repeatEq α) (uncurry p)

/-- given `F : typevec.{u} (n+1) → Type u`, `curry F : Type u → typevec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
def Curry (F : TypeVec.{u} (n + 1) → Type _) (α : Type u) (β : TypeVec.{u} n) : Type _ :=
  F (β ::: α)

instance Curry.inhabited (F : TypeVec.{u} (n + 1) → Type _) (α : Type u) (β : TypeVec.{u} n)
    [I : Inhabited (F <| (β ::: α))] : Inhabited (Curry F α β) :=
  I


/-- arrow to remove one element of a `repeat` vector -/
def dropRepeat (α : Type _) : ∀ {n}, drop (Repeat (succ n) α) ⟹ Repeat n α
  | succ n, Fin2.fs i => dropRepeat _ i
  | succ n, Fin2.fz   => fun (a : α) => a

/-- projection for a repeat vector -/
def ofRepeat {α : Sort _} : ∀ {n i}, Repeat n α i → α
  | _, Fin2.fz   => fun (a : α) => a
  | _, Fin2.fs i => @ofRepeat _ _ i

theorem const_iff_true {α : TypeVec n} {i x p} : ofRepeat (TypeVec.const p α i x) ↔ p := 
by
  induction' i
  . rfl
  . rename_i n i i_ih
    erw [TypeVec.const, @i_ih (drop α) x]


-- variables  {F : typevec.{u} n → Type*} [mvfunctor F]
-- variable {α β γ : TypeVec.{u} n}
-- variable (p : α ⟹ Repeat n Prop) (r : α ⊗ α ⟹ Repeat n Prop)

/-- left projection of a `prod` vector -/
def Prod.fst : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ α
  | succ n, α, β, Fin2.fs i => @fst _ (drop α) (drop β) i
  | succ n, α, β, Fin2.fz => Prod.fst

/-- right projection of a `prod` vector -/
def Prod.snd : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ β
  | succ n, α, β, Fin2.fs i => @snd _ (drop α) (drop β) i
  | succ n, α, β, Fin2.fz => Prod.snd

/-- introduce a product where both components are the same -/
def Prod.diag : ∀ {n} {α : TypeVec.{u} n}, α ⟹ α ⊗ α
  | succ n, α, Fin2.fs i, x => @diag _ (drop α) _ x
  | succ n, α, Fin2.fz, x => (x, x)

/-- constructor for `prod` -/
def Prod.mk : ∀ {n} {α β : TypeVec.{u} n} i : Fin2 n, α i → β i → (α ⊗ β) i
  | succ n, α, β, Fin2.fs i => mk (α := fun i => α i.fs) (β := fun i => β i.fs) i
  | succ n, α, β, Fin2.fz => Prod.mk


@[simp]
theorem prod_fst_mk {α β : TypeVec.{u} n} (i : Fin2 n) (a : α i) (b : β i) : 
  TypeVec.Prod.fst i (Prod.mk i a b) = a := 
by
  induction i
  simp_all only [Prod.fst, Prod.mk]
  rename_i i i_ih
  apply i_ih



@[simp]
theorem prod_snd_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) : 
  TypeVec.Prod.snd i (Prod.mk i a b) = b := 
by
  induction i
  simp_all [Prod.snd, Prod.mk]
  rename_i i i_ih
  apply i_ih



/-- `prod` is functorial -/
protected def Prod.map : ∀ {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β → α' ⟹ β' → α ⊗ α' ⟹ β ⊗ β'
  | succ n, α, α', β, β', x, y, Fin2.fs i, a =>
    @Prod.map _ (drop α) (drop α') (drop β) (drop β') (dropFun x) (dropFun y) _ a
  | succ n, α, α', β, β', x, y, Fin2.fz, a => (x _ a.1, y _ a.2)

-- mathport name: «expr ⊗' »
infixl:45 " ⊗' " => TypeVec.Prod.map


theorem fst_prod_mk {α α' β β' : TypeVec.{u} n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.Prod.fst ⊚ (f ⊗' g) = f ⊚ TypeVec.Prod.fst := 
by
  ext i
  intros
  induction i
  rfl
  rename_i i i_ih α''
  apply i_ih

theorem snd_prod_mk {α α' β β' : TypeVec.{u} n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.Prod.snd ⊚ (f ⊗' g) = g ⊚ TypeVec.Prod.snd := 
by
  ext i
  intros
  induction i
  rfl
  rename_i i i_ih α'' 
  apply i_ih

theorem fst_diag {α : TypeVec.{u} n} : 
    TypeVec.Prod.fst ⊚ (Prod.diag : α ⟹ _) = id := 
by
  ext i
  intros
  induction i
  rfl
  rename_i i i_ih _
  apply i_ih

theorem snd_diag {α : TypeVec n} : 
    TypeVec.Prod.snd ⊚ (Prod.diag : α ⟹ _) = id := 
by
  ext i
  intros
  induction i
  rfl
  rename_i i i_ih _
  apply i_ih

theorem repeat_eq_iff_eq {α : TypeVec.{u} n} {i x y} : 
  ofRepeat (repeatEq α i (Prod.mk _ x y)) ↔ x = y := 
by
  induction i
  rfl
  rename_i i i_ih
  erw [repeatEq, i_ih]

/-- given a predicate vector `p` over vector `α`, `subtype_ p` is the type of vectors
that contain an `α` that satisfies `p` -/
def Subtype_ : ∀ {n} {α : TypeVec.{u} n} p : α ⟹ Repeat n Prop, TypeVec n
  | _, α, p, Fin2.fz => Subtype fun x => p Fin2.fz x
  | _, α, p, Fin2.fs i => Subtype_ (dropFun p) i

/-- projection on `subtype_` -/
def subtypeVal : ∀ {n} {α : TypeVec.{u} n} p : α ⟹ Repeat n Prop, Subtype_ p ⟹ α
  | succ n, α, p, Fin2.fs i => @subtypeVal n _ _ i
  | succ n, α, p, Fin2.fz => Subtype.val

/-- arrow that rearranges the type of `subtype_` to turn a subtype of vector into
a vector of subtypes -/
def toSubtype :
    ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ Repeat n Prop), 
      (fun i : Fin2 n => { x // ofRepeat <| p i x }) ⟹ Subtype_ p
  | succ n, α, p, Fin2.fs i, x => toSubtype (dropFun p) i x
  | succ n, α, p, Fin2.fz, x => x

/-- arrow that rearranges the type of `subtype_` to turn a vector of subtypes
into a subtype of vector -/
def ofSubtype :
    ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ Repeat n Prop), 
        Subtype_ p ⟹ fun i : Fin2 n => { x // ofRepeat <| p i x }
  | succ n, α, p, Fin2.fs i, x => ofSubtype _ i x
  | succ n, α, p, Fin2.fz, x => x

/-- similar to `to_subtype` adapted to relations (i.e. predicate on product) -/
def toSubtype' :
    ∀ {n} {α : TypeVec.{u} n} p : α ⊗ α ⟹ Repeat n Prop,
      (fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (Prod.mk _ x.1 x.2) }) ⟹ Subtype_ p
  | succ n, α, p, Fin2.fs i, x => toSubtype' (dropFun p) i x
  | succ n, α, p, Fin2.fz, x =>
    ⟨x.val,
      cast
        (by apply congrArg; simp [Prod.mk])
        x.property
    ⟩

/-- similar to `ofSubtype` adapted to relations (i.e. predicate on product) -/
def ofSubtype' :
    ∀ {n} {α : TypeVec.{u} n} p : α ⊗ α ⟹ Repeat n Prop,
      Subtype_ p ⟹ fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (Prod.mk _ x.1 x.2) }
  | _, α, p, Fin2.fs i, x => ofSubtype' _ i x
  | _, α, p, Fin2.fz, x =>
    ⟨x.val,
      cast
        (by apply congrFun; simp [Prod.mk])
        x.property
    ⟩

/-- similar to `diag` but the target vector is a `Subtype_`
guaranteeing the equality of the components -/
def diagSub : ∀ {n} {α : TypeVec.{u} n}, α ⟹ Subtype_ (repeatEq α)
  | succ n, α, Fin2.fs i, x => @diagSub _ (drop α) _ x
  | succ n, α, Fin2.fz, x => ⟨(x, x), rfl⟩

theorem subtype_val_nil {α : TypeVec.{u} 0} (ps : α ⟹ Repeat 0 Prop) : TypeVec.subtypeVal ps = nil_fun :=
  funext <| by
    rintro ⟨⟩ <;> rfl

theorem diag_sub_val {n} {α : TypeVec.{u} n} : 
  subtypeVal (repeatEq α) ⊚ diagSub = Prod.diag := 
by
  ext i
  induction i
  simp [Prod.diag, diagSub, repeatEq, subtypeVal, comp]
  rename_i i i_ih
  apply @i_ih (drop α)

theorem prod_id : ∀ {n} {α β : TypeVec.{u} n}, (id ⊗' id) = (id : α ⊗ β ⟹ _) := by
  intros
  ext i a
  induction i
  · cases a
    rfl    
  · rename_i i i_ih _ _
    apply i_ih
    
/- FIXME
theorem append_prod_append_fun  {n} 
                                {α α' β β' : TypeVec.{u} n} 
                                {φ φ' ψ ψ' : Type u}
                                {f₀ : α ⟹ α'}
                                {g₀ : β ⟹ β'}
                                {f₁ : φ → φ'}
                                {g₁ : ψ → ψ'} : 
        (f₀ ⊗' (g₀ ::: (Prod.map f₁ g₁))) = ((f₀ ::: f₁) ⊗' (g₀ ::: g₁)) := 
by
  ext i a
  cases i
  cases a
  rfl
-/



@[simp]
theorem drop_fun_diag {α} : 
  dropFun (@Prod.diag (n + 1) α) = Prod.diag :=
by
  ext i
  induction i
  all_goals
    simp [dropFun, Prod.diag, *]  


@[simp]
theorem drop_fun_subtype_val {α} (p : α ⟹ Repeat (n + 1) Prop) : 
  dropFun (subtypeVal p) = subtypeVal _ :=
  rfl

@[simp]
theorem last_fun_subtype_val {α} (p : α ⟹ Repeat (n + 1) Prop) : 
  lastFun (subtypeVal p) = Subtype.val :=
  rfl

@[simp]
theorem drop_fun_to_subtype {α} (p : α ⟹ Repeat (n + 1) Prop) : dropFun (toSubtype p) = toSubtype _ :=
by
  ext i
  cases i
  all_goals
    simp [dropFun, toSubtype, *]

@[simp]
theorem last_fun_to_subtype {α} (p : α ⟹ Repeat (n + 1) Prop) : lastFun (toSubtype p) = _root_.id := by
  ext i
  cases i
  simp [dropFun, lastFun, toSubtype, *]

@[simp]
theorem drop_fun_of_subtype {α} (p : α ⟹ Repeat (n + 1) Prop) : dropFun (ofSubtype p) = ofSubtype _ := by
  ext i
  cases i
  all_goals
    simp [dropFun, ofSubtype, *]

@[simp]
theorem last_fun_of_subtype {α} (p : α ⟹ Repeat (n + 1) Prop) : lastFun (ofSubtype p) = _root_.id := by
  ext i
  cases i
  simp [dropFun, lastFun, ofSubtype, *]

@[simp]
theorem drop_fun_relLast {α : TypeVec n} {β} (R : β → β → Prop) : dropFun (relLast' α R) = repeatEq α :=
  rfl

-- open_locale MvFunctor

@[simp]
theorem drop_fun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    dropFun (f ⊗' f') = (dropFun f ⊗' dropFun f') := 
by
  ext i
  cases i
  all_goals
    simp [dropFun, Prod.map, *]


@[simp]
theorem last_fun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    lastFun (f ⊗' f') = _root_.Prod.map (lastFun f) (lastFun f') := 
by
  ext i
  cases i
  simp [lastFun, *]
  rfl

@[simp]
theorem drop_fun_from_Vec.append1_drop_last {α : TypeVec (n + 1)} : dropFun (@from_Vec.append1_drop_last _ α) = id :=
  rfl

@[simp]
theorem last_fun_from_Vec.append1_drop_last {α : TypeVec (n + 1)} : lastFun (@from_Vec.append1_drop_last _ α) = _root_.id :=
  rfl

@[simp]
theorem drop_fun_id {α : TypeVec (n + 1)} : dropFun (@TypeVec.id _ α) = id :=
  rfl

@[simp]
theorem prod_map_id {α β : TypeVec n} : (@TypeVec.id _ α ⊗' @TypeVec.id _ β) = id := by
  ext i
  induction i
  all_goals
    intro x
    simp only [TypeVec.Prod.map, *, drop_fun_id]
  rfl
  skip
  simp [Prod.map, id]

@[simp]
theorem subtype_val_diag_sub {α : TypeVec n} : subtypeVal (repeatEq α) ⊚ diagSub = Prod.diag := 
by
  ext i
  induction i
  . simp [comp, diagSub, subtypeVal, Prod.diag]
  . rename_i i i_ih
    simp [Prod.diag]
    simp [comp, diagSub, subtypeVal, Prod.diag] at *
    apply @i_ih (drop _)

  all_goals
    intro x
    simp [comp, diagSub, subtypeVal, Prod.diag, *]

@[simp]
theorem to_subtype_of_subtype {α : TypeVec.{u} n} (p : α ⟹ Repeat n Prop) : 
    toSubtype p ⊚ ofSubtype p = id := 
by
  ext i x
  induction i
  all_goals
    simp only [id, toSubtype, comp, ofSubtype, dropFun] at *
  rename_i α' p' i_ih 
  apply i_ih
  

@[simp]
theorem subtype_val_to_subtype {α : TypeVec n} (p : α ⟹ Repeat n Prop) :
    subtypeVal p ⊚ toSubtype p = fun _ => Subtype.val := 
by
  ext i x
  induction i
  all_goals
    simp only [toSubtype, comp, subtypeVal]  at *
  rename_i α' p' i_ih 
  apply i_ih

@[simp]
theorem to_subtype_of_subtype_assoc {α β : TypeVec n} (p : α ⟹ Repeat n Prop) (f : β ⟹ Subtype_ p) :
    @toSubtype n _ p ⊚ ofSubtype _ ⊚ f = f := 
by
  rw [← comp_assoc, to_subtype_of_subtype]
  simp

@[simp]
theorem to_subtype'_of_subtype' {α : TypeVec n} (r : α ⊗ α ⟹ Repeat n Prop) : 
    toSubtype' r ⊚ ofSubtype' r = id := 
by
  ext i x <;> induction i <;> simp only [id, toSubtype', comp, ofSubtype']  at * <;> simp [Subtype.eta, *]

theorem subtype_val_to_subtype' {α : TypeVec n} (r : α ⊗ α ⟹ Repeat n Prop) :
    subtypeVal r ⊚ toSubtype' r = fun i x => Prod.mk i x.1.fst x.1.snd := 
by
  ext i x <;> induction i <;> simp only [id, toSubtype', comp, subtypeVal, Prod.mk]  at * <;> simp [*]


end TypeVec


/-
Support for extending a TypeVec by one element.
-/
namespace Eq

theorem mp_mpr {α β : Type _} (h : α = β) (x : β) :
  Eq.mp h (Eq.mpr h x) = x :=
by induction h; rfl

theorem mpr_mp {α β : Type _} (h : α = β) (x : α) :
  Eq.mpr h (Eq.mp h x) = x :=
by induction h; rfl

end Eq

