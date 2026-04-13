/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

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

This file is a modified version of `Mathlib.Data.TypeVec`, with `Fin2` replaced by `Fin`
throughout.
-/
@[expose] public section

universe u v w x

namespace QPFTypes

/-- n-tuples of types, as a category -/
def TypeVec (n : Nat) :=
  Fin n → Type _

instance {n} : Inhabited (TypeVec.{u} n) :=
  ⟨fun _ => PUnit⟩

/-- arrow in the category of `TypeVec` -/
def TypeVec.Arrow (α : TypeVec.{u} n) (β : TypeVec.{v} n) :=
  ∀ i : Fin n, α i → β i

@[inherit_doc] scoped infixl:40 " ⟹ " => TypeVec.Arrow

variable {n : Nat}

namespace TypeVec

section
variable {α : TypeVec.{u} n} {β : TypeVec.{v} n} {γ : TypeVec.{w} n} {δ : TypeVec.{x} n}

/-- Extensionality for arrows -/
@[ext]
theorem Arrow.ext (f g : α ⟹ β) :
    (∀ i, f i = g i) → f = g := by
  intro h; funext i; apply h

instance Arrow.inhabited (α β : TypeVec n) [∀ i, Inhabited (β i)] : Inhabited (α ⟹ β) :=
  ⟨fun _ _ => default⟩

/-- identity of arrow composition -/
def id {α : TypeVec n} : α ⟹ α := fun _ x => x

/-- arrow composition in the category of `TypeVec` -/
@[grind]
def comp (g : β ⟹ γ) (f : α ⟹ β)
    : α ⟹ γ :=
  fun i x => g i (f i x)

@[inherit_doc] scoped infixr:80 " ⊚ " => TypeVec.comp -- type as \oo

@[simp, grind =]
theorem id_comp (f : α ⟹ β) : id ⊚ f = f :=
  rfl

@[simp, grind =]
theorem comp_id (f : α ⟹ β) : f ⊚ id = f :=
  rfl

@[grind =]
theorem comp_assoc
    (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
    (h ⊚ g) ⊚ f = h ⊚ g ⊚ f :=
  rfl
end

/-- Support for extending a `TypeVec` by one element.
  At index `0` (i.e. `Fin2.fz`) returns `β`; at index `i.succ` (i.e. `Fin2.fs i`) returns `α i`. -/
def append1 (α : TypeVec n) (β : Type _) : TypeVec (n + 1) :=
  Fin.cases β α

end TypeVec

@[inherit_doc] scoped infixl:67 " ::: " => TypeVec.append1

namespace TypeVec

def nil : TypeVec 0 :=
  Fin.elim0

/-- retain only a `n-length` prefix of the argument -/
def drop (α : TypeVec.{u} (n + 1)) : TypeVec n := fun i => α i.succ

/-- take the last value of a `(n+1)-length` vector -/
def last (α : TypeVec.{u} (n + 1)) : Type _ :=
  α 0

/--
Extend a `TypeVec` with a new element at the _front_ of the list.
-/
def cons (α : Type u) (αs : TypeVec.{u} n) : TypeVec (n + 1) :=
  Fin.lastCases α αs
@[inherit_doc] infixr:67 " <: " => cons

/-- take the first value of a `(n+1)-length` vector -/
def head (α : TypeVec.{u} (n + 1)) : Type _ :=
  α (.last _)

/-- retain only a `n-length` _suffix_ of the argument -/
def tail (α : TypeVec.{u} (n + 1)) : TypeVec n := fun i => α i.castSucc

instance last.inhabited (α : TypeVec (n + 1)) [Inhabited (α 0)] : Inhabited (last α) :=
  ⟨show α 0 from default⟩

theorem drop_append1 {α : TypeVec n} {β : Type _} {i : Fin n} : drop (append1 α β) i = α i := by
  simp [drop, append1, Fin.cases_succ]

theorem drop_append1' {α : TypeVec n} {β : Type _} : drop (append1 α β) = α :=
  funext fun _ => drop_append1

theorem last_append1 {α : TypeVec n} {β : Type _} : last (append1 α β) = β := by
  simp [last, append1, Fin.cases_zero]

@[simp]
theorem append1_drop_last (α : TypeVec (n + 1)) : append1 (drop α) (last α) = α := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [append1, last, Fin.cases_zero]
  · intro j
    simp [append1, drop, Fin.cases_succ]

/-- cases on `(n+1)-length` vectors -/
@[elab_as_elim]
def append1Cases {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ := by
  rw [← @append1_drop_last _ γ]; apply H

@[simp]
theorem append1_cases_append1 {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (α β) :
    @append1Cases _ C H (append1 α β) = H α β :=
  rfl

/-- append an arrow and a function for arbitrary source and target type vectors -/
def splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α' :=
  Fin.cases g f

/-- append an arrow and a function as well as their respective source and target types / typevecs -/
def appendFun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    append1 α β ⟹ append1 α' β' :=
  splitFun f g

end TypeVec

@[inherit_doc] scoped infixl:0 " ::: " => TypeVec.appendFun

namespace TypeVec

/-- split off the prefix of an arrow -/
def dropFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : drop α ⟹ drop β := fun i => f i.succ

/-- split off the last function of an arrow -/
def lastFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : last α → last β :=
  f 0

/-- arrow in the category of `0-length` vectors -/
def nilFun {α : TypeVec 0} {β : TypeVec 0} : α ⟹ β := fun i => i.elim0

theorem eq_of_drop_last_eq {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f = dropFun g)
    (h₁ : lastFun f = lastFun g) : f = g := by
  refine funext (fun x => ?_)
  refine Fin.cases ?_ ?_ x
  · apply h₁
  · intro j
    apply congrFun h₀

@[simp]
theorem dropFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    dropFun (splitFun f g) = f := by
  funext i
  simp [dropFun, splitFun, Fin.cases_succ]

/-- turn an equality into an arrow -/
def Arrow.mp {α β : TypeVec n} (h : α = β) : α ⟹ β
  | _ => Eq.mp (congrFun h _)

/-- turn an equality into an arrow, with reverse direction -/
def Arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
  | _ => Eq.mpr (congrFun h _)

/-- decompose a vector into its prefix appended with its last element -/
def toAppend1DropLast {α : TypeVec (n + 1)} : α ⟹ (drop α ::: last α) :=
  Arrow.mpr (append1_drop_last _)

/-- stitch two bits of a vector back together -/
def fromAppend1DropLast {α : TypeVec (n + 1)} : (drop α ::: last α) ⟹ α :=
  Arrow.mp (append1_drop_last _)

@[simp, grind =]
theorem lastFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    lastFun (splitFun f g) = g := by
  simp [lastFun, splitFun, Fin.cases_zero]

@[simp, grind =]
theorem dropFun_appendFun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    dropFun (f ::: g) = f := rfl

@[simp]
theorem lastFun_appendFun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    lastFun (f ::: g) = g := rfl

theorem split_dropFun_lastFun {α α' : TypeVec (n + 1)} (f : α ⟹ α') :
    splitFun (dropFun f) (lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl

theorem splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
    (H : splitFun f g = splitFun f' g') : f = f' ∧ g = g' := by
  rw [← dropFun_splitFun f g, H, ← lastFun_splitFun f g, H]; simp

theorem appendFun_inj {α α' : TypeVec n} {β β' : Type _} {f f' : α ⟹ α'} {g g' : β → β'} :
    (f ::: g : (α ::: β) ⟹ _) = (f' ::: g' : (α ::: β) ⟹ _)
    → f = f' ∧ g = g' :=
  splitFun_inj

theorem splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁)
    (f₁ : drop α₁ ⟹ drop α₂) (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
    splitFun (f₁ ⊚ f₀) (g₁ ∘ g₀) = splitFun f₁ g₁ ⊚ splitFun f₀ g₀ :=
  eq_of_drop_last_eq rfl rfl

@[simp, grind =]
theorem appendFun_comp_splitFun {α γ : TypeVec n} {β δ : Type _} {ε : TypeVec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last ε → β) (g₁ : β → δ) :
    appendFun f₁ g₁ ⊚ splitFun f₀ g₀ = splitFun (α' := γ.append1 δ) (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
  (splitFun_comp _ _ _ _).symm

@[grind =, grind =_]
theorem appendFun_comp {α₀ α₁ α₂ : TypeVec n}
    {β₀ β₁ β₂ : Type _}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ⊚ f₀ ::: g₁ ∘ g₀) = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

theorem appendFun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type _}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = (f₁ ⊚ f₀ ::: g₁ ∘ g₀) :=
  eq_of_drop_last_eq rfl rfl

theorem nilFun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin.elim0) : nilFun ⊚ f₀ = f₀ :=
  funext fun i => i.elim0

@[grind =]
theorem appendFun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type u} (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

@[simp]
theorem dropFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    dropFun (f₁ ⊚ f₀) = dropFun f₁ ⊚ dropFun f₀ :=
  rfl

@[simp]
theorem lastFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    lastFun (f₁ ⊚ f₀) = lastFun f₁ ∘ lastFun f₀ :=
  rfl

theorem appendFun_aux {α α' : TypeVec n} {β β' : Type _} (f : (α ::: β) ⟹ (α' ::: β')) :
    (dropFun f ::: lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl

@[simp, grind =]
theorem appendFun_id_id {α : TypeVec n} {β : Type _} :
    (@TypeVec.id n α ::: @_root_.id β) = TypeVec.id :=
  eq_of_drop_last_eq rfl rfl

instance subsingleton0 : Subsingleton (TypeVec 0) :=
  ⟨fun _ _ => funext fun i => i.elim0⟩

/-- cases distinction for 0-length type vector -/
protected def casesNil {β : TypeVec 0 → Sort _} (f : β Fin.elim0) : ∀ v, β v :=
  fun v => cast (by congr; funext i; exact i.elim0) f

/-- cases distinction for (n+1)-length type vector -/
protected def casesCons (n : Nat) {β : TypeVec (n + 1) → Sort _}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) :
    ∀ v, β v :=
  fun v : TypeVec (n + 1) => cast (by simp) (f v.last v.drop)

protected theorem casesNil_append1 {β : TypeVec 0 → Sort _} (f : β Fin.elim0) :
    TypeVec.casesNil f Fin.elim0 = f :=
  rfl

protected theorem casesCons_append1 (n : Nat) {β : TypeVec (n + 1) → Sort _}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) (v : TypeVec n) (α) :
    TypeVec.casesCons n f (v ::: α) = f α v :=
  rfl

/-- cases distinction for an arrow in the category of 0-length type vectors -/
def typevecCasesNil₃ {β : ∀ v v' : TypeVec 0, v ⟹ v' → Sort _}
    (f : β Fin.elim0 Fin.elim0 nilFun) :
    ∀ v v' fs, β v v' fs := fun v v' fs => by
  refine cast ?_ f
  have eq₁ : v = Fin.elim0 := by funext i; exact i.elim0
  have eq₂ : v' = Fin.elim0 := by funext i; exact i.elim0
  have eq₃ : fs = nilFun := by funext i; exact i.elim0
  cases eq₁; cases eq₂; cases eq₃; rfl

/-- cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevecCasesCons₃ (n : Nat) {β : ∀ v v' : TypeVec (n + 1), v ⟹ v' → Sort _}
    (F : ∀ (t t') (f : t → t') (v v' : TypeVec n) (fs : v ⟹ v'),
    β (v ::: t) (v' ::: t') (fs ::: f)) :
    ∀ v v' fs, β v v' fs := by
  intro v v'
  rw [← append1_drop_last v, ← append1_drop_last v']
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

/-- specialized cases distinction for an arrow in the category of 0-length type vectors -/
def typevecCasesNil₂ {β : Fin.elim0 ⟹ Fin.elim0 → Sort _} (f : β nilFun) : ∀ f, β f := by
  intro g
  suffices g = nilFun by rwa [this]
  ext i
  exact i.elim0

/-- specialized cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevecCasesCons₂ (n : Nat) (t t' : Type _) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort _}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) : ∀ fs, β fs := by
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

theorem typevecCasesNil₂_appendFun {β : Fin.elim0 ⟹ Fin.elim0 → Sort _} (f : β nilFun) :
    typevecCasesNil₂ f nilFun = f :=
  rfl

theorem typevecCasesCons₂_appendFun (n : Nat) (t t' : Type _) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort _}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f))
    (f fs) :
    typevecCasesCons₂ n t t' v v' F (fs ::: f) = F f fs :=
  rfl

-- for lifting predicates and relations
/-- `PredLast α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def PredLast (α : TypeVec n) {β : Type _} (p : β → Prop) : ∀ ⦃i⦄, (α.append1 β) i → Prop :=
  fun i => Fin.cases (motive := fun i => (α.append1 β) i → Prop) p (fun _ _ => True) i

/-- `RelLast α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r`
and all the other elements are equal. -/
def RelLast (α : TypeVec n) {β γ : Type u} (r : β → γ → Prop) :
    ∀ ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop :=
  fun i => Fin.cases (motive := fun i => (α.append1 β) i → (α.append1 γ) i → Prop)
    r (fun _ a b => a = b) i

section Liftp'

open Nat

/-- `repeat n t` is a `n-length` type vector that contains `n` occurrences of `t` -/
def «repeat» : ∀ (n : Nat), Type u → TypeVec n
  | 0, _ => Fin.elim0
  | Nat.succ i, t => append1 («repeat» i t) t

/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
def prod : ∀ {n}, TypeVec.{u} n → TypeVec.{u} n → TypeVec n
  | 0, _, _ => Fin.elim0
  | n + 1, α, β => (@prod n (drop α) (drop β)) ::: (last α × last β)

-- TODO: this ought to be scoped to the parent QPFTypes namespace
@[inherit_doc] scoped infixl:45 " ⊗ " => TypeVec.prod

/-- `const x α` is an arrow that ignores its source and constructs a `TypeVec` that
contains nothing but `x` -/
protected def const {β} (x : β) : ∀ {n} (α : TypeVec n), α ⟹ «repeat» _ β
  | 0, _, i => i.elim0
  | succ _, α, i =>
    Fin.cases (motive := fun i => α i → («repeat» (succ _) β) i)
      (fun _ => x)
      (fun j => TypeVec.const x (drop α) j)
      i

theorem const_append1 {β γ} (x : γ) {n} (α : TypeVec n) :
    TypeVec.const x (α ::: β) = appendFun (TypeVec.const x α) fun _ => x := rfl

theorem eq_nilFun {α β : TypeVec 0} (f : α ⟹ β) : f = nilFun := by
  ext x; exact x.elim0

theorem id_eq_nilFun {α : TypeVec 0} : @id _ α = nilFun := by
  ext x; exact x.elim0

theorem const_nil {β} (x : β) (α : TypeVec 0) : TypeVec.const x α = nilFun := by
  ext i : 1; exact i.elim0

/-- Projection from a repeat vector. Since `repeat n α` has `α` at every index,
this extracts the underlying `α` value. -/
def ofRepeat {α : Sort _} : ∀ {n : Nat} {i : Fin n}, «repeat» n α i → α
  | _ + 1, ⟨0, _⟩ => fun x => x
  | _ + 1, ⟨k + 1, hk⟩ => @ofRepeat α _ ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem const_iff_true : ∀ {n} {α : TypeVec n} {i : Fin n} {x p},
    ofRepeat (TypeVec.const p α i x) ↔ p
  | _ + 1, _, ⟨0, _⟩, _, _ => Iff.rfl
  | _ + 1, _, ⟨k + 1, hk⟩, _, _ => const_iff_true (i := ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

/-- given `F : TypeVec.{u} (n+1) → Type u`, `curry F : Type u → TypeVec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
def Curry (F : TypeVec.{u} (n + 1) → Type _) (α : Type u) (β : TypeVec.{u} n) : Type _ :=
  F (β ::: α)

instance Curry.inhabited (F : TypeVec.{u} (n + 1) → Type _) (α : Type u) (β : TypeVec.{u} n)
    [I : Inhabited (F <| (β ::: α))] : Inhabited (Curry F α β) :=
  I

section

/-- left projection of a `prod` vector -/
def prod.fst : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ α
  | 0, _, _, i => i.elim0
  | succ _, α, β, i =>
    Fin.cases (motive := fun i => (α ⊗ β) i → α i)
      Prod.fst
      (fun j => @prod.fst _ (drop α) (drop β) j)
      i

/-- right projection of a `prod` vector -/
def prod.snd : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ β
  | 0, _, _, i => i.elim0
  | succ _, α, β, i =>
    Fin.cases (motive := fun i => (α ⊗ β) i → β i)
      Prod.snd
      (fun j => @prod.snd _ (drop α) (drop β) j)
      i

/-- introduce a product where both components are the same -/
def prod.diag : ∀ {n} {α : TypeVec.{u} n}, α ⟹ α ⊗ α
  | 0, _, i => i.elim0
  | succ _, α, i =>
    Fin.cases (motive := fun i => α i → (α ⊗ α) i)
      (fun x => (x, x))
      (fun j => @prod.diag _ (drop α) j)
      i

/-- constructor for `prod` -/
def prod.mk : ∀ {n} {α β : TypeVec.{u} n} (i : Fin n), α i → β i → (α ⊗ β) i
  | 0, _, _, i => i.elim0
  | succ _, α, β, i =>
    Fin.cases (motive := fun i => α i → β i → (α ⊗ β) i)
      Prod.mk
      (fun j => @prod.mk _ (drop α) (drop β) j)
      i

end

@[simp]
theorem prod_fst_mk {α β : TypeVec n} (i : Fin n) (a : α i) (b : β i) :
    TypeVec.prod.fst i (prod.mk i a b) = a := by
  induction i using Fin.succRecOn with
  | zero n => simp [prod.fst, prod.mk]
  | succ n j ih => exact @ih (drop α) (drop β) a b

@[simp]
theorem prod_snd_mk {α β : TypeVec n} (i : Fin n) (a : α i) (b : β i) :
    TypeVec.prod.snd i (prod.mk i a b) = b := by
  induction i using Fin.succRecOn with
  | zero n => simp [prod.snd, prod.mk]
  | succ n j ih => exact @ih (drop α) (drop β) a b

/-- `prod` is functorial -/
protected def prod.map : ∀ {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β → α' ⟹ β' → α ⊗ α' ⟹ β ⊗ β'
  | 0, _, _, _, _, _, _, i => i.elim0
  | succ _, α, α', β, β', x, y, i =>
    Fin.cases (motive := fun i => (α ⊗ α') i → (β ⊗ β') i)
      (fun a => (x 0 a.1, y 0 a.2))
      (fun j => @prod.map _ (drop α) (drop α') (drop β) (drop β') (dropFun x) (dropFun y) j)
      i

-- TODO: this ought to be scoped to the parent QPFTypes namespace
@[inherit_doc] scoped infixl:45 " ⊗' " => TypeVec.prod.map

theorem fst_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.fst ⊚ (f ⊗' g) = f ⊚ TypeVec.prod.fst := by
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; cases a; rfl
  | succ n j ih => exact ih (dropFun f) (dropFun g)

theorem snd_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.snd ⊚ (f ⊗' g) = g ⊚ TypeVec.prod.snd := by
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; cases a; rfl
  | succ n j ih => exact ih (dropFun f) (dropFun g)

theorem fst_diag {α : TypeVec n} : TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id := by
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; rfl
  | succ n j ih => exact @ih (drop α)

theorem snd_diag {α : TypeVec n} : TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id := by
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; rfl
  | succ n j ih => exact @ih (drop α)

theorem prod_id : ∀ {n} {α β : TypeVec.{u} n}, (id ⊗' id) = (id : α ⊗ β ⟹ _) := by
  intro n α β
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; cases a; rfl
  | succ n j ih => exact @ih (drop α) (drop β)

theorem append_prod_appendFun {n} {α α' β β' : TypeVec.{u} n} {p p' q q' : Type u}
    {f₀ : α ⟹ α'} {g₀ : β ⟹ β'} {f₁ : p → p'} {g₁ : q → q'} :
    ((f₀ ⊗' g₀) ::: (_root_.Prod.map f₁ g₁)) = ((f₀ ::: f₁) ⊗' (g₀ ::: g₁)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · funext a; cases a; rfl
  · rfl

end Liftp'

@[simp]
theorem dropFun_diag {α} : dropFun (@prod.diag (n + 1) α) = prod.diag := by
  funext i
  simp [dropFun, prod.diag, Fin.cases_succ]

@[simp]
theorem dropFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    dropFun (f ⊗' f') = (dropFun f ⊗' dropFun f') := by
  funext i
  simp [dropFun, prod.map, Fin.cases_succ]

@[simp]
theorem lastFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    lastFun (f ⊗' f') = Prod.map (lastFun f) (lastFun f') := by
  simp only [lastFun, prod.map, Fin.cases_zero]
  funext ⟨a, b⟩; rfl

@[simp]
theorem dropFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    dropFun (@fromAppend1DropLast _ α) = id :=
  rfl

@[simp]
theorem lastFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    lastFun (@fromAppend1DropLast _ α) = _root_.id :=
  rfl

@[simp]
theorem dropFun_id {α : TypeVec (n + 1)} : dropFun (@TypeVec.id _ α) = id :=
  rfl

@[simp]
theorem prod_map_id {α β : TypeVec n} : (@TypeVec.id _ α ⊗' @TypeVec.id _ β) = id := prod_id

attribute [simp] drop_append1'

/-!
## Lemmas

This file is a bit disorganized,
but any _new_ lemmas will be added in this section
-/
section Lemmas

/-!
### nil
-/

theorem eq_nil (βs : TypeVec 0) : βs = nil := by
  funext i; exact i.elim0

instance : Subsingleton (TypeVec 0) where
  allEq a b := by rw [a.eq_nil, b.eq_nil]

/-!
### head / tail
-/
section HeadTail
variable (βs : TypeVec.{u} n) (β : Type u)

@[grind =] theorem head_append1 :
    (βs ::: β).head = match n with
      | 0 => β
      | _+1 => βs.head := by
  cases n <;> grind [append1, head]

@[grind =] theorem tail_append1 :
    (βs ::: β).tail = match n with
      | 0 => nil
      | _+1 => βs.tail ::: β := by
  funext i
  cases n
  · exact i.elim0
  · cases i using Fin.cases <;> grind [append1, tail]

@[simp, grind =] theorem head_cons : (β <: βs).head = β := by simp [head, cons]
@[simp, grind =] theorem tail_cons : (β <: βs).tail = βs := by
  funext i; simp [tail, cons]

@[simp, grind =] theorem cons_head_tail {βs : TypeVec (n+1)} :
    βs.head <: βs.tail = βs := by
  funext i; cases i using Fin.lastCases <;> simp [cons, head, tail]

end HeadTail

end Lemmas
end TypeVec
end QPFTypes

/-!
## Notes on Fin vs Fin2 API differences

The following `Fin` API is used where `Fin2` constructors/functions were used:
- `Fin.cases` replaces case analysis on `Fin2.fz`/`Fin2.fs` (for definitions and non-inductive proofs)
- `Fin.elim0` replaces `Fin2.elim0`
- `Fin.succ` replaces `Fin2.fs`
- `(0 : Fin (n+1))` replaces `Fin2.fz`

### Structural induction in proofs

`Fin2` supported structural induction directly:
```
induction i with
| fz => ...          -- base case: i = 0 : Fin2 (n+1), for any n
| fs n j ih => ...   -- step case: i = j.fs, IH for j : Fin2 n
```
whose key feature is that the motive `C : ∀ n, Fin2 n → Prop` quantifies over both `n` and the
index, so the IH is stated for a strictly smaller ambient dimension.

The direct `Fin` analog is `Fin.succRecOn` (argument-first) or `Fin.succRec` (argument-last), both
in core Lean 4 (`Init.Data.Fin.Lemmas`). Their motive also quantifies over both `n` and `i : Fin n`,
giving the same structural IH:
```
induction i using Fin.succRecOn with
| zero n => ...          -- base case: i = 0 : Fin (n+1), for any n
| succ n j ih => ...     -- step case: i = j.succ, IH for j : Fin n
```
Note that `n` in each branch is the *predecessor* dimension (so the `zero` branch has `i : Fin (n+1)`).
Variables depending on `n` (such as `TypeVec n`) are generalized automatically by the motive.

For *definitions*, direct pattern matching on `Fin` via `Fin.cases` (or `| ⟨0,_⟩ =>` / `| ⟨k+1,h⟩ =>`)
is cleaner than `Fin.succRec`, which is better suited to proofs.

### Direct analogs
- `Fin2.cases'` ↔ `Fin.cases` ✓
- `Fin2.elim0` ↔ `Fin.elim0` ✓
- Structural induction on `Fin2` ↔ `induction i using Fin.succRecOn` ✓
- No analog of `Fin2.toNat` needed — `Fin` already stores `.val : Nat`
-/
