/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

/-!
# Polynomial functors
This file defines polynomial functors and the W-type construction as a
polynomial functor.  (For the M-type construction, see
pfunctor/M.lean.)
-/

universe u

/--
A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P.obj α`, which is defined as the sigma type `Σ x, P.B x → α`.
An element of `P.obj α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/

structure PFunctor :=
(A : Type u) (B : A → Type u)

namespace PFunctor

  instance : Inhabited PFunctor := 
  ⟨⟨default, default⟩⟩

  variable (P : PFunctor) 
  variable {α β : Type u}

  /-- Applying `P` to an object of `Type` -/
  def obj (α : Type u)
    := Σ x : P.A, P.B x → α

  /-- Applying `P` to a morphism of `Type` -/
  def map (f : α → β) : obj P α → obj P β :=
    λ ⟨a, g⟩ => ⟨a, f ∘ g⟩


instance obj.Inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P.obj α) :=
 ⟨ ⟨ default, λ _ => default ⟩ ⟩

instance : Functor (P.obj) := {map := @map P}

protected theorem map_eq (f : α → β) (a : P.A) (g : P.B a → α) :
  @Functor.map (P.obj) _ _ _ f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
rfl

protected theorem id_map : ∀ x : P.obj α, id <$> x = id x :=
λ ⟨a, b⟩ => rfl

protected theorem comp_map (f : α → β) (g : β → γ) :
  ∀ x : P.obj α, (g ∘ f) <$> x = g <$> (f <$> x) :=
λ ⟨a, b⟩ => rfl

instance : LawfulFunctor (P.obj) :=
{
  map_const := rfl,
  id_map := @PFunctor.id_map P, 
  comp_map := @PFunctor.comp_map P
}



/-- `Idx` identifies a location inside the application of a PFunctor.
For `F : PFunctor`, `x : F.obj α` and `i : F.Idx`, `i` can designate
one part of `x` or is invalid, if `i.1 ≠ x.1` -/
def Idx := Σ x : P.A, P.B x

instance Idx.Inhabited [Inhabited P.A] [Inhabited (P.B default)] : Inhabited P.Idx :=
⟨ ⟨default, default⟩ ⟩

-- Make the variable P implicit
variable {P}

/-- `x.iget i` takes the component of `x` designated by `i` if any is or returns
a default value -/
def obj.iget [DecidableEq P.A] {α} [_root_.Inhabited α] (x : P.obj α) (i : P.Idx) : α :=
if h : i.1 = x.1
  then x.2 (cast (congrArg _ h) i.2)
  else default

@[simp]
theorem fst_map {α β : Type u} (x : P.obj α) (f : α → β) :
  (f <$> x).1 = x.1 := by { cases x; rfl }

@[simp]
theorem iget_map [DecidableEq P.A] {α β : Type u} [Inhabited α] [Inhabited β]
  (x : P.obj α) (f : α → β) (i : P.Idx)
  (h : i.1 = x.1) :
  (f <$> x).iget i = f (x.iget i) :=
by simp only [obj.iget, fst_map, *, dif_pos]
   cases x
   rfl 
   


end PFunctor

/-
## Composition of polynomial functors.
-/
namespace PFunctor

/-- functor composition for polynomial functors -/
def comp (P₂ P₁ : PFunctor.{u}) : PFunctor.{u} :=
⟨ Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1,
  λ a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u) ⟩

/-- constructor for composition -/
def comp.mk (P₂ P₁ : PFunctor.{u}) {α : Type} (x : P₂.obj (P₁.obj α)) : (comp P₂ P₁).obj α :=
⟨ ⟨ x.1, Sigma.fst ∘ x.2 ⟩, λ a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2  ⟩

/-- destructor for composition -/
def comp.get (P₂ P₁ : PFunctor.{u}) {α : Type} (x : (comp P₂ P₁).obj α) : P₂.obj (P₁.obj α) :=
⟨ x.1.1, λ a₂ => ⟨x.1.2 a₂, λ a₁ => x.2 ⟨a₂,a₁⟩ ⟩ ⟩

end PFunctor

/-
## Lifting predicates and relations.
-/

-- FIXME

-- namespace PFunctor
-- variable {P : PFunctor.{u}}
-- open Functor

-- theorem liftp_iff {α : Type u} (p : α → Prop) (x : P.obj α) :
--   liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i, p (f i) :=
-- begin
--   split,
--   { rintros ⟨y, hy⟩, cases h : y with a f,
--     refine ⟨a, λ i, (f i).val, _, λ i, (f i).property⟩,
--     rw [←hy, h, PFunctor.map_eq] },
--   rintros ⟨a, f, xeq, pf⟩,
--   use ⟨a, λ i, ⟨f i, pf i⟩⟩,
--   rw [xeq], reflexivity
-- end

-- theorem liftp_iff' {α : Type u} (p : α → Prop) (a : P.A) (f : P.B a → α) :
--   @liftp.{u} P.obj _ α p ⟨a,f⟩ ↔ ∀ i, p (f i) :=
-- begin
--   simp only [liftp_iff, sigma.mk.inj_iff]; split; intro,
--   { casesm* [Exists _, _ ∧ _], subst_vars, assumption },
--   repeat { constructor <|> assumption }
-- end

-- theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P.obj α) :
--   liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) :=
-- begin
--   split,
--   { rintros ⟨u, xeq, yeq⟩, cases h : u with a f,
--     use [a, λ i, (f i).val.fst, λ i, (f i).val.snd],
--     split, { rw [←xeq, h], refl },
--     split, { rw [←yeq, h], refl },
--     intro i, exact (f i).property },
--   rintros ⟨a, f₀, f₁, xeq, yeq, h⟩,
--   use ⟨a, λ i, ⟨(f₀ i, f₁ i), h i⟩⟩,
--   split,
--   { rw [xeq], refl },
--   rw [yeq], refl
-- end

-- open set

-- theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) :
--   @supp.{u} P.obj _ α  (⟨a,f⟩ : P.obj α) = f '' univ :=
-- begin
--   ext, simp only [supp, image_univ, mem_range, mem_set_of_eq],
--   split; intro h,
--   { apply @h (λ x, ∃ (y : P.B a), f y = x),
--     rw liftp_iff', intro, refine ⟨_,rfl⟩ },lake print-paths Init Qpf.PFunctor Qpf.W Qpf.M Qpf.Example.List
--   { simp only [liftp_iff'], cases h, subst x,
--     tauto }
-- end

-- end PFunctor