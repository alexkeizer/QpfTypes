import Qpf.Util.Fin
import Lean.Elab.Tactic.Conv


/--
n-tuples, as a category
-/
def Vec (α : Type _) (n : Nat)
  := fin' n → α

/--
n-tuples of types, as a category
-/
def TypeVec := Vec (Type _)

namespace TypeVec

  variable {n : Nat}

  /-- 
    An arrow between `TypeVec n`s consists of `n` arrows, 
    each from the `i`th type of the source `TypeVec` to the `i`th type of the target `TypeVec`
  -/
  def arrow (α β : TypeVec n) := ∀ i : fin' n, α i → β i

  infixl:40 " ⟹ " => arrow

  /-- Identity arrow of `TypeVec` -/
  def id {α : TypeVec n} : α ⟹ α := λ i x => x

  /-- Composition of `TypeVec` arrows -/
  def comp {α β γ : TypeVec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ :=
  λ i x => g i (f i x)

  infixr:80 " ⊚ " => TypeVec.comp   -- type as \oo

  
  @[simp] theorem id_comp {α β : TypeVec n} (f : α ⟹ β) : id ⊚ f = f := rfl

  @[simp] theorem comp_id {α β : TypeVec n} (f : α ⟹ β) : f ⊚ id = f := rfl

  theorem comp_assoc {α β γ δ : TypeVec n} (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
    (h ⊚ g) ⊚ f = h ⊚ g ⊚ f := rfl


  /-- Appends a single type to a `TypeVec` -/
  def append1 (α : TypeVec n) (β : Type _) : TypeVec (n+1)
  | (fin'.raise i) => α i
  | fin'.last      => β

  infixl:67 " ::: " => append1

  /-- Drop the last type from a `TypeVec` -/
  def drop (α : TypeVec (n+1)) : TypeVec n := λ i => α i.raise

  /-- Return the last type from a `TypeVec` -/
  def last (α : TypeVec (n+1)) : Type _ := α fin'.last

  theorem drop_append1 {α : TypeVec n} {β : Type _} {i : fin' n} : drop (append1 α β) i = α i := rfl

  theorem drop_append1' {α : TypeVec n} {β : Type _} : drop (append1 α β) = α :=
  by funext x; apply drop_append1

  theorem last_append1 {α : TypeVec n} {β : Type _} : last (append1 α β) = β := rfl

  @[simp]
  theorem append1_drop_last (α : TypeVec (n+1)) : append1 (drop α) (last α) = α :=
  funext $ λ i => by cases i; rfl; rfl

  -- @[elab_as_eliminator] 
  def append1_cases
    {C : TypeVec (n+1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ :=
  by rw [← @append1_drop_last _ γ]; apply H

  @[simp] theorem append1_cases_append1 {C : TypeVec (n+1) → Sort u}
    (H : ∀ α β, C (append1 α β)) (α β) :
    @append1_cases _ C H (append1 α β) = H α β := rfl


  def split_fun {α α' : TypeVec (n+1)}
    (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
  | (fin'.raise i) => f i
  | fin'.last      => g

  def append_fun {α α' : TypeVec n} {β β' : Type _}
    (f : α ⟹ α') (g : β → β') : append1 α β ⟹ append1 α' β' := split_fun f g

  infixl:66 " ::: " => append_fun

  def drop_fun {α β : TypeVec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β :=
  λ i => f i.raise

  def last_fun {α β : TypeVec (n+1)} (f : α ⟹ β) : last α → last β :=
  f fin'.last

  theorem eq_of_drop_last_eq {α β : TypeVec (n+1)} {f g : α ⟹ β}
    (h₀ : ∀ j, drop_fun f j = drop_fun g j) (h₁ : last_fun f = last_fun g) : f = g :=
  by funext i; cases i; apply h₀; apply h₁

  @[simp] theorem drop_fun_split_fun {α α' : TypeVec (n+1)}
    (f : drop α ⟹ drop α') (g : last α → last α') :
    drop_fun (split_fun f g) = f := rfl

  def arrow.mp {α β : TypeVec n} (h : α = β) : α ⟹ β
  | i => Eq.mp (congrFun h _)

  def arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
  | i => Eq.mpr (congrFun h _)

  def to_append1_drop_last {α : TypeVec (n+1)} : α ⟹ drop α ::: last α :=
  arrow.mpr (append1_drop_last _)

  @[simp] theorem last_fun_split_fun {α α' : TypeVec (n+1)}
    (f : drop α ⟹ drop α') (g : last α → last α') :
    last_fun (split_fun f g) = g := rfl

  @[simp] theorem drop_fun_append_fun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    drop_fun (f ::: g) = f := rfl

  @[simp] theorem last_fun_append_fun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    last_fun (f ::: g) = g := rfl

  theorem split_drop_fun_last_fun {α α' : TypeVec (n+1)} (f : α ⟹ α') :
    split_fun (drop_fun f) (last_fun f) = f :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  theorem split_fun_inj
    {α α' : TypeVec (n+1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
    (H : split_fun f g = split_fun f' g') : f = f' ∧ g = g' :=
  by rw [← drop_fun_split_fun f g, H, ← last_fun_split_fun f g, H]; simp

  /-- The unique arrow between empty `TypeVec`s -/
  def nil_fun {α β : TypeVec 0} : α ⟹ β :=
  λ i => fin'.elim0 i

  -- def nil_fun_elim {α β : TypeVec 0} : fin'.elim0 ⟹ fin'.elim0 :=
  -- λ i => fin'.elim0 i

  /-- `nil_fun` is indeed the unique arrow between `TypeVec 0`s -/
  @[simp] theorem nil_fun_uniq {α β : TypeVec 0} (f : α ⟹ β) : f = nil_fun :=
  by funext i; cases i

  @[simp] theorem nil_fun_uniq' (f : fin'.elim0 ⟹ fin'.elim0) : f = nil_fun :=
  by funext i; cases i

  theorem append_fun_inj {α α' : TypeVec n} {β β' : Type _} {f f' : α ⟹ α'} {g g' : β → β'} :
    f ::: g = f' ::: g' →  f = f' ∧ g = g' :=
  split_fun_inj

  theorem split_fun_comp {α₀ α₁ α₂ : TypeVec (n+1)}
      (f₀ : drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂)
      (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
    split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) = split_fun f₁ g₁ ⊚ split_fun f₀ g₀ :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  /- FIXME
  theorem append_fun_comp_split_fun
    {α γ : TypeVec n} {β δ : Type _} {ε : TypeVec (n + 1)}
      (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ)
      (g₀ : last ε → β) (g₁ : β → δ) :
    append_fun f₁ g₁ ⊚ split_fun f₀ g₀ = split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
  (split_fun_comp _ _ _ _).symm
  -/

  theorem append_fun_comp {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type _}
      (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    f₁ ⊚ f₀ ::: g₁ ∘ g₀ = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  theorem append_fun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type _}
      (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = f₁ ⊚ f₀ ::: g₁ ∘ g₀ :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  theorem nil_fun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ fin'.elim0) : nil_fun ⊚ f₀ = f₀ :=
  funext $ λ x => fin'.elim0 x

  theorem append_fun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type _}
      (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    @id _ α ::: g₁ ∘ g₀ = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  @[simp]
  theorem drop_fun_comp {α₀ α₁ α₂ : TypeVec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    drop_fun (f₁ ⊚ f₀) = drop_fun f₁ ⊚ drop_fun f₀ := rfl

  @[simp]
  theorem last_fun_comp {α₀ α₁ α₂ : TypeVec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    last_fun (f₁ ⊚ f₀) = last_fun f₁ ∘ last_fun f₀ := rfl

  theorem append_fun_aux {α α' : TypeVec n} {β β' : Type _}
    (f : α ::: β ⟹ α' ::: β') : drop_fun f ::: last_fun f = f :=
  eq_of_drop_last_eq (λ _ => rfl) rfl

  theorem append_fun_id_id {α : TypeVec n} {β : Type _} :
    @id n α ::: @_root_.id β = id :=
  eq_of_drop_last_eq (λ _ => rfl) rfl


  instance Subsingleton0 : Subsingleton (TypeVec 0) :=
  ⟨ λ a b => funext $ λ a => fin'.elim0 a  ⟩


  -- run_cmd mk_simp_attr `TypeVec
  -- attribute [TypeVec]

  set_option quotPrecheck false
  local prefix:0 "♯" => cast (by simp; apply congrArg <|> skip; simp <|> skip)

  def typevec_cases_nil {β : TypeVec 0 → Sort _} (f : β fin'.elim0) :
    ∀ v, β v :=
  λ v => cast (by apply congrArg; apply fin'.eq_fn0) f
  -- λ v => ♯ f

  def typevec_cases_cons (n : Nat) {β : TypeVec (n+1) → Sort _} (f : ∀ t (v : TypeVec n), β (v ::: t)) :
    ∀ v, β v :=
  λ v => cast (by simp) (f v.last v.drop)
  -- λ v => ♯ f v.last v.drop

  theorem typevec_cases_nil_append1 {β : TypeVec 0 → Sort _} (f : β fin'.elim0) :
    typevec_cases_nil f fin'.elim0 = f := rfl

  theorem typevec_cases_cons_append1 (n : Nat) {β : TypeVec (n+1) → Sort _}
        (f : ∀ t (v : TypeVec n), β (v ::: t))
        (v : TypeVec n) (α) :
    typevec_cases_cons n f (v ::: α) = f α v := rfl

  @[simp] def eq0 (f : TypeVec 0) : f = @fin'.elim0 (Type _)
  := by apply fin'.eq_fn0

  /-- FIXME 
  def typevec_cases_nil₃ {β : ∀ v v' : TypeVec 0, v ⟹ v' → Sort _} (f : β fin'.elim0 fin'.elim0 nil_fun) :
    ∀ v v' f, β v v' f :=
  λ v v' fs => cast (
    by 
       congr
       simp [veq, v'eq]
  ) f
  begin
    refine cast _ f; congr; ext; try { intros; exact fin'.elim0 ‹ fin' 0 ›  }; refl
  end
  -/

  def typevec_cases_cons₃ (n : Nat) {β : ∀ v v' : TypeVec (n+1), v ⟹ v' → Sort _}
    (F : ∀ t t' (f : t → t') (v v' : TypeVec n) (fs : v ⟹ v'), β (v ::: t) (v' ::: t') (fs ::: f)) :
    ∀ v v' fs, β v v' fs :=
  by 
    intros v v'
    rw [←append1_drop_last v, ←append1_drop_last v']
    intro fs
    rw [←split_drop_fun_last_fun fs]
    apply F

  def typevec_cases_nil₂ {β : fin'.elim0 ⟹ fin'.elim0 → Sort _}
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

  theorem typevec_cases_nil₂_append_fun {β : fin'.elim0 ⟹ fin'.elim0 → Sort _}
    (f : β nil_fun) :
    typevec_cases_nil₂ f nil_fun = f := rfl

  theorem typevec_cases_cons₂_append_fun (n : Nat) (t t' : Type _) (v v' : TypeVec (n)) {β : (v ::: t) ⟹ (v' ::: t') → Sort _}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) (f fs) :
    typevec_cases_cons₂ n t t' v v' F (fs ::: f) = F f fs := rfl

  /- for lifting predicates and relations -/

  /-- `pred_last α p x` predicates `p` of the last element of `x : α.append1 β`. -/
  def pred_last (α : TypeVec n) {β : Type _} (p : β → Prop) : ∀ ⦃i⦄, (α.append1 β) i → Prop
  | (fin'.raise i) => λ x => true
  | fin'.last      => p

  /-- `rel_last α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and all the other elements are equal. -/
  def rel_last (α : TypeVec n) {β γ : Type _} (r : β → γ → Prop) :
    ∀ ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop
  | (fin'.raise i) => Eq
  | fin'.last      => r

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