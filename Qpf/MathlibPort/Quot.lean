
namespace Quot

/-- weaken the relation of a quotient -/
def factor {α : Type _} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) :
  Quot r → Quot s :=
Quot.lift (Quot.mk s) (λ x y rxy => Quot.sound (h x y rxy))

theorem factor_mk_eq {α : Type _} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) :
  factor r s h ∘ Quot.mk _ = Quot.mk _ := rfl



/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def out {r : α → α → Prop} (q : Quot r) : α :=
Classical.choose (Quot.exists_rep q)


@[simp] theorem out_eq {r : α → α → Prop} (q : Quot r) : Quot.mk r q.out = q :=
Classical.choose_spec (Quot.exists_rep q)

end Quot