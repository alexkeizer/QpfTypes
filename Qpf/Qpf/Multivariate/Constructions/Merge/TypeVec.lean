import Qpf.Util.TypeVec


namespace TypeVec
/-- 
  Extend a `TypeVec` by duplicating an earlier element 
-/
@[reducible]
abbrev duplicate {n : Nat} (i : Fin2 n) (α : TypeVec n) : TypeVec (Nat.succ n)
  := α ::: (α i)

@[simp]
theorem duplicate_drop_id {n : Nat} (i : Fin2 n) (α : TypeVec n) :
  (α.duplicate i).drop = α :=
by
  simp [duplicate]

theorem duplicate_j_weaken_eq_α_j {n : Nat} (i j : Fin2 n) (α : TypeVec n)  :
  (α.duplicate i) (j.add 1) = α j :=
by
  simp [duplicate, Fin2.weaken, append1, Fin2.add]


namespace Arrow
  def duplicate (i : Fin2 n) (f : α ⟹ β) : (α.duplicate i) ⟹ (β.duplicate i) 
    | Fin2.fz   => f i
    | Fin2.fs j => f j

  @[simp]
  theorem duplicate_drop_id (i : Fin2 n) (f : α ⟹ β) :
    dropFun (f.duplicate i) = f :=
  by
    simp [duplicate]
    
end Arrow



def merge {n : Nat} (i : Fin2 n) (α : TypeVec (Nat.succ n)) : TypeVec n
  := fun j => if j = i  then α (i.fs) ⊕ α Fin2.fz
                        else α (j.fs)

-- def unmerge {n : Nat} (i : Fin2 n) (α : TypeVec n) : TypeVec (Nat.succ n)
--   | Fin2.fz   => match α i with
--                   | β₁ ⊕ β₂ => β₂
--                   | _       => Unit
--   | Fin2.fs j => _


end TypeVec