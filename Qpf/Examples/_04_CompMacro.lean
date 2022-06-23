import Qpf
import Qpf.Examples._01_List
      
-- Projections

-- every qpf whose target is just a variable, gets compiled to a projection
#qpf F₁ α β γ := γ

-- The supplied name is bound to the curried function
#print F₁
-- while the internal, uncurried, function is exposed as `.typefun`
#print F₁.typefun

-- We can confirm the expected results with reduce
#reduce F₁.typefun ![Nat, Int, (List Nat)]
#reduce F₁ Nat Int (List Nat)


-- Note that we can use `_` holes for unused variables
#qpf F₂ α _ _ := α

#print F₂.typefun

#reduce F₂ Nat Int (List Nat)



-- Constants
#qpf F_int α β := Int

#print F_int
#print F_int.typefun

#reduce F_int Nat Nat

#qpf F_list α β := QpfList Nat

#print F_list
#print F_list.typefun

#reduce F_list Nat Nat


-- Composition
example : MvQpf F₁.typefun := inferInstance
example : MvQpf (TypeFun.ofCurried F₁) := inferInstance

#qpf F₃ α β := F₁ α β α

#print F₃.typefun
#reduce F₃ Nat Int


