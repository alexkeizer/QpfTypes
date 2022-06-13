import Qpf.MathlibPort.Fin2
import Qpf.Util.Vec


import Lean
open Lean

structure QpfApp (n : Nat) where
  (qpf: Syntax)
  (args : List (Fin2 n))

structure DataTypeCtor (n : Nat) where
  (name : Name)
  (args : List $ Fin2 $ n)


structure DataType where
  -- `fvars` are free variables, i.e., the parameters of the datatype declaration, 
  -- `mvars` are variables introduced to represent some composite expression
  (fvars mvars: Nat)
  -- The expressions that define each `mvar`
  (exprs: Vec (QpfApp (fvars + mvars)) mvars)
  (name : Name)
  (type : Expr)
  (ctors : List (DataTypeCtor $ fvars+mvars))

#check StateM DataType
#check Constructor

namespace DataType 
  def typeToVar (type : Expr) : StateM DataType Nat :=
    pure 0

  def parseCtor (ctor : Constructor) : StateM DataType Unit := do
    

  def ofInductive' : List Constructor → StateM DataType Unit
    | ctor :: ctors =>  do
                          parseCtor ctor
                          ofInductive' ctors
    | []            =>  pure ()
    


  def ofInductive : InductiveType → DataType
    | ⟨name, type, ind_ctors⟩ => 
      let base : DataType := {
        fvars := 0
        mvars := 0
        exprs := Vec.nil
        ctors := List.nil
        name
        type
      }

      (ofInductive' ind_ctors base).snd

end DataType