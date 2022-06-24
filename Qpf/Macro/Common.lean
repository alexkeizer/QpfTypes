import Qpf.Qpf

namespace Macro
  open Lean Meta

  def withLiveBinders [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n]
                  [Inhabited α]
                  (binders : Array Syntax) 
                  (f : Array Expr → n α) : n α
  := do
    let u := mkLevelSucc <|← mkFreshLevelMVar;
    let decls := binders.map fun α => (
        α[0].getId, 
        fun _ => pure (mkSort u)
      )

    withLocalDeclsD decls f
end Macro
