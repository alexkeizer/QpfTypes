import Qpf.Macro.Data.Replace
import Qpf.Macro.Data.View

open Lean Meta Elab.Command
open PrettyPrinter (delab)

namespace Data.Command
open Parser in
/--
  Count the number of arguments to a constructor
-/
partial def countConstructorArgs : Syntax → Nat
  | Syntax.node _ ``Term.arrow #[_, _, tail]  =>  1 + (countConstructorArgs tail)
  | _                                         => 0

open Elab
/--
  Add convenient constructor functions to the environment
-/
def mkConstructors (view : DataView) (shape : Name) : CommandElabM Unit := do
  for ctor in view.ctors do
    trace[QPF] "mkConstructors\n{ctor.declName} : {ctor.type?}"
    let n_args := (ctor.type?.map countConstructorArgs).getD 0

    let args := (← (List.range n_args).mapM
      fun _ => do pure <| mkIdent <|← Elab.Term.mkFreshBinderName).toArray

    let pointConstructor := mkIdent ((DataCommand.fixOrCofix view.command).getId ++ `mk)
    let shapeCtor := mkIdent <| Name.replacePrefix ctor.declName view.declName shape
    trace[QPF] "shapeCtor = {shapeCtor}"

    let body ← if n_args = 0 then
        `($pointConstructor $shapeCtor)
      else
        `(fun $args:ident* => $pointConstructor ($shapeCtor $args:ident*))

    let explicit ← view.getExplicitExpectedType
    let type : Term := TSyntax.mk <|
      (ctor.type?.map fun type =>
        Replace.replaceAllStx view.getExpectedType explicit type
      ).getD explicit
    let modifiers : Modifiers := {
      isNoncomputable := view.modifiers.isNoncomputable
      attrs := #[{
        name := `matchPattern
      }]
    }
    let declId := mkIdent <| ctor.declName.replacePrefix (←getCurrNamespace) .anonymous

    let cmd ← `(
      $(quote modifiers):declModifiers
      def $declId:ident : $type := $body:term
    )

    trace[QPF] "mkConstructor.cmd = {cmd}"
    elabCommand cmd
  return ()

end Data.Command
