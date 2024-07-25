import Qpf.Macro.Data.Replace
import Qpf.Macro.Data.View
import Qpf.Macro.NameUtils

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

    let args ← (List.range n_args).mapM fun _ =>
      do pure <| mkIdent <|← Elab.Term.mkFreshBinderName
    let args := args.toArray

    let mk := mkIdent ((DataCommand.fixOrCofix view.command).getId ++ `mk)
    let shapeCtor := mkIdent <| Name.replacePrefix2 view.declName shape ctor.declName
    trace[QPF] "shapeCtor = {shapeCtor}"



    let body := if n_args = 0 then
        `($mk $shapeCtor)
      else
        `(fun $args:ident* => $mk ($shapeCtor $args:ident*))
    let body ← body

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
    let declId := mkIdent <| Name.stripPrefix2 (←getCurrNamespace) ctor.declName

    let cmd ← `(
      $(quote modifiers):declModifiers
      def $declId:ident : $type := $body:term
    )

    trace[QPF] "mkConstructor.cmd = {cmd}"
    elabCommand cmd
  return ()

end Data.Command
