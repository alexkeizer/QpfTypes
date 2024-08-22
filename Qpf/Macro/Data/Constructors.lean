import Qpf.Macro.Data.Replace
import Qpf.Macro.Data.RecForm
import Qpf.Macro.Data.View

open Lean Meta Elab Elab.Command
open PrettyPrinter (delab)

namespace Data.Command
open Parser in
/--
  Count the number of arguments to a constructor
-/
partial def countConstructorArgs : Syntax → Nat
  | Syntax.node _ ``Term.arrow #[_, _, tail]  => 1 + (countConstructorArgs tail)
  | _                                         => 0

/--
  Add definitions for constructors
  that are generic across two input types shape and name.
  Additionally we allow the user to control how names are generated.
  Any binders passed in `binders` are added as parameters to the generated constructor 
-/
def mkConstructorsWithNameAndType
    (view : DataView) (shape : Name)
    (nameGen : CtorView → Name) (argTy retTy : Term)
    (binders : TSyntaxArray ``Parser.Term.bracketedBinder := #[])
    : CommandElabM Unit := do
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

    let type ← RecursionForm.extract ctor view.getExpectedType
      |>.map (RecursionForm.replaceRec view.getExpectedType argTy)
      |> RecursionForm.toType retTy

    let modifiers : Modifiers := {
      isNoncomputable := view.modifiers.isNoncomputable
      attrs := #[{
        name := `matchPattern
      }]
    }
    let declId := mkIdent $ nameGen ctor

    let cmd ← `(
      $(quote modifiers):declModifiers
      def $declId:ident $binders*: $type := $body:term
    )

    trace[QPF] "mkConstructor.cmd = {cmd}"
    elabCommand cmd

  return

/--
  Add convenient constructor functions to the environment
-/
def mkConstructors (view : DataView) (shape : Name) : CommandElabM Unit := do
  let explicit ← view.getExplicitExpectedType
  let nameGen := (·.declName.replacePrefix (←getCurrNamespace) .anonymous)

  mkConstructorsWithNameAndType view shape nameGen explicit explicit

end Data.Command
