import Lean

open Lean Parser.Term
open Parser (Parser)

-- TODO: Figure out if there is a better solution to this
/-- Both `bracketedBinder` and `matchAlts` have optional arguments,
which cause them to not by recognized as parsers in quotation syntax
(that is, ``` `(bracketedBinder| ...) ``` does not work).
To work around this, we define aliases that force the optional argument to it's default value, 
so that we can write ``` `(bb| ...) ```instead. -/
abbrev bb            : Parser := bracketedBinder
abbrev matchAltExprs : Parser := matchAlts

/- Since `bb` and `matchAltExprs` are aliases for `bracketedBinder`, resp. `matchAlts`,
we can safely coerce syntax of these categories  -/
instance : Coe (TSyntax ``bb) (TSyntax ``bracketedBinder)      where coe x := ⟨x.raw⟩
instance : Coe (TSyntax ``matchAltExprs) (TSyntax ``matchAlts) where coe x := ⟨x.raw⟩
