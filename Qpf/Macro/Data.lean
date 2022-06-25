
import Qpf.Macro.Data.Internals
import Qpf.Macro.Common


syntax qpfCtor := "| " ident (" : " term)?

syntax qpfType := ("data " <|> "codata ") declId