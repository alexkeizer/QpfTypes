
-- import Qpf.Macro.Data.ElabData


syntax qpfCtor := "| " ident (" : " term)?

syntax qpfType := ("data " <|> "codata ") declId