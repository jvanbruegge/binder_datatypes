theory POPLmark_2B
imports POPLmark_1B
begin

binder_datatype (FTVars: 'tv, FVars: 'v) trm = Var 'v
  | Abs x::'v "'tv typ" t::"('tv, 'v) trm" binds x in t
  | App "('tv, 'v) trm" "('tv, 'v) trm"
  | TAbs X::'tv "'tv typ" t::"('tv, 'v) trm" binds X in t
  | TApp "('tv, 'v) trm" "'tv typ"

print_theorems

term Var

end