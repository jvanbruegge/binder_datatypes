signature MRSBNF_COMP = sig

  val id_mrsbnf: MRSBNF_Def.mrsbnf
end

structure MRSBNF_Comp : MRSBNF_COMP = struct

val id_mrsbnf = the (MRSBNF_Def.mrsbnf_of @{context} "BMV_Monad.ID");

end