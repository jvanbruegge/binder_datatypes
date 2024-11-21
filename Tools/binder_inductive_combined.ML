structure Binder_Inductive_Combined =
struct

fun ind_decl co args =
  let
    val (options, rest) = Binder_Inductive.config_parser args;
    val names = map (fn (x, _, _) => x) (fst (Parse.vars rest));
    val (inductive, rest) = Inductive.gen_ind_decl Inductive.add_ind_def co rest;
  in (fn lthy =>
    let
      val lthy = snd (Local_Theory.begin_nested lthy);
      val lthy = inductive lthy;
      val (lthy, old_lthy) = `Local_Theory.end_nested lthy;
      val state = Binder_Inductive.binder_inductive_cmd (((options, Binding.name_of (hd names)), NONE), (NONE, NONE)) lthy
    in state end, rest) end;

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>binder_inductive\<close> "derive strengthened induction theorems for inductive predicates"
    (ind_decl false);

end
