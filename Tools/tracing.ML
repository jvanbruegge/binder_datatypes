(* Tactic tracing combinator.

     - before: log the label, goal index, and subgoal term
     - after:  log how many subgoals remain on the first result state
     - fail:   log that the tactic produced an empty sequence

   Usage:

     val step = Tactic_Trace.wrap ctxt {
       indent = "  ", tag = "[MyTac]"
     } "label" tac
     (* then use `step i st` wherever you would use `tac i st` *)

   The tactic is called as an int -> tactic (operates on subgoal i),
   matching the shape used by THEN', THEN_ALL_NEW, etc. *)

signature TACTIC_TRACE =
sig
  type config = { indent : string, tag : string }
  val wrap : Proof.context -> config -> string -> (int -> tactic) -> int -> tactic
  val wrap0 : Proof.context -> config -> string -> tactic -> tactic
end;

structure Tactic_Trace : TACTIC_TRACE =
struct

type config = { indent : string, tag : string }

fun pretty_subgoal ctxt i st =
  Pretty.string_of (Pretty.quote (
    Syntax.pretty_term ctxt (Thm.term_of (Thm.cprem_of st i))
    handle THM _ => Pretty.str "<no such subgoal>"))

fun wrap ctxt ({indent, tag} : config) label t i st =
  let
    val _ = tracing (indent ^ tag ^ " " ^ label ^ " on goal "
                     ^ string_of_int i ^ ": " ^ pretty_subgoal ctxt i st)
  in
    (t i st) |> (fn s => case Seq.pull s of
        SOME (a, r) =>
          (tracing (indent ^ tag ^ " " ^ label ^ " -> "
                    ^ string_of_int (Thm.nprems_of a) ^ " subgoals");
           Seq.cons a r)
      | NONE =>
          (tracing (indent ^ tag ^ " FAILED at " ^ label); Seq.empty))
  end

fun wrap0 ctxt cfg label t = wrap ctxt cfg label (fn _ => t) 1

end;


(* Tactic timing combinator.

   Usage:

     val step = Tactic_Time.wrap {
       indent = "  ", tag = "[Timing]"
     } "UFVars_Uctors" tac
     (* then use `step i st` wherever you would use `tac i st` *)

*)

signature TACTIC_TIME =
sig
  type config = { indent : string, tag : string }
  val wrap : config -> string -> (int -> tactic) -> int -> tactic
  val wrap0 : config -> string -> tactic -> tactic
end;

structure Tactic_Time : TACTIC_TIME =
struct

type config = { indent : string, tag : string }

fun wrap ({indent, tag} : config) label t i st =
  let
    val start = Time.now ()
    fun elapsed () =
      Time.toString (Time.- (Time.now (), start))
  in
    (t i st) |> (fn s => case Seq.pull s of
        SOME (a, r) =>
          (tracing (indent ^ tag ^ " " ^ label ^ " " ^ elapsed () ^ "s -> "
                    ^ string_of_int (Thm.nprems_of a) ^ " subgoals");
           Seq.cons a r)
      | NONE =>
          (tracing (indent ^ tag ^ " FAILED at " ^ label
                    ^ " after " ^ elapsed () ^ "s");
           Seq.empty))
  end

fun wrap0 cfg label t = wrap cfg label (fn _ => t) 1

end;
