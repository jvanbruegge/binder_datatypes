theory Linearize_rail
  imports "Binders.MRBNF_Composition" "Binders.MRBNF_Recursor"
  keywords "linearize_mrbnf" :: thy_goal
begin

ML_file "../Tools/mrbnf_linearize_tactics.ML"
ML_file "../Tools/mrbnf_linearize.ML"
(* this is just to build the rail diagram for linearize_mrbnf*)

ML_file \<open>~~/src/Doc/antiquote_setup.ML\<close>
text  \<open>
\<^rail>\<open>
  @@{command linearize_mrbnf} @{syntax spec} name '=' term @{syntax wits}? \<newline>
    @'on' @{syntax on_vars} @{syntax bindings}? @{syntax "morphisms"}?
  ;
  @{syntax_def spec}: @{syntax tfree} | '(' (((name ':')? @{syntax tfree}) + ',') ')'
  ;
  @{syntax_def tfree}: typefree ('::' sort)
  ;
  @{syntax_def wits}: '[' 'wits' ':' (term + ',') ']'
  ;
  @{syntax_def on_vars}: (typefree + @'and')
  ;
  @{syntax_def bindings}: @'for' ((('map' | 'rel' | 'pred' | 'nonrep' | 'sameShape') ':' name) +)
  ;
  @{syntax_def "morphisms"}: @'morphisms' name name
\<close>
\<close>
end