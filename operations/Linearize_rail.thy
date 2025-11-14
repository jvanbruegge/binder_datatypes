theory Linearize_rail
  imports "Binders.MRBNF_Composition"
begin
(* this is just to build the rail diagram for linearize_mrbnf*)

ML_file \<open>~~/src/Doc/antiquote_setup.ML\<close>
text  \<open>
\<^rail>\<open>
  @@{command linearize_mrbnf} @{syntax spec} name '=' typ @{syntax wits}? \<newline>
    @'on' (typefree + @'and') @{syntax bindings}? @{syntax 'morphisms'}?
  ;
  @{syntax_def spec}: @{syntax tfree} | '(' (((name ':')? @{syntax tfree}) + ',') ')'
  ;
  @{syntax_def tfree}: typefree ('::' sort)
  ;
  @{syntax_def wits}: '[' 'wits' ':' (term + ',') ']'
  ;
  @{syntax_def bindings}: @'for' ((('map' | 'rel' | 'pred' | 'nonrep' | 'sameShape') ':' name) +)
  ;
  @{syntax_def 'morphisms'}: @'morphisms' name name
\<close>
\<close>
end