This is the artifact accompanying the paper:

Barendregt Convenes with Knaster and Tarski:
Strong Rule Induction for Syntax with Bindings

### How To Run?

The artifact contains the tool support for defining binding datatypes and proving strong rule
induction principles we developed in Isabelle/HOL as well as the case studies we report on in the
paper. It works with the latest released version Isabelle2024, which can be downloaded here:

[https://isabelle.in.tum.de/website-Isabelle2024/](https://isabelle.in.tum.de/website-Isabelle2024/)

After downloading Isabelle, a good starting point is to issue the following command while located in the base directory.

```
/<Isabelle/installation/path>/bin/isabelle jedit -d . -l Prelim thys/Untyped_Lambda_Calculus/LC_Beta.thy
```

in the folder of the artifact. This will open `Isabelle/jEdit` and load our formalization of beta reduction for the untyped lambda calculus and the associated strong rule induction principle. Using the `Isabelle/jEdit` menu, one can then browse through the subdirectories of `thys` and open any other theories; or one can start directly with another theory, for example:

```
/<Isabelle/installation/path>/bin/isabelle jedit -d . -l Prelim thys/Infinitary_Lambda_Calculus/Iso_LC_ILC.thy
```

(Again, when issuing the above, it is important to be located in the base directory, since the `ROOT` file is located there.)

To let Isabelle check all relevant theories (from the command line, i.e., without running Isabelle/jEdit), one can use the command

```
/<Isabelle/installation/path>/bin/isabelle build -vD .
```

We also provide generated HTML documents (folder html) that allow one to browse the formalization
without running Isabelle. The file html/index.html provides a good starting point. These were produced using the above command with `browser_info` option, i.e., running

```
/<Isabelle/installation/path>/bin/isabelle build -vD . -o browser_info
```

The resulting html files are placed in `~/.isabelle/Isabelle2024/browser_info`.

### Overview

The formalization is organized into the following sessions:

| session                    | description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| -------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Isabelle_Prelim            | Administrative session bundling the standard Isabelle libraries that we use.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| Prelim                     | Miscellaneous extensions to standard libraries, and bindings-specific infrastructure (e.g., countable and uncountable types we use for variables).                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| Binders                    | Main metatheory including the formalization our Thms 19, called strong_induct in the formalization, and 22 (called BE_iinduct in Generic_Strong_Rule_Induction.thy (Sect. 4, 7.3, 8.2, 8.4 and App. G.2), the proof that our results generalize the Urban/Berghofer/Norrish criterion in Urban_Berghofer_Norrish_Rule_Induction.thy (claimed in the paper and detailed in App. A), and the binding-aware datatype automation in MRBNF_Composition.thy and MRBNF_Recursor.thy and various ML files (App. G). Also contains the formalization of Counterexample 16 (Sect. 8.2) in No_Least_Support_Counterexample.thy. |
| Untyped_Lambda_Calculus    | Formalization of the untyped lambda calculus including beta reduction and parallel beta reduction (Sect. 2).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| Process_Calculus           | Formalization of the pi-calculus transition relation and the associated strong rule induction principle (Sect. 7.1 and App. D.3) -- covering both the early-instantiation and late-instantiation semantics, in theories Pi_Transition_Early.thy and Pi_Transition_Late.thy                                                                                                                                                                                                                                                                                                                                           |
| System_Fsub                | Formalization of System F with subtyping, the associated strong rule induction principles, and the POPLmark challenge 1A (Sect. 7.2 and App. F).                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| Infinitary_Lambda_Calculus | Formalization of Mazza's isomorphism between the untyped lambda calculus and the affine uniform infinitary lambda calculus (Sect 8.3 and App. E), with the end results stated in Iso_LC_ILC.thy.                                                                                                                                                                                                                                                                                                                                                                                                                     |
| Infinitary_FOL             | Formalization of the infinitary first-order logic deduction relation and the associated strong rule induction principle (Sect 8.1 and App. D.4).                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |

The session structure resembles the directory structure: theories from session <SESSION> are placed
in the directory src/thys/<SESSION>. Exceptions to this rule are the Isabelle_Prelim session which
merely bundles existing theories from Isabelle's standard library, and the Binders session whose
associated theories are placed directly in the directories src/thys and src/Tools (the latter
consists of the ML files implementing the support for datatypes with bindings).

### Notations

The formalization uses notations that are close to those from the paper, but makes some exceptions in order to observe the HOL conventions. Thus, in the formalization we prefer to have the main types that we use start with a lowercase. For example, in Isabelle we use `lterm` for tne type of of lambda-terms, which in the paper is denoted by `LTerm`; similarly, the formalization uses `proc` for the type of pi-calculus processes, which in the paper is denoted by `Proc`; etc.

Another specificity of the formalization is that the datatypes are defined to have more generic/polymorphic types than in the paper, after which they are instantiated to the exact types from the paper. Namely, instead of working with a fixed set of variables of suitable cardinality (which in the finitary case is just the cardinal of natural numbers aleph0), that set is kept as a parameter -- and in Isabelle, taking advantage of polymorphism, this is a type variable 'var of type class that specifies the cardinality constraint. (Our `binder_datatype` command automatically assigns 'var to have the suitable type class.) This allows more flexibility in case we want to nest the given datatype inside another datatype that perhaps requires larger collections of variables. But once the exact datatypes needed for a case study have been decided, one can instantiate 'var with a fixed type, var, of suitable cardinality. And this is what we do in all our example datatypes: First define the polymorphic version, then instantiate it to the monomorphic version (which matches the one described in the paper). We consistently use the suffix `P` for the polymorphic version. For example, we introduce `ltermP` as the type of lambda-terms polymorphic in the type of variables, then we take `lterm` to be the instance `var ltermP` for some fixed countable type of variables `var`. (The paper's implementation section 9 and the appendix implementation section G have some ad hoc choices of names, e.g., `type` versus `typ` and `term` versus `trm`, which we have decided to amend to the notation scheme explained above -- and will of course update the paper accordingly.)

Another place where the formalization uses different notations is that of pi-calculusm (Sect. 7.1). Namely we prefer ASCII notations with self-explanatory names, such as `Sum`, `Inp`, `Out` etc. The same is true for the dirrent versions of beta-reduction, where we use the notations `step`, `pstep` (for the parallel version) etc. instead of arrow notation. Finally, we sometimes introduce small variations to help parsing, e.g., double comma rather than comma for context-append in System F subtyping (Sect. 7.2).

### Formalization of the abstract results

As sketched in the fourth paragraph of Sect. 9 and the first paragraph of App. G.2, the general theorems have been formalized using Isabelle's locales, which are essentially persistent contexts that fix some type variables and term variables on them---and one can prove facts relative to these contexts. Locales corresponding to our three main theorems, Thm. 7, Thm. 19 and Thm. 22, are in the theory thys/Generic_Strong_Rule_Induction.thy.

The locale for Thm. 22 is called `IInduct`, and the Isabelle theorem corresponding to Thm. 22 is called `strong_iinduct`. It is built incrementally, from a previous `IInduct1` locale, which in turn extends a `CComponents` locale. The proof of the theorem follows the informal proof described in Sect. 4 (for Thm. 7), with the proof-mining and upgrades described in Sects. 7.3, 8.2 and 8.4 factored in. Overall, the cumulated assumptions of locale `IInduct` are those of Thm. 22, so these assumptions are of course no longer repeated when stating the theorem in the locale. But we can see the self-contained theorem with all assumptions if we type the following command outside the scope of the locale, which unfolds all the locale predicates:

```
print_statement IInduct.strong_iinduct[unfolded
      IInduct_def IInduct1_def CComponents_def
      IInduct_axioms_def IInduct1_axioms_def
      conj_imp_eq_imp_imp, rule_format]
```

(We have added this printing command, and the other two shown below, at the end of the theory thys/Generic_Strong_Rule_Induction.thy.)

The locale for Thm. 19 is called `Induct`. The fact that Thm. 19 is a particular case of (i.e., follows from)  Thm. 22 is captured by a sublocale relationship `sublocale Induct < IInduct`. Establishing this required us to prove that the assumptions of the `Induct` locale imply (the suitable instantiation of) those of the `IInduct` locale, and this allowed to us to make available in `Induct` (the same suitable instantiation of) the facts proved in `IInduct`. In short, we obtain Thm. 18 from Thm. 22 as a conseuqnece of this sublocale relationship; we named this theorem `strong_induct`. This theorem too can be contemplated outside of its locale:

```
print_statement Induct.strong_induct[unfolded
     Induct_def Induct1_def LSNominalSet_def
     Induct_axioms_def Induct1_axioms_def
     conj_imp_eq_imp_imp, rule_format]
```

Finally, the locale for Thm. 7 is called `Induct_nom`, and in turn is proved to be a sublocale of the `Induct` locale, reflecting the fact that Thm. 7 follows from Thm. 19.

```
Induct_nom.strong_induct_nom[unfolded
      Induct_nom_def Induct1_nom_def NominalSet_def
      Induct_nom_axioms_def Induct1_nom_axioms_def
      conj_imp_eq_imp_imp, rule_format]
```

The theory also contains less general versions of the first two of the above locales, where the Refreshability assumption is replaced by the stronger Freshness assumption (introduced in Def. 6). The names of these Freshness-based versions have suffix `_simple` at the end, and we establish sublocale relationships between these and the Refreshability-based ones, namely `sublocale IInduct_simple < IInduct` and `sublocale Induct_simple < Induct`.

### Formalization of the case studies

Most of our examples and case studies consist of three distinct types of theories:

(1) Those introducing the relevant binding-aware datatypes, usually via our `binder_datatype` command described in Sect. 9 and App. G.1. and proving and customizing basic properties about them (such as properties of substitution and swapping). In particular, we have:

- theory thys/Untyped_Lambda_Calculus/LC.thy dedicated to (the definition and customization of) the datatype of lambda-terms described in Sect. 2 and App. D.1;
- theory thys/Pi_Calculus/Pi.thy dedicated to the datatype of pi-calculus processes described in Sect. 7.1 and App. D.3;
- theory thys/POPLmark/SystemFSub_Types dedicated to the datatype of System-F-with-subtyping types described in Sect. 7.2;
- theory thys/Infinitary_FOL/InfFmla.thy dedicated to the datatype of infinitary FOL formulas described in Sect. 8.1 and App. D.4; here we work parametrically on two infinite regular cardinals `k1` and `k2`, which we axiomatize;
- theory thys/Infinitary_Lambda_Calculus/ILC.thy dedicated to the datatype of infinitary lambda-terms described in Sect. 8.3 and App. D.2.

An exception to the rule of using `binder_datatype` is the (non-recursive) datatype of commitments for the pi-calculus (described in Sect. 7.1), for which we use some Isabelle/ML tactics to the same effect in thys/Pi_Calculus/Commitments.thy (the reason being that our parser currently does not yet cover the degenerate case of non-recursive binders).

(2) Those introducing the relevant binding-aware inductive predicates, usually via our `binder_inductive` command described in Sect. 9 and App. G.2) -- the exceptions being the instances of the binder-explicit Thm. 22, where we instantiate the locale manually. In particular, we have:

* In thys/Untyped_Lambda_Calculus, the theories LC_Beta.thy and LC_Parallel_Beta.thy, containing the inductive definitions of lambda-calculus beta-reduction and parallel beta-reduction respectively, referred to in Sects. 2 and 5. In particular, Prop. 2 from the paper (in the enhanced version described in Remark 8) is generated and proved via the `binder_inductive` command from LC_Beta.thy; it is called `step.strong_induct`. The corresponding theorem for parallel-beta is called `pstep.strong_induct`, which is generated and proved from the `binder-inductive` command from LC_Parallel_Beta.thy. A variant of parallel-beta decorated with the counting of the number applicative redexes (which is needed in the Mazza case study) is also defined in LG_Beta-depth.thy (and its strong rule induction follows the same course).

* In thys/Pi_Calculus, the theories Pi_Transition_Early.thy and Pi_Transition_Late.thy use the `binder-inductive` command to define and endow with strong rule induction the late and early transition relations discussed in Sect. 7.1; and the theory Pi_cong.thy does the same for both the structural-congruence and the transition relations for the variant of pi-calculus discussed in App. B.

* In thys/POPLmark, the theory SystemFSub.thy is dedicated to defining (in addition to some auxiliary concepts such as well-formedness of contexts) the typing relation for System-F-with-subtyping discussed in Sect. 7.2. Here, because (as discussed in Sects. 7.2 and 7.3) we want to make use of an inductively proved lemma before we prove Refreshability (a prerequisite for enabling strong rule induction), we make use of a more flexible version of `binder_inductive`: namely we introduce the typing relation as a standard inductive definition (using Isabelle's `inductive` command), then prove the lemma that we need, and at the end we "make" this predicate into a binder-aware inductive predicate (via our command `make_binder_inductive`), generating the strong induction theorem, here named `ty.strong_induct` (since the typing predicate is called `ty`). Note that, in general, a `binder_inductive` command is equivalent to an `inductive` command followed immediately by a `make_binder_inductive` command. We have implemented this finer-granularity `make_binder_inductive` command after the submission, so it is not yet documented in the paper. (In the previous version of the supplementary material we had a different (less convenient) solution, which inlined everything that needed to be proved as goals produced by `binder_inductive`.)

* In thys/Infinitary_FOL, the theory InfFOL.thy introduces IFOL deduction again via `binder_inductive'.  

* In thys/Infinitary_Lambda_Calculus, we have several instantiations of the general strong induction theorem, Thm. 22. However, this is not done via the `binder_inductive` command, but by manually instantiating the locale coresponding to Thm. 22, namely `IInduct`. This is done for several inductive predicates needed by the Mazza case study: in ILC_Renaming_Equivalence.thy for the renaming equivalence relation from Sect. 8.3, in ILC_UBeta.thy for the uniform infinitary beta-reduction from App. E.3, and in ILC_good.thy for the `good` (auxiliary) predicate from App. E.6. By contrast, the `affine` predicate in from App. E.3, located in ILC_affine.thy, and the plain infinitary beta-reduction from App. E.1, located in ILC_Beta.thy, only require Thm. 19 so they are handled using `binder_inductive`.

(3) Proving facts specific to the case studies, namely:

- Theory thys/POPLmark/POPLmark_1A.thy proves the transitivity of the typing relation for System-F-with-subtyping.
- Theory thys/Infinitary_Lambda_Calculus/Iso_LC_ILC.thy contains the main theorems pertaining to Mazza's isomorphism, after the theories Translation_LC_to_ILC.thy and Translation_ILC_to_LC.thy establish the back and forth translation between the finitary and infinitary calculi (via suitable binding-aware recursors). This follows quite faithfully the development described in App. E.
- Theory thys/Urban_Berghofer_Norrish_Rule_Induction.thy again follows faithfully the development described in App. A.

### Tactics and automation using Isabelle/ML

As discussed in Sect. 9 and App. G, we have automated the production of binding-aware datatypes and inductive predicates (subject to strong rule induction) using Isabelle/ML, via the commands `binder_datatype`, `binder_inductive` (and its variant `make_binder_inductive`) and proof method `binder_induction`.

- The command `binder_datatype` is implemented in `Tools/parser.ML`. However most of the ML code in this directory is used to construct a binder datatype. It also reuses the normal datatype construction code from HOL.
- The command `binder_inductive` and `make_binder_inductive` are implemented in `Tools/binder_inductive.ML` and `Tools/binder_inductive_combined.ML`. The `binder_inductive` command just calls the normal Isabelle `inductive` command and immediately follows with a call to `make_binder_inductive`.
- The proof method `binder_induction` is implemented in `Tools/binder_induction.ML`. It is adapted from the normal Isabelle induction proof method. For the given `avoiding:` clause it infers the set of free variables and uses that to instantiate the parameter rho in the `strong_induct` theorems.
- The prototype implementation of the refreshability heuristic is defined inline in `thys/MRBNF_FP.thy`. Currently it requires all theorems to be passed manually, in a future version the required theorems will be inferred from the context.

### Mapping of the results from the paper to Isabelle theorem names


#### For the main paper 

##### Section 2

Prop 1 --> subsumed by Prop. 2 (also generated and proved automatically by the standard inductive definition)

Prop 2 --> theorem `step.strong_induct` (generated and proved by `binder_inductive`) from thys/Untyped_Lambda_Calculus

##### Sections 3 and 4

Thms 4 and 5 --> just recallections of the standard result (available in the Isabelle library)

Thm 7 (already the strengthened version discussed in Sect. 7.3) --> theorem `strong_induct_nom` (in locale `Induct_nom`) from thys/Generic_Strong_Rule_Induction.thy.

##### Section 7.1

Prop 12 --> theorems called `trans.strong_induct` (generated and proved by `binder_inductive`) from Pi_Transition_Early.thy and Pi_Transition_Late.thy. (As explained in the paper, Prop 12 actually shows a hybrid containing a selection of the more interesting rules for the two types of transitions.)

##### Section 7.2

Prop 13 --> theorem `ty.strong_induct` (generated and proved by `binder_inductive`) from thys/POPLmark/SystemFSub.thy

##### Section 8.1

Prop 15 --> theorem `deduct.strong_induct` (generated and proved by `binder_inductive`) from thys/Infinitary_FOL/InfFOL.thy

##### Section 8.2

Counterexample 16 --> theorem `counterexample` from No_Least_Support_Counterexample.thy

Thm 19 --> theorem `strong_induct` (in locale `Induct`) from thys/Generic_Strong_Rule_Induction.thy.

##### Section 8.3

Prop 20 --> theorem `affine.strong_induct` (generated and proved by `binder_inductive`) from thys/Infinary_Lambda_Calculus/ILC_affine.thy

Prop 21 --> theorem `strong_induct_reneqv` from ILC_Renaming_Equivalence.thy

##### Section 8.4

Thm 22 --> theorem `strong_iinduct` (in locale `IInduct`) from thys/Generic_Strong_Rule_Induction.thy.


#### For the appendix

##### Appendix A

The Urban-Berghofer-Norrish result described in App. A is formalized in an incremental sequence of locales that follows the same structere and naming as the locales for our main abstract results. `UBN` stands for the acronym of the author names.

Thm. 29 --> just a recallection of the standard rule induction of the predicate generated by the rules. In isabelle the predicate is called `II` and is located in thys/Urban_Berghofer_Norrish_Rule_Induction.thy, in the locale `UBN_Components`, so the Isabelle is called `II.induct`.

Thm. 33 --> this is infered from our Thm. 19 (theorem `strong_induct` in locale `Induct`) via a sublocale relationship: `UBN < UBN: Induct_simple` (the second `UBN` is just a label to avoid name clashes), which makes the theorem `strong_induct` available into the locale `UBN`


##### Appendix B

Prop 34 --> theorem `cong.strong_induct` (generated and proved by `binder_inductive`) from thys/Infinitary_FOL/Pi_cong.thy

Prop 35 --> theorem `trans.strong_induct` (generated and proved by `binder_inductive`) from thys/Infinitary_FOL/Pi_trans.thy


##### Appendix C

Lemma 36 --> the sublocale statement `sublocale NominalSet < LSNominalSet` from thys/Generic_Strong_Rule_Induction.thy

(We have not formalized Prop. 37; it is not used anywhere in the other results. Also, we have not formalized Prop 39, but have inlined its content whenever we needed it, e.g., when needed to take product or list extensions of LS-nominal sets.) 


##### Appendix D

All the facts shown here are generated automatically by our `binder_datatype` command. 


##### Appendix E 

We only indicate a selection only, namely the strong rule induction theorems and the main end results. 

Prop 71 --> theorem `istep.strong_induct` (generated and proved by `binder_inductive`) from thys/Infinitary_Lambda_Calculus/ILC_Beta.thy

Prop 83 --> theorem `strong_induct_ustepD` from thys/Infinitary_Lambda_Calculus/ILC_UBeta.thy

Thm 103 --> theorems `stepD_ustepD` and `ustepD_stepD` (and the variants `ustepD'_stepD` and `stepD_ustepD`, details provided as comments in the formalization) from thys/Infinitary_Lambda_Calculus/Iso_LC_ILC.thy

##### Appendix F

Thm 109 --> theorems `ty_transitivity` and `ty_narrowing` from thys/POPLmark/POPLmark_1A.thy 





 






