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

in the folder of the artifact. This will open `Isabelle/jEdit` and load our formalization of beta reduction for the untyped lambda calculus and the associated strong rule induction principle. Using the`Isabelle/jEdit` menu, one can then browse through the subdirectories of `thys` and open any other theories; or one can start directly with another theory, for example:

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


### Overview

The formalization is organized into the following sessions:

session | description
------- | -----------

Isabelle_Prelim | Administrative session bundling the standard Isabelle libraries that we use. 

Prelim | Miscellaneous extensions to standard libraries, and bindings-specific infrastructure (e.g., countable and uncountable types we use for variables). 

Binders | Main metatheory including the formalization our Thms 19, called strong_induct in the formalization, and 22 (called BE_iinduct in Generic_Strong_Rule_Induction.thy (Sect. 4, 7.3, 8.2, 8.4 and App. G.2), the proof that our results generalize the Urban/Berghofer/Norrish criterion in Urban_Berghofer_Norrish_Rule_Induction.thy (claimed in the paper and detailed in App. A), and the binding-aware datatype automation in MRBNF_Composition.thy and MRBNF_Recursor.thy and various ML files (App. G). Also contains the formalization of Counterexample 16 (Sect. 8.2) in No_Least_Support_Counterexample.thy. 

Untyped_Lambda_Calculus | Formalization of the untyped lambda calculus including beta reduction and parallel beta reduction (Sect. 2).

Process_Calculus | Formalization of the pi-calculus transition relation and the  associated strong rule induction principle (Sect. 7.1 and App. D.3) -- covering both the early-instantiation and late-instantiation semantics, in theories Pi_Transition_Early.thy and Pi_Transition_Late.thy

System_Fsub | Formalization of System F with subtyping, the associated strong rule induction principles, and the POPLmark challenge 1A (Sect. 7.2 and App. F).

Infinitary_Lambda_Calculus | Formalization of Mazza's isomorphism between the untyped lambda calculus and the affine uniform infinitary lambda calculus (Sect 8.3 and App. E), with the end results stated in Iso_LC_ILC.thy. 

Infinitary_FOL | Formalization of the infinitary first-order logic deduction relation and the associated strong rule induction principle (Sect 8.1 and App. D.4). 

The session structure resembles the directory structure: theories from session <SESSION> are placed
in the directory src/thys/<SESSION>. Exceptions to this rule are the Isabelle_Prelim session which
merely bundles existing theories from Isabelle's standard library, and the Binders session whose
associated theories are placed directly in the directories src/thys and src/Tools (the latter
consists of the ML files implementing the support for datatypes with bindings).


### Notations

The formalization uses notations that very close to those from the paper, but makes some exceptions in order to observe the HOL conventions. Thus, in the formalization we prefer to have the main types that we use start with a lowercase. For example, in Isabelle we use `lterm` for tne type of of lambda-terms, which in the paper is denoted by `LTerm`; similarly, the formalization uses `proc` for the type of pi-calculus processes, which in the paper is denoted by `Proc`; etc. 

Another specificity of the formalization is that the datatypes are defined at more generic/polymorphic types than in the paper, and later instantiated to the exact types from the paper. Namely, instead of working with a fixed set of variables of suitable cardinality (which in the finitary case is just aleph0), that set is kept as a parameter -- and in Isabelle, taking advantage of polymorphism, this is a type variable 'var of type class that specifies the cardinality constraint. (Our binder_datatype command automatically assigns 'var to have the suitable type class.) This allows more flexibility in case we want to nest the given datatype inside another datatype that perhaps requires larger collections of variables. But once the exact datatypes needed for a case study have been decided, one can instantiate 'var with a fixed type var of suitable cardinality. And this is what we do in all our example datatypes: First define the polymorphic version, then instantiate it to the monomorphic version (which matches that used in the paper). We consistently use the suffix `P` for the polymorphic version. For example, we introduce `ltermP` as the type of lambda-terms polymorphic in the type of variables, then we take `lterm` to be the instance `var ltermP` for some fixed countable type of variables `var`. (The paper's implementation section 9 and the appendix implementation section G contain some more ad hoc choices of names, e.g., `type` versus `typ` and `term` versus `trm`, which we have decided to amend to the notation scheme explained above -- and will of course update the paper accordingly.) 

Another place where the formalization uses different notations is that of pi-calculusm (Sect. 7.1). Namely we prefer ASCII notations with self-explanatory names, such as `Sum`, `Inp`, `Out` etc. The same is true for the dirrent versions of beta-reduction, where we use the notations `step`, `stepP` (for the parallel version) etc. instead of arrow notation. Finally, we inrtoduce small variations to help parsing, e.g., double comma rather than comma for context append in System F subtyping (Sect. 7.2). 


### Formalization of the abstract results

As sketched in the fourth paragraph of Sect. 9 and the first paragraph of App. G.2, the general theorems have been formalized using Isabelle's locales, which are essentially persistent contexts that fix some type variables and term variables on them---allowing one to prove facts relative to these contexts. Locales corresponding to our three main theorems, Thm. 7, Thm. 19 and Thm. 22, are in theory thys/Generic_Strong_Rule_Induction.thy. 

    The locale for Thm. 22 is called `IInduct`, and the Isabelle theorem corresponding to Thm. 22 is called `strong_iinduct`. It is built incrementally, a previous `IInduct1` locale, which in turn extends a `CComponents` locale. The proof of the theorem follows the informal proof descrbed in Sect. 4 (for Thm. 7), with the proof-mining and upgrades described in Sects. 7.3, 8.2 and 8.4 factored in. Overall, the cumulated assumptions of locale `IInduct` are those of Thm. 22, so these assumptions are of course no longer repeated when stating the theorem in the locale. But we can see the full theorem with all assumptions if we type the following command outside the scope of the locale, which unfolds all the locale predicates:  
    
    ```
    print_statement Induct.strong_induct[unfolded
         Induct_def Induct1_def LSNominalSet_def
         Induct_axioms_def Induct1_axioms_def
         conj_imp_eq_imp_imp, rule_format]
    ```
    
    The locale for Thm. 19 is called `Induct`. Since Thm. 19 follows from Thm. 22, we establish a sublocale relationship, between the two, `sublocale Induct < IInduct`. This required us to prove that the assumptions of the `Induct` locale imply (a suitable instantiation of) those of the `IInduct` locale, and this allowed to us to make available in `Induct` (the same suitable instantiation of) the facts proved in `IInduct`. In short, we obtain Thm. 22 as a conseuqnece of this sublocale relationship; we named this theorem `strong_induct`. This theorem too can be contemplated outside of its locale: 
    
        ```
    print_statement IInduct.strong_iinduct[unfolded
          IInduct_def IInduct1_def CComponents_def
          IInduct_axioms_def IInduct1_axioms_def
          conj_imp_eq_imp_imp, rule_format]
       ```
       
    Finally, the locale for Thm. 7 is called `Induct_nom`, and is proved to be a sublocale of the `Induct` locale, reflecting the fact that Thm. 7 follows from Thm. 19. 
    
        ```
    Induct_nom.strong_induct_nom[unfolded
          Induct_nom_def Induct1_nom_def NominalSet_def
          Induct_nom_axioms_def Induct1_nom_axioms_def
          conj_imp_eq_imp_imp, rule_format]
       ```
    

### Formalization of the case studies 

Most of our examples and case studies consist of three distinct types of theories:

(1) Those introducing the relevant binding-aware datatypes, usually via our `binding_datatype` command described in Sect. 9 and App. G.1. and proving basic properties about them. In particular, we have:
   * theory thys/Untyped_Lambda_Calculus/LC.thy dedicated to (the definition and customization of)  the datatype of lambda-terms described in Sect. 2 and App. D.1; 
   * theory thys/Pi_Calculus/Pi.thy dedicated to the datatype of Pi-calculus processes described in Sect. 7.1 and App. D.3; 
   * theory thys/POPLmark/SystemFSub_Types dedicated to the datatype of System-F-with-subtyping types described in Sect. 7.2; 
   * theory thys/Infinitary_FOL/InfFmla.thy dedicated to the datatype of infinitary FOL formulas described in Sect. 8.1 and App. D.4; 
   * theory thys/Infinitary_Lambda_Calculus/ILC.thy dedicated to the datatype of infinitary lambda-terms described in Sect. 8.3 and App. D.2. 
   
   An exception to the rule of using `binding_datatype` is the (non-recursive) datatype of commitments for the pi-calculus (described in Sect. 7.1), for which we use some Isabelle/ML tactics to the same effect in thys/Pi_Calculus/Commitments.thy (the reason being that we don't yet have a parser for the degenerate case of non-recursive binders). 
   
(2) Those introducing the relevant binding-aware inductive predicates, usually via our `binder_inductive` command decsribed in Sect. 9 and App. G.2) -- the exception being the instances of the binder-explicit Thm. 22, where we instantiate the locale manually. In particular, we have:

    * In thys/Untyped_Lambda_Calculus, the theories LC_Beta.thy and LC_Parallel_Beta.thy, containing the inductive definition of lambda-calculus beta-reduction and parallel beta-reduction respectively, refered to in Sects. 2 and 5. In particular, Prop. 2 from the paper (in the enhanced version described in Remark 8) is generated and proved via the `binder_inductive` command from LC_Beta.thy; it is called `step.strong_induct`. The corresponding theorem for parallel-beta is called `pstep.strong_induct`, which is generated and proved from the `binder-inductive` command from LC_Parallel_Beta.thy. A variant of parallel-beta decorated with the counting of the number applicative redexes (which is needed in the Mazza case study) is also defined in LG_Beta-depth.thy (and its strong rule induction follows the same course).
    * In thys/Pi_Calculus, the theories Pi_Transition_Early.thy and Pi_Transition_Late.thy use the `binder-inductive` command to define and endow with strong rule induction the late and early transition relations discussed in Sect. 7.1; and the theory Pi_cong.thy does the same for both the structural-congruence and the transition relations for the variant of pi-calculus discussed in App. B. 
    * In thys/POPLmark/, the theory SystemFSub is dedicated to defining (in addition to some auxiliary concepts such as well-formedness of contexts) the typing relation for System F discussed in Sect. 7.2. Here, because (as discussed in Sects. 7.2 and 7.3) we want to make use of an inductively proved lemma before we prove refreshability (a prerequisite for our rule induction), we make use of a more flexible version of `binding_inductive`: namely we introduce the subtyping relation as a standard inductive definition (using Isabelle's standard `inductive` command), then prove what we need, and at the end we "make" this into a binder-aware inductive predicate (via command `make_binder_inductive`), generating the strong induction theorem, here named `ty.strong_induct`. (Note that, in general, a `binder_inductive` command is equivalent to an `inductive` command followed by a `make_binder_inductive` command. We have implemented these finer-granularity `make_binder_inductive` command after the submission, so it is not yet documented in the paper; in the previous version of the supplementary material we had a different (less convenient) solution, which inlined everything that needed to be proved as goals produced by `binder_inductive`.)
    * In thys/Infinitary_FOL, the theory InfFOLintroduced IFOL deduction again via `binder_inductive'. 
    * In thys/Infinitary_Lambda_Calculus, we have several instantiations of the general strong induction theorem, Thm. 22. However, this is not done via the `binder_inductive` command, but by manually instantiating the locale coresponding to Thm. 22, namely `IInduct'. This is done for several inductive predicates needed by the Mazza case study: in  ILC_affine.thy and ILC_Renaming_Equivalence.thy for the `affine` predicate renaming equivalence relation from Sect. 8.3, in ILC_UBeta.thy for the uniform infinitary beta-reduction from App. E.3, and ILC_good.thy for the `good` (auxiliary) predicate from App. E.6. (By contrast, the plain infinitary beta-reduction from App. E.1, localed in pain in ILC_Beta.thy and included just for illustration not for the case study, only requires Thm. 19 so it is servived using`binder_inductive`.)
  
(3) Proving facts specific to the case studies, namely: 
   * Theory thys/POPLmark/POPLmark_1A proves the transitivity of the typing relation for System-F-with-subtyping 
   * Theory thys/Infinitary_Lambda_Calculus/Iso_LC_ILC.thy contains the main theorems pertaining to Mazza's isomorphism, after the theories Translation_LC_to_ILC.thy and Translation_ILC_to_LC.thy establish the back and forth translation between the finitary and infinitary calculi (via suitable binding-aware recursors). This follows quite faithfully the development described in App. E. 
   * Theory thys/Urban_Berghofer_Norrish_Rule_Induction.thy, again following faithfully the development described in App. 9. 
   
   
### Tactics and automation using Isabelle/ML

As discussed in Sect. 9 and App. G, we have automated the production of binding-aware datatypes and inductive predicates (subject to strong rule induction) using Isabelle/ML, via the commands `binding_datatype`, `binder_inductive` (and its variant `make_binder_inductive`) and tactic `binder_induction`. 
   * The command `binding_datatype` is implemented in XXX. TODO: One or two sentences.  
   * The command `binder_inductive` and `make_binder_inductive` are  implemented in XXX. TODO: One or two sentences. 
   * The tactic `binder_induction` is implemented in XXX. TODO: One or two sentences. Point out the theorems where it is used. 

