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

Process_Calculus | Formalization of the pi-calculus transition relation and the  associated strong rule induction principle (Sect. 7.1 and App. D.3).

System_Fsub | Formalization of System F with subtyping, the associated strong rule induction principles, and the POPLmark challenge 1A (Sect. 7.2 and App. F).

Infinitary_Lambda_Calculus | Formalization of Mazza's isomorphism between the untyped lambda calculus and the affine uniform infinitary lambda calculus in Iso_LC_ILC (Sect 8.3 and App. E).

Infinitary_FOL | Formalization of the infinitary first-order logic deduction relation and the associated strong rule induction principle (Sect 8.1 and App. D.4). 

The session structure resembles the directory structure: theories from session <SESSION> are placed
in the directory src/thys/<SESSION>. Exceptions to this rule are the Isabelle_Prelim session which
merely bundles existing theories from Isabelle's standard library, and the Binders session whose
associated theories are placed directly in the directories src/thys and src/Tools (the latter
consists of the ML files implementing the support for datatypes with bindings).


### Mapping to the concepts and results claimed in the paper






### Notations

The formalization uses notations that very close to those from the paper, but makes some exceptions in order to observe the HOL conventions. Thus, in the formalization we prefer to have the main types that we use start with a lowercase. For example, in Isabelle we use `lterm` for tne type of of lambda-terms, which in the paper is denoted by `LTerm`; similarly, the formalization uses `proc` for the type of pi-calculus processes, which in the paper is denoted by `Proc`; etc. 

Another specificity of the formalization is that the datatypes are defined at more generic/polymorphic types than defined in the paper, and later instantiated to the exact types from the paper.  Namely, instead of working with a fixed set of variables of suitable cardinality (which in the finitary case is just Aleph0), that set is kept as a parameter -- and in Isabelle, taking advantage of polymorphism, this is a type variable 'var of type class that specifies the cardinality constraint. (Our binder_datatype command automatically assigns 'var to have the suitable type class.) This allows more flexibility in case we want to nest the given datatype inside another datatype that perhaps requires larger sets of variables. But once the exact datatypes needed for a case study have been decided, one can instantiate 'var with a fixed type var of suitable cardinality. And this is what we do in all our example datatypes: first define the polymorphic version, then instantiate it to the monomorphic version (which matches exactly that used in the paper). We consistently use the suffix `P` for the polymorphic version. For example, we introduce `ltermP` as the type of lambda-terms polymorphic in the type of variables, then we take `lterm` to be the instance `var ltermP` for some fixed countable type of variabler `var`. (The paper's implementation section 9 and the appendix implementation section G contain some more ad hoc choices of names, e.g., `type` versus `typ`, which we have decided to amend as explained above -- and will of course update the paper accordingly.) 





TODO:
-- var for the type of variables (usually we use the notations from the paper, but lowercase following the convention in HOL)
-- conventions: eg. Lterm the polymorphic type, lterm its monomorphic versions 
(the paper uses Lterm); ILterm vs. ilterm etc. 
-- mention the NoLeastSupportCounterexample theory. 
-- check in the browsable html files too
-- say we always have theories dedicated to the specific datatypes
--- say for the infinitary case automation is less well-developed
-- For the support of a function, in the formalization we use the more customary notation "supp" (read "support") for what in the paper we call "core" (at the beginning of section 3). 

