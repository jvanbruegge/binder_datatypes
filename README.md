This is the artifact accompanying the paper:

Barendregt Convenes with Knaster and Tarski: 
Strong Rule Induction for Syntax with Bindings 

### How To Run?

The artifact contains the tool support for defining binding datatypes and proving strong rule
induction principles we developed in Isabelle/HOL as well as the case studies we report on in the
paper. It works with the latest released version Isabelle2024, which can be downloaded here:

[https://isabelle.in.tum.de/website-Isabelle2024/](https://isabelle.in.tum.de/website-Isabelle2024/)

After downloading Isabelle, a good starting point is to issue the following command

```
/<Isabelle/installation/path>/bin/isabelle jedit -d . -l Prelim thys/Untyped_Lambda_Calculus/LC_Beta
```

in the folder of the artifact. This will open Isabelle/jEdit and load our formalization of beta reduction for the untyped lambda calculus and the associated strong rule induction principle.

To let Isabelle check all relevant theories (from the command line, i.e., without running Isabelle/jEdit), one can use the command

```
/<Isabelle/installation/path>/bin/isabelle build -vD .
```

### Overview

We also provide generated HTML documents (folder html) that allow one to browse the formalization
without running Isabelle. The file html/index.html provides a good starting point. The
formalization is organized into the following "sessions":

session | description
------- | -----------
Isabelle_Prelim|administrative session bundling standard Isabelle libraries we use
Prelim|miscellaneous extensions to standard libraries, and bindings-specific infrastructure (e.g., countable and uncountable types we use for variables)
Binders|main metatheory including the formalization our Thms 10 (called strong_induct in the formalization) and 20 (BE_iinduct) in Generic_Barendregt_Enhanced_Rule_Induction (Sect 4, 7.3, 7.5 and App. F.2), the proof that our results generalize existing results from the literature in Urban_Berghofer_Norrish_Rule_Induction (App. B), and the binding-aware datatype automation in MRBNF_Composition and MRBNF_Recursor and the various ML files, App. F.1)
Operations|detailed proof examples for automation of the metatheory
Untyped_Lambda_Calculus|formalization of the untyped lambda calculus including beta reduction and parallel beta reduction (Sect 2)
Process_Calculus|formalization of the pi calculus transition relation and the  associated strong rule induction principle (Sect 7.1 and App. C.3)
System_Fsub|formalization of System F with subtyping, the associated strong rule induction principles, and the POPLmark challenge 1A, (Sect 7.2 and App. E)
Infinitary_Lambda_Calculus|formalization of Mazza's isomorphism between the untyped lambda calculus and the affine uniform infinitary lambda calculus in Iso_LC_ILC (Sect 7.4 and App. D)
Infinitary_FOL|formalization of the infinitary first-order logic deduction relation and the associated strong rule induction principle (Sect 8.1)

The session structure resembles the directory structure: theories from session <SESSION> are placed
in the directory src/thys/<SESSION>. Exceptions to this rule are the Isabelle_Prelim session which
merely bundles existing theories from Isabelle's standard library, and the Binders session whose
associated theories are placed directly in the directories src/thys and src/Tools (the latter
consists of the ML files implementing the support for datatypes with bindings).

