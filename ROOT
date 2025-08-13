chapter Binders

session Prelim in "thys/Prelim" = "HOL-Cardinals" +
  sessions
    "HOL-Library"
  theories [document = false]
    "HOL-Library.Old_Datatype"
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Countable"
    "HOL-Library.Infinite_Set"
    "HOL-Library.Countable_Set"
    "HOL-Library.Countable_Set_Type"
    "HOL-Library.Infinite_Typeclass"
  theories
    Prelim
    Card_Prelim

session Binders in "thys" = Prelim +
  directories
    "../Tools"
  theories
    MRBNF_Composition
    MRBNF_FP
    MRBNF_Recursor
    Swapping
    Support

session Operations in "operations" = Untyped_Lambda_Calculus +
  theories
    Binder_Inductive
    Least_Fixpoint
    Least_Fixpoint2
    Greatest_Fixpoint
    Recursor
    Corecursor
    Corecursor2
    VVSubst
    TVSubst
    Sugar
    BMV_Monad
    BMV_Fixpoint

session Tests in "tests" = Case_Studies +
  sessions
    System_Fsub
    Operations
  directories
    "fixtures"
  theories
    Regression_Tests
    Case_Study_Regression_Tests
    Fixpoint_Tests
    Binder_Datatype_Tests

session Case_Studies in "case_studies" = Binders +
  sessions
    "HOL-Library"
    "HOL-Computational_Algebra"
  theories [document = false]
    "HOL-Library.Stream"
    "HOL-Library.FSet"
    "HOL-Library.Multiset"
    "HOL-Computational_Algebra.Primes"
  theories
    FixedCountableVars
    FixedUncountableVars
    Swapping_vs_Permutation
    General_Customization
    Generic_Barendregt_Enhanced_Rule_Induction
    More_List
    More_Stream

session Untyped_Lambda_Calculus in "case_studies/Untyped_Lambda_Calculus" = Case_Studies +
  theories
    LC
    LC_Beta
    LC_Beta_depth
    LC_Head_Reduction
    LC_Parallel_Beta

session Infinitary_Lambda_Calculus in "case_studies/Infinitary_Lambda_Calculus" = Untyped_Lambda_Calculus +
  theories
    ILC
    ILC2
    ILC_Beta
    ILC_affine
    Embed_var_ivar
    Supervariables
    BSmall
    ILC_Renaming_Equivalence
    ILC_uniform
    ILC_Head_Reduction
    ILC_UBeta_depth
    ILC_relations_more
    Translation_LC_to_ILC
    ILC_good
    Super_Recursor
    Translation_ILC_to_LC
    Iso_LC_ILC

session Infinitary_FOL in "case_studies/Infinitary_FOL" = Case_Studies +
  theories
    InfFOL

session Process_Calculus in "case_studies/Pi_Calculus" = Case_Studies +
  theories
    Pi
	  Commitment
    Pi_Transition_Common
    Pi_Transition_Early
    Pi_Transition_Late
    Pi_cong

session System_Fsub in "case_studies/POPLmark" = Case_Studies +
  theories
    SystemFSub
    Labeled_FSet
    Pattern
    POPLmark_1B
    POPLmark_2B

session STLC in "case_studies/STLC" = Binders +
  theories
    STLC
