chapter Binders

session Isabelle_Prelim = "HOL-Cardinals" +
  sessions
    "HOL-Library"
    "HOL-Computational_Algebra"
  theories [document = false]
    "HOL-Library.Old_Datatype"
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Countable"
    "HOL-Library.Infinite_Set"
    "HOL-Library.Countable_Set"
    "HOL-Library.Countable_Set_Type"
    "HOL-Library.Stream"
    "HOL-Library.FSet"
    "HOL-Library.Multiset"
    "HOL-Computational_Algebra.Primes"

session Prelim in "thys/Prelim" = Isabelle_Prelim +
  theories
    Prelim
    Card_Prelim
    More_List
    More_Stream
    Curry_LFP
    FixedCountableVars
    FixedUncountableVars
    Swapping_vs_Permutation

session Binders in "thys" = Prelim +
  directories
    "../Tools"
  theories
    MRBNF_Composition
    MRBNF_FP
    MRBNF_Recursor
    Generic_Barendregt_Enhanced_Rule_Induction
    General_Customization
    Urban_Berghofer_Norrish_Rule_Induction

session Operations in "operations" = Untyped_Lambda_Calculus +
  theories
    Binder_Inductive
    Least_Fixpoint
    Least_Fixpoint2
    Greatest_Fixpoint
    Recursor
    Corecursor
    VVSubst
    TVSubst
    Sugar

session Tests in "tests" = Binders +
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

session Untyped_Lambda_Calculus in "thys/Untyped_Lambda_Calculus" = Binders +
  theories
    LC
    LC_Beta
    LC_Beta_depth
    LC_Head_Reduction
    LC_Parallel_Beta
    LC_Primal

session Infinitary_Lambda_Calculus in "thys/Infinitary_Lambda_Calculus" = Untyped_Lambda_Calculus +
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

session Infinitary_FOL in "thys/Infinitary_FOL" = Binders +
  theories
    InfFOL

session Process_Calculus in "thys/Pi_Calculus" = Binders +
  theories
    Pi
	  Commitment
    Pi_Transition_Common
    Pi_Transition_Early
    Pi_Transition_Late
    Pi_cong

session System_Fsub in "thys/POPLmark" = Binders +
  theories
    SystemFSub
    Labeled_FSet
    Pattern
    POPLmark_1B
    POPLmark_2B
