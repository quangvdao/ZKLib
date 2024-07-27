import Jolt.InteractiveOracleReduction.Basic

/-!
  # (Oracle) Commitment Schemes

  An _oracle_ commitment scheme for a given oracle `Oracle : {D : Data} → Input → Output`
  parameterized by some data `D` consists of two main operations:

  - `Commit` which commits to the data `D`
  - `Open`, which is an interactive oracle proof (with respect to a different oracle `OraclePrime`)
    for the relation that `Oracle {D} (input) = output`. Here the underlying data `D` is the
    witness, and `input`, `output` are the statement.
-/
