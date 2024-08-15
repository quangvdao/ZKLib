import ZKLib.InteractiveOracleReduction.Basic

/-!
  # Interactive Oracle Proof (IOP) as a special case of IOR

  This file contains the definition of the Interactive Oracle Proof (IOP) protocol as a special case
  of the more general Interactive Oracle Reduction (IOR) protocol, when we specialize the output
  relation to the Boolean relation `boolRel`.
-/



-- TODO: IOP as a special case of IOR, where `relOut = boolRel PEmpty` (i.e. the output statement is
-- `Bool`, and the output witness is empty)
namespace IOP

structure Spec extends IOR.Spec where
  relOut := boolRel Empty

structure PartialTranscript (spec : Spec) (i : Fin (spec.numRounds + 1)) extends
    IOR.PartialTranscript spec.toSpec i

structure Transcript (spec : Spec) extends IOR.Transcript spec.toSpec

structure VerifierView (spec : Spec) extends IOR.VerifierView spec.toSpec

structure Prover (spec : Spec) extends IOR.Prover spec.toSpec

structure Verifier (spec : Spec) extends IOR.Verifier spec.toSpec

structure Protocol (spec : Spec) extends Prover spec, Verifier spec

-- TODO: port over all the security definitions from `IOR`

-- def run (spec : Spec) (protocol : Protocol spec) (stmtIn : spec.relIn.Statement) (witIn : spec.relIn.Witness) :=
--   IOR.run spec.toSpec protocol.toProver protocol.toVerifier stmtIn witIn

-- def completeness (spec : Spec) (protocol : Protocol spec) (completenessError : I) : Prop :=
--   ∀ stmtIn : spec.relIn.Statement,
--   ∀ witIn : spec.relIn.Witness,
--   spec.relIn.isValid stmtIn witIn = true →
--       let output := run spec protocol.toProver protocol.toVerifier stmtIn witIn
--       let prob := spec.relOut.isValid' <$> output
--       prob true ≥ 1 - completenessError



end IOP
