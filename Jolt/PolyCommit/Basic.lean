import Jolt.Data.UnivariatePoly
import Jolt.Data.MultilinearPoly
import Jolt.Data.MultivariatePoly


-- Formalism for polynomial commitments

variable {R : Type} [Inhabited R] [CommSemiring R]
variable {CommFormat : Type}

def MvPolyCommit (R : Type) (CommFormat : Type) := MvPoly R → CommFormat
