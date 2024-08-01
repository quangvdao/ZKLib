import Jolt.ConstraintSystem.Constants
import Jolt.ConstraintSystem.Field
import Jolt.Relation.Lookup

/-!
  # Lookup Relations in Jolt
-/

namespace Jolt

variable (F : Type) [JoltField F]

class InstructionLookup where
  lookup : F → F → F
  lookup_correct : ∀ x y, lookup x y = x + y



namespace Lookup






end Lookup

end Jolt
