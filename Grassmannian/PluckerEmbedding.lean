import Mathlib.Tactic
import Grassmannian.SmoothMaps  
import Grassmannian.Exterior

open Classical

namespace Grassmannian 

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] {r n : ℕ} [SeparatingDual 𝕜 E]
[Nonempty (Grassmannian 𝕜 E r)]

variable (𝕜 E r n)

def PluckerMap (x : Grassmannian 𝕜 E r) : Grassmannian 𝕜 (ExteriorAlgebra.GradedPiece 𝕜 E n) (Nat.choose r n) := by
  set W := ExteriorAlgebra.GradedPiece 𝕜 x.1 n 
  sorry

