import Mathlib.Tactic
import Grassmannian.SmoothMaps  
import Grassmannian.Exterior

open Classical

namespace Grassmannian 

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (r n : ℕ) 

def PluckerMap (x : Grassmannian K V r) : Grassmannian K (ExteriorAlgebra.GradedPiece K V n) (Nat.choose r n) := by
  refine ⟨LinearMap.range (ExteriorAlgebra.GradedPiece.map n (Submodule.subtype x.1)), ?_⟩
  letI := x.2.1 
  letI := ExteriorAlgebra.GradedPiece.Finite K x.1 n  
  constructor
  . apply Module.Finite.range 
  . rw [LinearMap.finrank_range_of_inj]
    . rw [ExteriorAlgebra.GradedPiece.finrank_finiteDimensional] 
      . rw [x.2.2]
      . apply Module.Free.of_divisionRing 
    . apply ExteriorAlgebra.GradedPiece.map_injective_field 
      apply Submodule.ker_subtype 
  

#exit 

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] {r n : ℕ} [SeparatingDual 𝕜 E]
[Nonempty (Grassmannian 𝕜 E r)]

variable (𝕜 E r n)


  

