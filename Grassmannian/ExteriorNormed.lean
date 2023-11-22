import Mathlib.Tactic
import Grassmannian.Exterior
import Grassmannian.SeparatingMaps 
import Grassmannian.ContinuousAlternatingMap


open Classical

set_option maxHeartbeats 1000000

namespace ExteriorAlgebra 

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℕ} 


def seminormAlternatingForm (f : AlternatingMap 𝕜 E 𝕜 (Fin r)) : Seminorm 𝕜 (GradedPiece 𝕜 E r).carrier := 
{ toFun := fun x => ‖(GradedPiece.liftAlternating r f x)‖
  map_zero' := by simp only [map_zero, norm_zero]
  add_le' := fun r s => by simp only; rw [LinearMap.map_add]; exact le_trans (norm_add_le _ _) (le_refl _)
  neg' := sorry
  smul' := sorry}

  
  
  
  #exit 
  set u := GradedPiece.liftAlternating r f
  set p : Seminorm 𝕜 𝕜 := sorry
  refine Seminorm.comp p u (𝕜 := 𝕜) (𝕜₂ := 𝕜) (σ₁₂ := RingHom.id 𝕜) (E₂ := 𝕜) (E := (GradedPiece 𝕜 E r).carrier) 



  

