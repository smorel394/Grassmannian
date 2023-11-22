import Mathlib.Tactic
--import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
--import Mathlib.Analysis.NormedSpace.OperatorNorm
--import Mathlib.Topology.Algebra.Module.FiniteDimension
--import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
--import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
--import Mathlib.Data.Real.Basic
import Grassmannian.SmoothMaps  
import Grassmannian.Exterior


open Classical
--noncomputable section 


section test1

variable (R M : Type*) [Field R] [AddCommGroup M] [Module R M] (r n : ℕ)

--def Grassmannian : Set (Submodule R M) := {W : Submodule R M | FiniteDimensional R W ∧ FiniteDimensional.finrank R W = r}

def PluckerMap (x : Grassmannian R M r) : Grassmannian R (ExteriorAlgebra R M) (Nat.choose r n) := by
  set W := (0 : Submodule R (ExteriorAlgebra R M))
  refine ⟨W, ?_⟩

end test1 

universe u v w 
variable (R : Type u) (M : Type v) (N : Type w) [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]


#exit 

section test2

universe u v

variable {𝕜 : Type u} [hnorm : NormedField 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F : Type w} [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜 F] 
  [FiniteDimensional 𝕜 E] (n : ℕ)

def FG : FiniteDimensional 𝕜 (LinearMap.range (ExteriorAlgebra.ι 𝕜 : E →ₗ[𝕜] ExteriorAlgebra 𝕜 E)^n) := by
  rw [←Submodule.fg_iff_finiteDimensional]
  apply Submodule.FG.pow 
  rw [LinearMap.range_eq_map]
  apply Submodule.FG.map 
  rw [←Module.finite_def]
  exact inferInstance 

end test2




