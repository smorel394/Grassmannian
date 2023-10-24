import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading




open Classical
noncomputable section 

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





