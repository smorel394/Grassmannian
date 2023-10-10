import Mathlib.Tactic
import Grassmannian.TopCharts


noncomputable section 


namespace Grassmannian

/- Note: if my changes to mathlib are accepted, change the NontriviallyNormedField 𝕜 to 
NontriviallyNormedDivisionRing 𝕜 We will also need to introduce a NontriviallyNormedField over which
𝕜 is an algebra and E and U are NormedSpaces.-/
/-variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]
[NormedAddCommGroup U] [Module 𝕜 U] [BoundedSMul 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}-/

variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}

def ChangeOfChart (φ ψ : E ≃L[𝕜] (Fin r → 𝕜) × U) : ((Fin r → 𝕜) →L[𝕜] U) → ((Fin r → 𝕜) →L[𝕜] U) :=
(Chart φ) ∘ (InverseChart ψ)

lemma ChangeOfChartDomain (φ ψ : E ≃L[𝕜] (Fin r → 𝕜) × U) : (LocalHomeomorph.trans (LocalHomeomorph.symm 
(Chart_LocalHomeomorph ψ)) (Chart_LocalHomeomorph φ)).toLocalEquiv.source = 
{f : ((Fin r → 𝕜) →L[𝕜] U) | Submodule.map ψ.symm (LinearMap.graph f) ⊓ 
LinearMap.ker ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) = ⊥} := by
  ext f 
  simp only [LocalHomeomorph.trans_toLocalEquiv, LocalHomeomorph.symm_toLocalEquiv, LocalEquiv.trans_source,
    LocalEquiv.symm_source, LocalHomeomorph.coe_coe_symm, Set.mem_inter_iff, Set.mem_preimage, ge_iff_le,
    Set.mem_setOf_eq]
  unfold Chart_LocalHomeomorph Chart_LocalEquiv
  simp only [Set.top_eq_univ, Set.mem_univ, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst,
    LocalHomeomorph.mk_coe_symm, LocalEquiv.coe_symm_mk, true_and, ge_iff_le]
  unfold InverseChart Goodset
  simp only [ge_iff_le, Set.mem_setOf_eq]
  rfl

lemma ChangeOfChartSmooth (φ ψ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
ContDiffOn 𝕜 ⊤ (ChangeOfChart φ ψ) {f : ((Fin r → 𝕜) →L[𝕜] U) | Submodule.map ψ.symm (LinearMap.graph f) ⊓ 
LinearMap.ker ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) = ⊥} := by --sorry
  have heq : ChangeOfChart φ ψ = (ChartLift φ) ∘ (InverseChartLift ψ) := by
    ext f 
    unfold ChangeOfChart
    simp only [Function.comp_apply]
    rw [InverseChartLift_isLift, ChartLift_isLift]
  rw [heq]
  have hdom : {f : ((Fin r → 𝕜) →L[𝕜] U) | Submodule.map ψ.symm (LinearMap.graph f) ⊓ 
    LinearMap.ker ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) = ⊥} = ⊤ ∩
    (InverseChartLift ψ)⁻¹'  {v : Fin r → E | LinearIndependent 𝕜 
    (((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) ∘ v)} := by
    ext f
    simp only [ge_iff_le, Set.mem_setOf_eq, Set.top_eq_univ, 
      ContinuousLinearEquiv.coe_coe, Set.preimage_setOf_eq, Set.univ_inter]
    unfold InverseChartLift
    simp only 
    constructor
    . intro h 
      rw [←disjoint_iff] at h
      apply LinearIndependent.map (f := ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap).toLinearMap)
      . apply LinearIndependent.map' 
        . apply LinearIndependent.map'
          . apply Basis.linearIndependent 
          . simp only [ContinuousLinearMap.coe_prod, ContinuousLinearMap.coe_id, LinearMap.ker_prod, LinearMap.ker_id,
            ge_iff_le, bot_le, inf_of_le_left]
        . simp only [ContinuousLinearEquiv.symm_toLinearEquiv, LinearEquiv.ker]
      . simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst]
        rw [Set.range_comp, Set.range_comp]
        rw [Submodule.span_image, Submodule.span_image]
        rw [Basis.span_eq (Pi.basisFun 𝕜 (Fin r))]
        simp only [Submodule.map_top]
        erw [←LinearMap.graph_eq_range_prod]
        exact h 
    . intro h 
      ext u 
      simp only [ge_iff_le, Submodule.mem_inf, Submodule.mem_map, LinearMap.mem_graph_iff, ContinuousLinearMap.coe_coe,
        Prod.exists, exists_eq_left, LinearMap.mem_ker, ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst',
        ContinuousLinearEquiv.coe_coe, Function.comp_apply, Submodule.mem_bot]
      constructor 
      . intro ⟨hu1, hu2⟩
        obtain ⟨a, hau⟩ := hu1 
        have haeq : a = Finset.sum ⊤ (fun i => (a i) • ((Pi.basisFun 𝕜 (Fin r)) i)) := by
          ext i 
          simp only [Finset.top_eq_univ, Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.stdBasis_apply',
            smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [←hau, haeq] at hu2 
        have heq :   (Finset.sum ⊤ fun i => a i • (Pi.basisFun 𝕜 (Fin r)) i,
          f (Finset.sum ⊤ fun i => a i • (Pi.basisFun 𝕜 (Fin r)) i)) = Finset.sum ⊤
          fun i => ⟨a i • (Pi.basisFun 𝕜 (Fin r)) i, f (a i • (Pi.basisFun 𝕜 (Fin r)) i)⟩ := by 
          rw [map_sum]
          apply Prod.ext 
          . rw [Prod.fst_sum]
          . rw [Prod.snd_sum]
        rw [heq] at hu2  
        have heq : ∀ i, (a i • (Pi.basisFun 𝕜 (Fin r)) i, f (a i • (Pi.basisFun 𝕜 (Fin r)) i)) = 
          a i • ((Pi.basisFun 𝕜 (Fin r)) i, f ((Pi.basisFun 𝕜 (Fin r)) i)) := by
          intro i
          simp only [map_smul, Prod.smul_mk]
        rw [Finset.sum_congr (Eq.refl _) (fun i _ => heq i)] at hu2 
        rw [map_sum, map_sum] at hu2 
        change LinearMap.fst 𝕜 (Fin r → 𝕜) U _ = 0 at hu2 
        rw [map_sum] at hu2
        have heq : ∀ i, (LinearMap.fst 𝕜 (Fin r → 𝕜) U)
          (φ ((ContinuousLinearEquiv.symm ψ) (a i • ((Pi.basisFun 𝕜 (Fin r)) i, f ((Pi.basisFun 𝕜 (Fin r)) i))))) =
           a i • (LinearMap.fst 𝕜 (Fin r → 𝕜) U)
          (φ ((ContinuousLinearEquiv.symm ψ) (((Pi.basisFun 𝕜 (Fin r)) i, f ((Pi.basisFun 𝕜 (Fin r)) i))))) := by
          intro i
          rw [map_smul, map_smul, map_smul]
        rw [Finset.sum_congr (Eq.refl _) (fun i _ => heq i)] at hu2 
        rw [Fintype.linearIndependent_iff] at h
        have hazero := h a hu2       
        rw [Finset.sum_eq_zero] at haeq
        . rw [haeq] at hau 
          simp only [map_zero] at hau  
          erw [map_zero] at hau 
          exact Eq.symm hau 
        . intro i _ 
          rw [hazero i, zero_smul]
      . intro hu 
        rw [hu]
        simp only [AddEquivClass.map_eq_zero_iff, Prod.mk_eq_zero, exists_eq_left, map_zero, Prod.fst_zero, and_self]
  rw [hdom]
  apply ContDiffOn.comp' (f := InverseChartLift ψ) (g := ChartLift φ) (s := ⊤) 
  . exact ChartLiftSmoothOn φ
  . apply ContDiff.contDiffOn
    exact InverseChartLiftSmooth ψ

end Grassmannian

end 



