import Mathlib.Tactic
import Grassmannian.Charts
import Mathlib.Analysis.Calculus.ContDiff 
import Mathlib.Analysis.NormedSpace.OperatorNorm




noncomputable section 


namespace Grassmannian

/- Note: if my changes to mathlib are accepted, change the NontriviallyNormedField 𝕜 to 
NontriviallyNormedDivisionRing 𝕜 We will also need to introduce a NontriviallyNormedField over which
𝕜 is an algebra and E and U are NormedSpaces.-/
/-variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]
[NormedAddCommGroup U] [Module 𝕜 U] [BoundedSMul 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}-/

variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}


/- We prove that the charts are continuous, but first proving that their lifts are smooth (hence also continuous).-/


section Chart

/- Helper functions for ChartLift.-/
variable (𝕜 E r)


def ChartLiftHelper1 : (Fin r → E) →ₗ[𝕜] ((Fin r → 𝕜) →L[𝕜] E) :=
{
  toFun := fun v => (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v)  
  map_add' := by intro v w; simp only
                 apply ContinuousLinearMap.coe_injective
                 rw [ContinuousLinearMap.coe_add,Basis.coe_constrL, Basis.coe_constrL, Basis.coe_constrL]
                 simp only [map_add]
  map_smul' := by intro a v; simp only
                  apply ContinuousLinearMap.coe_injective
                  rw [ContinuousLinearMap.coe_smul, Basis.coe_constrL, Basis.coe_constrL]
                  simp only [map_smul, RingHom.id_apply]
}

lemma ChartLiftHelper1_norm_le (v : Fin r → E) : ‖ChartLiftHelper1 𝕜 E r v‖ ≤ r * ‖v‖ := by
  apply ContinuousLinearMap.op_norm_le_bound _ (mul_nonneg (Nat.cast_nonneg r) (norm_nonneg v))
  intro a 
  unfold ChartLiftHelper1
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Basis.constrL_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply] 
  refine le_trans (norm_sum_le (ι := Fin r) ⊤ (fun i => a i • v i)) ?_
  have hav : ∀ (i : Fin r), ‖a i • v i‖ ≤ ‖v‖ * ‖a‖ := by
    intro i
    rw [norm_smul, mul_comm]
    apply mul_le_mul (norm_le_pi_norm _ i) (norm_le_pi_norm _ i) (norm_nonneg _) (norm_nonneg _)
  refine le_trans (Finset.sum_le_card_nsmul ⊤ _ (‖v‖ * ‖a‖) (fun i _ => hav i)) ?_
  simp only [Finset.top_eq_univ, Finset.card_fin, nsmul_eq_mul]
  rw [mul_assoc]

def ChartLiftHelper1L :  (Fin r → E) →L[𝕜] ((Fin r → 𝕜) →L[𝕜] E) :=
LinearMap.mkContinuous (ChartLiftHelper1 𝕜 E r) r (ChartLiftHelper1_norm_le 𝕜 E r)

def ChartLiftHelper2 (φ : E →L[𝕜] (Fin r → 𝕜)) : (Fin r → E) →L[𝕜] (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜) :=
ContinuousLinearMap.comp (ContinuousLinearMap.compL 𝕜 (Fin r → 𝕜) E (Fin r → 𝕜) φ) (ChartLiftHelper1L 𝕜 E r)

def ChartLiftHelper2_equiv (φ : E →L[𝕜] (Fin r → 𝕜)) {v : Fin r → E} (hv : LinearIndependent 𝕜 (φ ∘ v)) :
(Fin r → 𝕜) ≃L[𝕜] (Fin r → 𝕜) := by
  apply LinearEquiv.toContinuousLinearEquiv
  apply LinearEquiv.ofBijective (φ.toLinearMap.comp (Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v))
  erw [GoodsetPreimage_iff_equiv'] at hv
  exact hv 

lemma ChartLiftHelp2_equiv_comp (φ : E →L[𝕜] (Fin r → 𝕜)) {v : Fin r → E} (hv : LinearIndependent 𝕜 (φ ∘ v)) :
ChartLiftHelper2 𝕜 E r φ v = (ChartLiftHelper2_equiv 𝕜 E r φ hv).toContinuousLinearMap := by
  ext u
  unfold ChartLiftHelper2_equiv ChartLiftHelper2
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.ofBijective_apply,
    LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Basis.constr_apply_fintype, Pi.basisFun_equivFun,
    LinearEquiv.refl_apply]
  unfold ChartLiftHelper1L ChartLiftHelper1
  simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply, Basis.constrL_apply]
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply]
  

variable {r}

def ChartLiftHelper3 (F G : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] : 
(F →L[𝕜] G) × (E →L[𝕜] F) → (E →L[𝕜] G) := fun x => ContinuousLinearMap.compL 𝕜 _ _ _ x.1 x.2

def IsBoundedBilinearMap_chartLiftHelper3 (F G : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] 
[NormedAddCommGroup G] [NormedSpace 𝕜 G] : IsBoundedBilinearMap 𝕜 (ChartLiftHelper3 𝕜 E F G) := by
  apply ContinuousLinearMap.isBoundedBilinearMap 

variable {𝕜 E}


lemma ChartLift_eq (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
ChartLift φ  = (fun v => ContinuousLinearMap.compL 𝕜 (Fin r → 𝕜) E U
    ((ContinuousLinearMap.snd 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) 
    (ChartLiftHelper3 𝕜 (Fin r → 𝕜) (Fin r → 𝕜) E ⟨(ChartLiftHelper1L 𝕜 E r v), 
    (Ring.inverse (ChartLiftHelper2 𝕜 E r ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp 
    φ.toContinuousLinearMap) v))⟩)) := by --sorry
  ext v 
  unfold ChartLift ChartLiftHelper3 ChartLiftHelper2 ChartLiftHelper1L ChartLiftHelper1 
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
    Function.comp_apply, Basis.constrL_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
    LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.compL_apply]
  rw [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_comp']
  simp only [ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe, Function.comp_apply, Basis.constrL_apply,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply]

 
 /-ChartLift is smooth at every point over the Goodset of φ.-/

lemma ChartLiftSmoothAt (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) {v : Fin r → E} (hv : LinearIndependent 𝕜 
  (((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) ∘ v)) : 
ContDiffAt 𝕜 ⊤ (ChartLift φ) v := by --sorry
  rw [ChartLift_eq]  
  apply ContDiffAt.continuousLinearMap_comp    
  have heq : (fun v => (ChartLiftHelper3 𝕜 (Fin r → 𝕜) (Fin r → 𝕜) E ⟨(ChartLiftHelper1L 𝕜 E r v), 
    (Ring.inverse (ChartLiftHelper2 𝕜 E r ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) v))⟩)) = 
    ((ChartLiftHelper3 𝕜 (Fin r → 𝕜) (Fin r → 𝕜) E) ∘ (fun v => ⟨(ChartLiftHelper1L 𝕜 E r v), 
    (Ring.inverse (ChartLiftHelper2 𝕜 E r ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) v))⟩)
    ) := by
    ext v 
    simp only [Function.comp_apply]
  rw [heq]
  apply ContDiff.comp_contDiffAt v (IsBoundedBilinearMap.contDiff (IsBoundedBilinearMap_chartLiftHelper3 _ _ _ _))
  apply ContDiffAt.prod
  . apply ContDiff.contDiffAt 
    apply ContinuousLinearMap.contDiff     
  . have heq : (fun v => Ring.inverse (ChartLiftHelper2 𝕜 E r 
      ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) v)) = 
      Ring.inverse ∘ (fun v => (ChartLiftHelper2 𝕜 E r ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp 
      φ.toContinuousLinearMap) v)) := by
      ext v
      simp only [Function.comp_apply]
    rw [heq]
    apply ContDiffAt.comp
    . rw [ChartLiftHelp2_equiv_comp 𝕜 E r ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp 
        φ.toContinuousLinearMap) hv]
      exact contDiffAt_ring_inverse 𝕜 (ContinuousLinearEquiv.toUnit (ChartLiftHelper2_equiv 𝕜 E r 
        ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) hv))  
    . apply ContDiff.contDiffAt 
      apply ContinuousLinearMap.contDiff 

lemma ChartLiftSmoothOn (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
ContDiffOn 𝕜 ⊤ (ChartLift φ) {v : Fin r → E | LinearIndependent 𝕜 
  (((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) ∘ v)} := by 
  rw [contDiffOn_open_iff_contDiffAt]
  . exact fun v => ChartLiftSmoothAt φ v.2
  . apply GoodsetIsOpen_aux1 

/- We deduce the continuity of ChartLift.-/

lemma ChartLiftContinuousAt (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) {v : Fin r → E} (hv : LinearIndependent 𝕜 
  (((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) ∘ v)) : 
ContinuousAt (ChartLift φ) v := ContDiffAt.continuousAt (ChartLiftSmoothAt φ hv)


lemma ChartLiftContinuousOn (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
ContinuousOn (ChartLift φ) {v : Fin r → E | LinearIndependent 𝕜 
  (((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) ∘ v)} := 
ContinuousAt.continuousOn (fun _ hv => ChartLiftContinuousAt φ hv)

/- Now we deduce the continuity of the chart itself.-/

lemma ChartContinuous (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
ContinuousOn (Chart φ) (Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap)) := by 
  set φ₁ := (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap
  apply (continuousOn_open_iff (GoodsetIsOpen φ₁)).mpr
  intro U hU 
  apply isOpen_coinduced.mpr 
  have heq : (Grassmannian.mk' 𝕜)⁻¹' (Goodset φ₁ ∩ (Chart φ)⁻¹' U) = (fun v => v.1)⁻¹'
    ({v : Fin r → E | LinearIndependent 𝕜 (φ₁ ∘ v)} ∩ (ChartLift φ)⁻¹' U) := by
    ext u
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, Set.preimage_inter, Set.mem_inter_iff,
      Set.mem_preimage, mk'_eq_mk, ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst',
      ContinuousLinearEquiv.coe_coe, Set.preimage_setOf_eq, Set.mem_setOf_eq] 
    rw [GoodsetPreimage, ChartLift_isLift]
    rfl 
  rw [heq]
  apply IsOpen.preimage
  . apply continuous_induced_dom
  . exact (continuousOn_open_iff (GoodsetIsOpen_aux1 φ₁)).mp (ChartLiftContinuousOn φ) U hU 

end Chart
 
section InverseChart

/- Now we do the same for the inverse chart. First we prove that its lift is smooth.-/

variable (𝕜 E)

def InverseChartLiftHelper1 (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] : 
(E →L[𝕜] F) × E → F := fun x => ContinuousLinearMap.apply' F (RingHom.id 𝕜) x.2 x.1 

def IsBoundedBilinearMap_inverseChartLiftHelper1 (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] : 
IsBoundedBilinearMap 𝕜 (InverseChartLiftHelper1 𝕜 E F) := by 
  apply ContinuousLinearMap.isBoundedBilinearMap 


def InverseChartLiftHelper2 (F G : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] 
[NormedSpace 𝕜 G] : 
(E →L[𝕜] F) × (E →L[𝕜] G) → (E →L[𝕜] F × G) := fun x => ContinuousLinearMap.prodₗᵢ 𝕜 x 



variable {𝕜 E}

lemma InverseChartLiftSmooth (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
ContDiff 𝕜 ⊤ (InverseChartLift φ) := by --sorry
  rw [contDiff_pi]
  intro i
  have heq : (fun f => InverseChartLift φ f i) = (fun f => InverseChartLiftHelper1 𝕜 _ _
    ⟨(ContinuousLinearMap.comp φ.symm.toContinuousLinearMap (ContinuousLinearMap.prod 
    (ContinuousLinearMap.id _ _) f)), ((Pi.basisFun 𝕜 (Fin r)) i)⟩) := by
    ext f
    unfold InverseChartLift InverseChartLiftHelper1
    simp only [Pi.basisFun_apply, Function.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id',
      id_eq, ContinuousLinearMap.apply_apply']
    rw [ContinuousLinearMap.coe_comp', Function.comp_apply]
    simp only [ContinuousLinearEquiv.coe_coe, EmbeddingLike.apply_eq_iff_eq]
    rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
  rw [heq]
  apply ContDiff.comp (IsBoundedBilinearMap.contDiff (IsBoundedBilinearMap_inverseChartLiftHelper1 _ _ _))
  apply ContDiff.prod
  . have heq : (fun f => (ContinuousLinearMap.comp φ.symm.toContinuousLinearMap (ContinuousLinearMap.prod 
      (ContinuousLinearMap.id _ _) f))) = (fun f => ContinuousLinearMap.compL 𝕜 _ _ _
      φ.symm.toContinuousLinearMap (ContinuousLinearMap.prod (ContinuousLinearMap.id _ _) f)) := by
      ext f 
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.compL_apply]
      rw [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
      rfl
    rw [heq]
    apply ContDiff.continuousLinearMap_comp
    have heq : (fun f => ContinuousLinearMap.prod (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜)) f) =
      (fun f => (ContinuousLinearMap.prodₗᵢ 𝕜 (𝕜 := 𝕜) (Fₗ := Fin r → 𝕜) (Gₗ := U)) 
      ⟨(ContinuousLinearMap.id 𝕜 (Fin r → 𝕜)), f⟩) := by
      apply funext
      intro f
      apply ContinuousLinearMap.ext
      intro a 
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq]
      erw [ContinuousLinearMap.prodₗ_apply]
      simp only [Equiv.toFun_as_coe_apply]
      rw [ContinuousLinearMap.prodEquiv_apply, ContinuousLinearMap.prod_apply]
      simp only [ContinuousLinearMap.coe_id', id_eq]
    rw [heq]
    apply ContDiff.continuousLinearMap_comp (LinearIsometryEquiv.toContinuousLinearEquiv (ContinuousLinearMap.prodₗᵢ 𝕜 
      (E := Fin r → 𝕜) (Fₗ := Fin r → 𝕜) (Gₗ := U) (𝕜 := 𝕜))).toContinuousLinearMap  
    apply ContDiff.prod
    . apply contDiff_const 
    . apply contDiff_id 
  . apply contDiff_const 

/- We deduce that the lift is continuous. -/

lemma InverseChartLiftContinuous (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
Continuous (InverseChartLift φ) :=
ContDiff.continuous (InverseChartLiftSmooth φ)

/- To relate this to the continuity of the inverse chart, it is convenient to define a variant of the lift 
with codomain {v : Fin r → E | LinearIndependent 𝕜 v}.-/

def InverseChartLift' (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :=
Set.codRestrict (InverseChartLift φ) {v : Fin r → E | LinearIndependent 𝕜 v}
(fun f => LinearIndependent.of_comp (ι := Fin r) (R := 𝕜) (v := InverseChartLift φ f) (M := E) (M' := Fin r → 𝕜) 
((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) 
(InverseChartLift_codomain φ f))


lemma InverseChartLift'_isLift (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
InverseChart φ = (Grassmannian.mk' 𝕜) ∘ (InverseChartLift' φ) := by 
  ext f
  rw [InverseChartLift_isLift]
  unfold InverseChartLift' InverseChartLift
  simp only [Function.comp_apply, mk'_eq_mk, Set.val_codRestrict_apply]
  
lemma InverseChartLift'Continuous (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
Continuous (InverseChartLift' φ) :=
Continuous.codRestrict (InverseChartLiftContinuous φ) _


/- We deduce that the inverse chart is continuous. -/

lemma InverseChartContinuous (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
Continuous (InverseChart φ) := by 
  rw [InverseChartLift'_isLift]
  exact Continuous.comp continuous_coinduced_rng (InverseChartLift'Continuous φ)



end InverseChart 


/- Definition of the chart as a local homeomorph. -/


def Chart_LocalHomeomorph (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) : 
LocalHomeomorph (Grassmannian 𝕜 E r) ((Fin r → 𝕜) →L[𝕜] U) := {Chart_LocalEquiv φ with  
  open_source := GoodsetIsOpen _ 
  open_target := isOpen_univ
  continuous_toFun := ChartContinuous φ
  continuous_invFun := Continuous.continuousOn (InverseChartContinuous φ) 
}

end Grassmannian

end 

