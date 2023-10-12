import Mathlib.Tactic
import Mathlib.Geometry.Manifold.ContMDiff
import Grassmannian.Manifold
import Grassmannian.contMDiff_openEmbedding 

open Classical 

namespace Grassmannian

section SmoothMaps 

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] {r : ℕ} [SeparatingDual 𝕜 E]
[Nonempty (Grassmannian 𝕜 E r)]

variable (𝕜 E r)


lemma Smooth.quotientMap : 
ContMDiff (modelWithCornersSelf 𝕜 (Fin r → E)) (E' := (Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) 
(M' := Grassmannian 𝕜 E r) (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) ⊤
(Grassmannian.mk' 𝕜) := by
  apply contMDiff_of_locally_contMDiffOn
  intro v
  set φ := PhiForChart (Epsilon 𝕜 E r) (Grassmannian.mk' 𝕜 v)
  set φ₁ := (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) _).comp φ.toContinuousLinearMap
  set hφ := PhiForChart_prop (Epsilon 𝕜 E r) (Grassmannian.mk' 𝕜 v)
  existsi {v | LinearIndependent 𝕜 (φ₁ ∘ v.1)}
  rw [and_iff_right (GoodsetIsOpen_aux2 φ₁), Set.mem_setOf_eq]
  erw [←(GoodsetPreimage φ₁ v.2), and_iff_right hφ]
  have heq : ∀ u, u ∈ {v | LinearIndependent 𝕜 (φ₁ ∘ v.1)} → (Grassmannian.mk' 𝕜) u = 
    ((InverseChart φ) ∘ (ChartLift φ) ∘ (fun v => v.1)) u := by
    intro u hu
    exact QuotientInChart φ u hu 
  rw [contMDiffOn_congr heq]
  apply ContMDiffOn.comp (g := InverseChart φ) (E' := ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)))
    (I' := modelWithCornersSelf 𝕜 ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r))) (t := ⊤)
  . have h1 : InverseChart φ = (instChartedSpaceGrassmannian.chartAt (Grassmannian.mk' 𝕜 v)).symm := by
      unfold ChartedSpace.chartAt instChartedSpaceGrassmannian ChartAt Chart_LocalHomeomorph Chart_LocalEquiv
      simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp, Set.top_eq_univ, LocalHomeomorph.mk_coe_symm,
        LocalEquiv.coe_symm_mk]  
    rw [h1]
    have h2 : ⊤ = (instChartedSpaceGrassmannian.chartAt (Grassmannian.mk' 𝕜 v)).toLocalEquiv.target := by
      unfold ChartedSpace.chartAt instChartedSpaceGrassmannian ChartAt Chart_LocalHomeomorph Chart_LocalEquiv
      simp only [Set.top_eq_univ]       
    rw [h2]
    apply contMDiffOn_chart_symm (I := ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r)
  . apply ContMDiffOn.comp (E' := Fin r → E) (I' := modelWithCornersSelf 𝕜 (Fin r → E)) 
      (t := {v : Fin r → E | LinearIndependent 𝕜 (φ₁ ∘ v)})
    . rw [contMDiffOn_iff_contDiffOn]
      apply ChartLiftSmoothOn 
    . apply ContMDiff.contMDiffOn 
      apply contMDiffOpenEmbedding
    . simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Set.preimage_setOf_eq,
      Set.setOf_subset_setOf, imp_self, Subtype.forall, implies_true, forall_const]
  . simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Set.top_eq_univ,
    Set.preimage_univ, Set.subset_univ]


/- If f is map from the Grassmannian to a manifold such that f ∘ Grassmannian.mk' is smooth, we prove that f is
smooth. This is useful to construct smooth maps from the Grassmannian.-/


lemma ChoiceOfChartForLift (v : {v : Fin r → E // LinearIndependent 𝕜 v}) :
∃ (φ : E ≃L[𝕜] (Fin r → 𝕜) × (ModelSpace 𝕜 E r)), ((Grassmannian.mk' 𝕜 v) ∈ Goodset
((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) _).comp φ.toContinuousLinearMap) ∧
((InverseChartLift_codRestrict φ) ∘ (Chart φ) ∘ (Grassmannian.mk' 𝕜)) v = v) := by
  set ψ := PhiForChart (Epsilon 𝕜 E r) (Grassmannian.mk' 𝕜 v)
  set hψ := PhiForChart_prop (Epsilon 𝕜 E r) (Grassmannian.mk' 𝕜 v)
  set ψ₁ := (ContinuousLinearMap.fst 𝕜 _ _).comp ψ.toContinuousLinearMap 
  rw [Grassmannian.mk'_eq_mk, GoodsetPreimage] at hψ
  set b : Fin r → (Fin r → 𝕜) := ψ₁ ∘ v.1 
  have hblin : LinearIndependent 𝕜 b := hψ 
  have hbspan : ⊤ ≤ Submodule.span 𝕜 (Set.range b) := by
    have heq : Set.range b = ψ₁ '' (Set.range v.1) := by
      rw [Set.range_comp] 
    rw [heq, Submodule.span_image]
    rw [GoodsetPreimage_iff_equiv] at hψ 
    have ha := hψ.2 
    rw [←LinearMap.range_eq_top] at ha 
    erw [LinearMap.range_comp] at ha 
    rw [Submodule.range_subtype] at ha 
    erw [ha]
  set basis := Basis.mk hblin hbspan 
  set f := (Basis.equiv basis (Pi.basisFun 𝕜 (Fin r)) (Equiv.refl _)).toContinuousLinearEquiv 
  set φ := ContinuousLinearEquiv.trans ψ (ContinuousLinearEquiv.prod f (ContinuousLinearEquiv.refl 𝕜 _))
  existsi φ
  constructor 
  . rw [Grassmannian.mk'_eq_mk, GoodsetPreimage]
    have heq : (ContinuousLinearMap.fst 𝕜 _ _).comp φ.toContinuousLinearMap = 
      f.toContinuousLinearMap.comp ((ContinuousLinearMap.fst 𝕜 _ _).comp ψ.toContinuousLinearMap) := by
      apply ContinuousLinearMap.ext; intro u
      rw [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_comp', 
        ContinuousLinearMap.coe_comp', Function.comp_apply, Function.comp_apply]
      erw [ContinuousLinearEquiv.trans_apply]
      rw [ContinuousLinearEquiv.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearEquiv.coe_refl', id_eq]
      simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.trans_apply, LinearEquiv.coe_toContinuousLinearEquiv']
    rw [heq, ContinuousLinearMap.coe_comp, LinearMap.coe_comp, Function.comp.assoc]
    apply LinearIndependent.map' hψ 
    simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
      ContinuousLinearEquiv.trans_apply, LinearEquiv.coe_toContinuousLinearEquiv, LinearEquiv.ker]
  . sorry


lemma Smooth.mapFromGrassmannian {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type u}
[TopologicalSpace H] {I : ModelWithCorners 𝕜 F H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
[SmoothManifoldWithCorners I M] {f : Grassmannian 𝕜 E r → M} (v : {v : Fin r → E // LinearIndependent 𝕜 v})
(hf : ContMDiffAt (modelWithCornersSelf 𝕜 (Fin r → E)) I ⊤ (f ∘ (Grassmannian.mk' 𝕜) : 
{v : Fin r → E // LinearIndependent 𝕜 v} → M) v) :
@ContMDiffAt 𝕜 _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _ _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _ 
(ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) (Grassmannian 𝕜 E r) _ _ F _ _ H _ I M _ _ ⊤ f 
(Grassmannian.mk' 𝕜 v):= by 
  set φ := Classical.choose (ChoiceOfChartForLift 𝕜 E r v)  
  set φ₁ := (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) _).comp φ.toContinuousLinearMap
  set hφ := Classical.choose_spec (ChoiceOfChartForLift 𝕜 E r v)
  set g := (f ∘ (Grassmannian.mk' 𝕜)) ∘ (InverseChartLift_codRestrict φ) ∘ (Chart φ) 
  have heq : f =ᶠ[nhds (Grassmannian.mk' 𝕜 v)] g := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    existsi (Goodset φ₁)
    constructor
    . refine IsOpen.mem_nhds ?_ hφ.1
      apply GoodsetIsOpen  
    . intro W hW 
      conv => lhs 
              rw [IdInChart φ hW]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq 
  apply ContMDiffAt.comp (E' := Fin r → E) (I' := modelWithCornersSelf 𝕜 (Fin r → E))
  . have heq : (InverseChartLift_codRestrict φ ∘ Chart φ) (Grassmannian.mk' 𝕜 v) = v := by
      conv => rhs
              rw [←hφ.2]
    rw [heq]
    exact hf  
  . apply ContMDiffAt.comp (E' := (Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) (I' := modelWithCornersSelf 𝕜
      ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)))
    . rw [ContMDiffAT_vs_openEmbedding (modelWithCornersSelf 𝕜 ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r))) 
        (LinearIndependentToAll 𝕜 E r) (InverseChartLift_codRestrict φ)]
      have heq : (fun v => v.1) ∘ InverseChartLift_codRestrict φ = InverseChartLift φ := by
        apply funext; intro f
        unfold InverseChartLift_codRestrict
        simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, Function.comp_apply,
          Set.val_codRestrict_apply]
      rw [heq]
      rw [contMDiffAt_iff_contDiffAt] 
      apply ContDiff.contDiffAt
      exact InverseChartLiftSmooth φ 
    . have heq : Chart φ = (Chart_LocalHomeomorph φ).toFun := rfl 
      rw [heq]
      apply contMDiffAt_of_mem_maximalAtlas 
      . apply SmoothManifoldWithCorners.subset_maximalAtlas
        unfold atlas ChartedSpace.atlas instChartedSpaceGrassmannian 
        simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, Function.comp_apply,
          Set.mem_setOf_eq] 
        existsi φ
        rfl
      . unfold Chart_LocalHomeomorph Chart_LocalEquiv
        simp only  
        exact hφ.1 


end SmoothMaps 