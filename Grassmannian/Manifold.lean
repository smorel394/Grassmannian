import Mathlib.Tactic
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Grassmannian.FiniteCodimension
import Grassmannian.ChangeOfChart

open Classical 

namespace Grassmannian

section ChartedSpace 

variable {𝕜 E F U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] {r : ℕ}
(ε : E ≃L[𝕜] (Fin r → 𝕜) × U)

variable (𝕜 E U r)

/-class MySpecialEquiv  :=
  (myEquiv : E ≃L[𝕜] (Fin r → 𝕜) × U)-/

variable {𝕜 E U r}

--variable (ε : MySpecialEquiv 𝕜 E U r) 

def ContinuousEquivWithModel : LinearMap.ker ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp 
ε.toContinuousLinearMap) ≃L[𝕜] U := by
  set φ₁ := (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp ε.toContinuousLinearMap
  set φ₂ := (ContinuousLinearMap.snd 𝕜 (Fin r → 𝕜) U).comp ε.toContinuousLinearMap
  set f := ContinuousLinearMap.comp ε.symm.toContinuousLinearMap (ContinuousLinearMap.inr 𝕜 (Fin r → 𝕜) U)
  have hf : ∀ (u : U), f u ∈ LinearMap.ker φ₁ := by
    intro u
    simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
      ContinuousLinearMap.inr_apply, LinearMap.mem_ker, ContinuousLinearMap.coe_fst',
      ContinuousLinearEquiv.apply_symm_apply]
  apply ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.comp φ₂ (Submodule.subtypeL (LinearMap.ker φ₁)))
    (ContinuousLinearMap.codRestrict f (LinearMap.ker φ₁) hf)
  . intro v
    rw [←SetCoe.ext_iff]
    simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
      Submodule.coe_subtypeL', Submodule.coeSubtype, Function.comp_apply, ContinuousLinearMap.coe_codRestrict_apply,
      ContinuousLinearMap.inr_apply]
    have hv : (ε v).fst = 0 := v.2 
    rw [←hv, Prod.mk.eta]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  . intro u 
    simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
      Submodule.coe_subtypeL', Submodule.coeSubtype, Function.comp_apply, ContinuousLinearMap.coe_codRestrict_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.apply_symm_apply]

variable [SeparatingDual 𝕜 E]

noncomputable abbrev PhiForChart (W : Grassmannian 𝕜 E r) : E ≃L[𝕜] (Fin r → 𝕜) × U := by
  set φ := Classical.choose (SeparatingMaps.ofSeparatingDual inferInstance r W)
  set hφ := Classical.choose_spec (SeparatingMaps.ofSeparatingDual inferInstance r W)
  have hrank : FiniteDimensional.finrank 𝕜 (Fin r → 𝕜) = r := by simp only [FiniteDimensional.finrank_fintype_fun_eq_card,
    Fintype.card_fin]
  have hsurj : Function.Surjective φ := by
    erw [SeparatingMaps_iff_surjective _ r W hrank φ] at hφ
    intro a 
    obtain ⟨v, hv⟩ := hφ a
    existsi v.1 
    simp only [ge_iff_le, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype, Function.comp_apply] at hv
    exact hv 
  have hψ : Function.Surjective (ContinuousLinearMap.comp (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U) 
    ε.toContinuousLinearMap) := by
    rw [ContinuousLinearMap.coe_comp']
    apply Function.Surjective.comp 
    . rw [ContinuousLinearMap.coe_fst']
      intro a 
      existsi ContinuousLinearMap.inl 𝕜 _ _ a 
      simp only [ContinuousLinearMap.inl_apply]
    . apply ContinuousLinearEquiv.surjective     
  refine ContinuousLinearEquiv.trans (FiniteCodimensionContinuousLinearEquivProd hsurj) (ContinuousLinearEquiv.prod 
    (ContinuousLinearEquiv.refl 𝕜 (Fin r → 𝕜)) 
    (ContinuousLinearEquiv.trans (FiniteCodimensionContinuousLinearEquiv hsurj hψ hrank hrank) 
    (ContinuousEquivWithModel ε)))
  

noncomputable abbrev PhiForChart_prop (W : Grassmannian 𝕜 E r) :
W ∈ Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp (PhiForChart ε W).toContinuousLinearMap) := by --sorry
  change W.1 ⊓ _ = ⊥  
  rw [Submodule.eq_bot_iff]
  intro u 
  rw [Submodule.mem_inf]
  intro ⟨huW, hu⟩
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, LinearMap.mem_ker, LinearMap.coe_comp,
    ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, Function.comp_apply, ContinuousLinearEquiv.trans_apply,
    LinearMap.fst_apply] at hu  
  rw [ContinuousLinearEquiv.prod_apply, ContinuousLinearEquiv.coe_refl'] at hu 
  simp only [id_eq] at hu 
  unfold FiniteCodimensionContinuousLinearEquivProd at hu
  rw [ContinuousLinearEquiv.equivOfInverse_apply, ContinuousLinearMap.prod_apply] at hu
  simp only at hu   
  set φ := Classical.choose (SeparatingMaps.ofSeparatingDual inferInstance r W)
  set hφ := Classical.choose_spec (SeparatingMaps.ofSeparatingDual inferInstance r W)
  change u ∈ LinearMap.ker φ at hu 
  rw [←(Submodule.mem_bot 𝕜), ←hφ, Submodule.mem_inf]
  exact ⟨huW, hu⟩


noncomputable def ChartAt (W : Grassmannian 𝕜 E r) : LocalHomeomorph (Grassmannian 𝕜 E r) ((Fin r → 𝕜) →L[𝕜] U) := 
Chart_LocalHomeomorph (PhiForChart ε W)

lemma ChartAt_source (W : Grassmannian 𝕜 E r) :
(ChartAt ε W).source = Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp 
(PhiForChart ε W).toContinuousLinearMap) := by
  unfold ChartAt Chart_LocalHomeomorph Chart_LocalEquiv
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst]


noncomputable def ChartedSpaceGrassmannian : ChartedSpace ((Fin r → 𝕜) →L[𝕜] U) (Grassmannian 𝕜 E r) := 
{
  atlas := {f | ∃ (φ : E ≃L[𝕜] (Fin r → 𝕜) × U), f = Chart_LocalHomeomorph φ}
  chartAt := fun W => ChartAt ε W   
  mem_chart_source := fun W => by rw [ChartAt_source ε W]; exact PhiForChart_prop ε W  
  chart_mem_atlas := fun W => by unfold ChartAt; simp only [Set.mem_setOf_eq]
                                 existsi PhiForChart ε W 
                                 rfl
}

variable (𝕜 U r)

def ModelGrassmannian := modelWithCornersSelf 𝕜 ((Fin r → 𝕜) →L[𝕜] U)

variable {𝕜 U r}

noncomputable def SmoothManifoldGrassmannian : 
@SmoothManifoldWithCorners 𝕜 _ _ _ _ _ _ (ModelGrassmannian 𝕜 U r) (Grassmannian 𝕜 E r) _
(ChartedSpaceGrassmannian ε):= 
@smoothManifoldWithCorners_of_contDiffOn _ _ _ _ _ _ _ (ModelGrassmannian 𝕜 U r) (Grassmannian 𝕜 E r) _
(ChartedSpaceGrassmannian ε)
(
  by intro e e' he he'
     match he, he' with 
     | ⟨φ, he⟩, ⟨ψ, he'⟩ => 
       unfold ModelGrassmannian
       rw [modelWithCornersSelf_coe, Function.comp.left_id, modelWithCornersSelf_coe_symm, Function.comp.right_id, 
         Set.range_id, Set.inter_univ, Set.preimage_id_eq, id_eq, he, he']
       rw [ChangeOfChartDomain]
       apply ChangeOfChartSmooth
)

end ChartedSpace 


section Manifold

variable {𝕜 E F U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] {r : ℕ}
[SeparatingDual 𝕜 E] [Nonempty (Grassmannian 𝕜 E r)]

variable (𝕜 E r)

noncomputable def ModelSpace : Submodule 𝕜 E := 
LinearMap.ker (Classical.choose (SeparatingMaps.ofSeparatingDual inferInstance r (Classical.choice inferInstance)))

noncomputable def Epsilon : E ≃L[𝕜] (Fin r → 𝕜) × (ModelSpace 𝕜 E r) := by
  set W : Grassmannian 𝕜 E r := Classical.choice inferInstance 
  set φ := Classical.choose (SeparatingMaps.ofSeparatingDual inferInstance r W)  
  set hφ := Classical.choose_spec (SeparatingMaps.ofSeparatingDual inferInstance r W)
  have hsurj : Function.Surjective φ := by
    erw [SeparatingMaps_iff_surjective _ r W] at hφ
    intro a 
    obtain ⟨v, hv⟩ := hφ a
    existsi v.1 
    simp only [ge_iff_le, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype, Function.comp_apply] at hv
    exact hv 
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact FiniteCodimensionContinuousLinearEquivProd hsurj 



variable {𝕜 E r}


noncomputable instance instChartedSpaceGrassmannian :
ChartedSpace ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) (Grassmannian 𝕜 E r) := 
{
  atlas := {f | ∃ (φ : E ≃L[𝕜] (Fin r → 𝕜) × (ModelSpace 𝕜 E r)), f = Chart_LocalHomeomorph φ}
  chartAt := fun W => ChartAt (Epsilon 𝕜 E r) W   
  mem_chart_source := fun W => by rw [ChartAt_source (Epsilon 𝕜 E r) W]; exact PhiForChart_prop (Epsilon 𝕜 E r) W  
  chart_mem_atlas := fun W => by unfold ChartAt; simp only [Set.mem_setOf_eq]
                                 existsi PhiForChart (Epsilon 𝕜 E r) W 
                                 rfl
}




noncomputable instance instSmoothManifoldGrassmannian : 
SmoothManifoldWithCorners (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) (Grassmannian 𝕜 E r) := 
smoothManifoldWithCorners_of_contDiffOn (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) (Grassmannian 𝕜 E r) 
(
  by intro e e' he he'
     match he, he' with 
     | ⟨φ, he⟩, ⟨ψ, he'⟩ => 
       unfold ModelGrassmannian
       rw [modelWithCornersSelf_coe, Function.comp.left_id, modelWithCornersSelf_coe_symm, Function.comp.right_id, 
         Set.range_id, Set.inter_univ, Set.preimage_id_eq, id_eq, he, he']
       rw [ChangeOfChartDomain]
       apply ChangeOfChartSmooth
)


/- Smooth manifold structure on {v : Fin r → E // LinearIndependent 𝕜 v}, under the same hypotheses. First we put a
Nonempty instance on that type.-/

instance instNonemptyGrassmannianLift : Nonempty {v : Fin r → E // LinearIndependent 𝕜 v} := 
(NonemptyGrassmannian_iff 𝕜 E r).mpr inferInstance 

variable (𝕜 E r)

def LinearIndependentToAll : OpenEmbedding (fun v : {v : Fin r → E // LinearIndependent 𝕜 v} => (v.1 : Fin r → E)) := 
{
  induced := by tauto
  inj := by intro u v; rw [SetCoe.ext_iff]; simp only [imp_self]
  open_range := by simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq]
                   exact isOpen_setOf_linearIndependent 
} 

lemma LinearIndependentToAll.inverse {v : Fin r → E} (hv : LinearIndependent 𝕜 v) :
v = (OpenEmbedding.toLocalHomeomorph (fun v => v.1) (LinearIndependentToAll 𝕜 E r)).symm v := by 
  have heq : v = (fun v => v.1) (⟨v, hv⟩ : {v : Fin r → E // LinearIndependent 𝕜 v}) := by simp only 
  nth_rewrite 2 [heq]
  nth_rewrite 2 [←(OpenEmbedding.toLocalHomeomorph_apply _ (LinearIndependentToAll 𝕜 E r))]
  rw [LocalHomeomorph.left_inv]
  tauto 

variable {𝕜 E r}

noncomputable instance instChartedSpaceLinearIndependent : ChartedSpace (Fin r → E) 
{v : Fin r → E // LinearIndependent 𝕜 v} := 
(LinearIndependentToAll 𝕜 E r).singletonChartedSpace 


lemma LinearIndependent.chartAt (v : {v : Fin r → E // LinearIndependent 𝕜 v}) : 
instChartedSpaceLinearIndependent.chartAt v = OpenEmbedding.toLocalHomeomorph (fun v => v.1) 
(LinearIndependentToAll 𝕜 E r) := by tauto 


lemma LinearIndependent.chartAt.target (v : {v : Fin r → E // LinearIndependent 𝕜 v}) : 
LocalEquiv.target (LocalHomeomorph.toLocalEquiv (instChartedSpaceLinearIndependent.2 v)) = 
{v : Fin r → E // LinearIndependent 𝕜 v} := by 
  rw [LinearIndependent.chartAt, OpenEmbedding.toLocalHomeomorph_target]
  simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, Subtype.range_coe_subtype]
    

lemma LinearIndependent.chartAt.inverse (v : {v : Fin r → E // LinearIndependent 𝕜 v}) 
{w : Fin r → E} (hw : LinearIndependent 𝕜 w) :
w = (instChartedSpaceLinearIndependent.chartAt v).symm w := by 
  rw [LinearIndependent.chartAt]
  exact LinearIndependentToAll.inverse 𝕜 E r hw 

instance : SmoothManifoldWithCorners (modelWithCornersSelf 𝕜 (Fin r → E)) {v : Fin r → E // LinearIndependent 𝕜 v} :=
(LinearIndependentToAll 𝕜 E r).singleton_smoothManifoldWithCorners (modelWithCornersSelf 𝕜 (Fin r → E))


end Manifold

end Grassmannian 
