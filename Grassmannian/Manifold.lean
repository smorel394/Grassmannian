import Mathlib.Tactic
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Grassmannian.FiniteCodimension
import Grassmannian.ChangeOfChart

variable {𝕜 E F U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] {r : ℕ}

variable (𝕜 E U r)

class MySpecialEquiv  :=
  (myEquiv : E ≃L[𝕜] (Fin r → 𝕜) × U)

variable {𝕜 E U r}

variable (ε : MySpecialEquiv 𝕜 E U r) (hsep : SeparatingDual 𝕜 E)

def ContinuousEquivWithModel : LinearMap.ker ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp 
ε.myEquiv.toContinuousLinearMap) ≃L[𝕜] U := by
  set φ₁ := (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp ε.myEquiv.toContinuousLinearMap
  set φ₂ := (ContinuousLinearMap.snd 𝕜 (Fin r → 𝕜) U).comp ε.myEquiv.toContinuousLinearMap
  set f := ContinuousLinearMap.comp ε.myEquiv.symm.toContinuousLinearMap (ContinuousLinearMap.inr 𝕜 (Fin r → 𝕜) U)
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
    have hv : (ε.myEquiv v).fst = 0 := v.2 
    rw [←hv, Prod.mk.eta]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  . intro u 
    simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
      Submodule.coe_subtypeL', Submodule.coeSubtype, Function.comp_apply, ContinuousLinearMap.coe_codRestrict_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.apply_symm_apply]

namespace Grassmannian

noncomputable abbrev PhiForChart (W : Grassmannian 𝕜 E r) : E ≃L[𝕜] (Fin r → 𝕜) × U := by
  set φ := Classical.choose (SeparatingMaps.ofSeparatingDual hsep r W)
  set hφ := Classical.choose_spec (SeparatingMaps.ofSeparatingDual hsep r W)
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
    ε.myEquiv.toContinuousLinearMap) := by
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
W ∈ Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp (PhiForChart ε hsep W).toContinuousLinearMap) := by --sorry
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
  set φ := Classical.choose (SeparatingMaps.ofSeparatingDual hsep r W)
  set hφ := Classical.choose_spec (SeparatingMaps.ofSeparatingDual hsep r W)
  change u ∈ LinearMap.ker φ at hu 
  rw [←(Submodule.mem_bot 𝕜), ←hφ, Submodule.mem_inf]
  exact ⟨huW, hu⟩


noncomputable def ChartAt (W : Grassmannian 𝕜 E r) : LocalHomeomorph (Grassmannian 𝕜 E r) ((Fin r → 𝕜) →L[𝕜] U) := 
Chart_LocalHomeomorph (PhiForChart ε hsep W)

lemma ChartAt_source (W : Grassmannian 𝕜 E r) :
(ChartAt ε hsep W).source = Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp 
(PhiForChart ε hsep W).toContinuousLinearMap) := by
  unfold ChartAt Chart_LocalHomeomorph Chart_LocalEquiv
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst]

noncomputable instance instChartedSpaceGrassmannian : ChartedSpace ((Fin r → 𝕜) →L[𝕜] U) (Grassmannian 𝕜 E r) := 
{
  atlas := {f | ∃ (φ : E ≃L[𝕜] (Fin r → 𝕜) × U), f = Chart_LocalHomeomorph φ}
  chartAt := fun W => ChartAt ε hsep W   
  mem_chart_source := fun W => by rw [ChartAt_source ε hsep W]; exact PhiForChart_prop ε hsep W  
  chart_mem_atlas := fun W => by unfold ChartAt; simp only [Set.mem_setOf_eq]
                                 existsi PhiForChart ε hsep W 
                                 rfl
}

variable (𝕜 r U) 

def ModelGrassmannian := modelWithCornersSelf 𝕜 ((Fin r → 𝕜) →L[𝕜] U) 

variable {𝕜 r U}


noncomputable def instSmoothManifoldGrassmannian : 
@SmoothManifoldWithCorners 𝕜 _ _ _ _ _ _ (ModelGrassmannian 𝕜 U r) (Grassmannian 𝕜 E r) _
(instChartedSpaceGrassmannian ε hsep):= 
@smoothManifoldWithCorners_of_contDiffOn _ _ _ _ _ _ _ (ModelGrassmannian 𝕜 U r) (Grassmannian 𝕜 E r) _
(instChartedSpaceGrassmannian ε hsep)
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



end Grassmannian 
