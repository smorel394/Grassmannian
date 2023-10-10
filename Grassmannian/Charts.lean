import Mathlib.Tactic
import Mathlib.LinearAlgebra.ProjectiveSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Grassmannian.Grassmannian 
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.FiniteDimension


open Classical
noncomputable section 


/- Note: if my changes to mathlib are accepted, change the NontriviallyNormedField 𝕜 to 
NontriviallyNormedDivisionRing 𝕜 We will also need to introduce a NontriviallyNormedField over which
𝕜 is an algebra and E and U are NormedSpaces.-/
/-variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]
[NormedAddCommGroup U] [Module 𝕜 U] [BoundedSMul 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}-/

variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}


namespace Grassmannian

/- We define what will be charts on Grassmannian 𝕜 E r. The charts are indexed by continuous linear equivalences
φ : E ≃L[𝕜] U × (Fin r → 𝕜), the model of each chart is ((Fin r → 𝕜) →L[𝕜] U). The source of the chart is
the set of r-dimensional subspaces W such that φ.2 induces an isomorphism W ≃ (Fin r → 𝕜), or equivalently
such that W intersects Ker φ.1 trivially; we call this the Goodset of φ.1; its image is all of the codomain.
To have a chart defined at each point, we will need to assume that there exists a continuous linear equivalence 
between E and (Fin r → 𝕜) × U, but we do that later.-/


/- Definition of the sources and lemmas about it.-/

def Goodset (φ : E →ₗ[𝕜] (Fin r → 𝕜)) : Set (Grassmannian 𝕜 E r) :=
{W : Grassmannian 𝕜 E r | W.1 ⊓ (LinearMap.ker φ) = ⊥}

lemma GoodsetPreimage_iff_equiv (φ : E →ₗ[𝕜] (Fin r → 𝕜)) (v : Fin r → E)  :
LinearIndependent 𝕜 (φ ∘ v) ↔ Function.Bijective (LinearMap.domRestrict φ 
(Submodule.span 𝕜 (Set.range v))) := by --sorry
  constructor 
  . intro hv 
    have hker : LinearMap.ker (LinearMap.domRestrict φ (Submodule.span 𝕜 (Set.range v))) = ⊥ := by
      ext ⟨u, hu⟩
      simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_bot]
      constructor 
      . intro h
        rw [←(Basis.constr_range (Pi.basisFun 𝕜 (Fin r)) ℤ ), LinearMap.mem_range] at hu
        obtain ⟨a, ha⟩ := hu
        simp_rw [←ha] at h 
        simp only [Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply, map_sum,
          map_smul] at h  
        rw [Fintype.linearIndependent_iff] at hv 
        simp only [Submodule.mk_eq_zero]
        rw [←ha]
        simp only [Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply]
        apply Finset.sum_eq_zero
        intro i _ 
        rw [hv a h i]
        simp only [zero_smul]
      . exact fun h => by simp only [Submodule.mk_eq_zero] at h; simp only [h, map_zero]
    rw [LinearMap.ker_eq_bot] at hker
    change _ ∧ _ 
    rw [and_iff_right hker]    
    have hv' : LinearIndependent 𝕜 v := LinearIndependent.of_comp _ hv
    have hdim := finrank_span_eq_card hv' 
    simp only [Fintype.card_fin] at hdim  
    letI : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range v)) := by
      apply FiniteDimensional.span_of_finite 
      apply Set.finite_range
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hker 
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hdim 
  . intro hbij
    have hv : LinearIndependent 𝕜 v := by
      rw [linearIndependent_iff_card_eq_finrank_span]
      simp only [Fintype.card_fin]
      change r = FiniteDimensional.finrank 𝕜 _ 
      rw [←(LinearMap.finrank_range_of_inj hbij.1)]
      rw [LinearMap.range_eq_top.mpr hbij.2]
      simp only [finrank_top, FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
    apply LinearIndependent.map hv
    rw [Submodule.disjoint_def]
    intro u huv huφ
    have h : ⟨u, huv⟩ ∈ LinearMap.ker (LinearMap.domRestrict φ (Submodule.span 𝕜 (Set.range v))) := by
      simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply]
      exact huφ
    have hker : LinearMap.ker (LinearMap.domRestrict φ (Submodule.span 𝕜 (Set.range v))) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact hbij.1
    rw [hker] at h
    simp only [Submodule.mem_bot, Submodule.mk_eq_zero] at h  
    exact h 

/-
lemma GoodsetPreimage_iff_equiv' (φ : E →L[𝕜] (Fin r → 𝕜)) (v : Fin r → E)  :
LinearIndependent 𝕜 (φ.toLinearMap ∘ v) ↔ Function.Bijective (φ.comp 
(Submodule.subtypeL (Submodule.span 𝕜 (Set.range v)))) := by 
  have heq : (LinearMap.domRestrict φ.toLinearMap (Submodule.span 𝕜 (Set.range v))) = 
    (φ.comp (Submodule.subtypeL (Submodule.span 𝕜 (Set.range v)))).toLinearMap := by
    ext u
    simp only [LinearMap.domRestrict_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Submodule.coe_subtypeL, LinearMap.coe_comp, Submodule.coeSubtype, Function.comp_apply] 
  change _ ↔ Function.Bijective (φ.comp (Submodule.subtypeL (Submodule.span 𝕜 (Set.range v)))).toLinearMap
  rw [←heq]
  exact GoodsetPreimage_iff_equiv φ.toLinearMap v 
-/

lemma GoodsetPreimage_iff_equiv' (φ : E →L[𝕜] (Fin r → 𝕜)) (v : Fin r → E)  :
LinearIndependent 𝕜 (φ.toLinearMap ∘ v) ↔ Function.Bijective (φ.comp (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v)) := by 
--sorry
  have heq : (φ.comp (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v)).toLinearMap = 
    (φ.toLinearMap.comp (Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v)) := by 
    ext u
    simp only [ContinuousLinearMap.coe_comp, Basis.coe_constrL, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
      LinearMap.coe_single, Function.comp_apply, Basis.constr_apply_fintype, Pi.basisFun_equivFun,
      LinearEquiv.refl_apply, ne_eq]
  change _ ↔ Function.Bijective (φ.comp (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v)).toLinearMap
  rw [heq]
  have hequiv : Function.Bijective (φ.toLinearMap.comp (Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v))
    ↔ Function.Injective (φ.toLinearMap.comp (Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v)) := by
    constructor 
    . exact fun h => h.1
    . exact fun h => ⟨h, LinearMap.surjective_of_injective h⟩ 
  rw [hequiv]
  have heq : φ.toLinearMap.comp (Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v) = 
    (Finsupp.total (Fin r) (Fin r → 𝕜) 𝕜 (φ ∘ v)).comp
    (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin r)).symm.toLinearMap := by
    apply LinearMap.ext 
    intro u
    simp only [LinearMap.coe_comp, Function.comp_apply, Basis.constr_apply_fintype, Pi.basisFun_equivFun,
      LinearEquiv.refl_apply, map_sum, map_smul, LinearEquiv.coe_coe]
    rw [Finsupp.total_eq_fintype_total_apply (S := ℤ) (R := 𝕜), Fintype.total_apply]
    rfl
  rw [heq, LinearMap.coe_comp, Function.Injective.of_comp_iff', ←LinearMap.ker_eq_bot]
  rfl
  apply LinearEquiv.bijective 


lemma GoodsetPreimage (φ : E →ₗ[𝕜] Fin r → 𝕜) {v : Fin r → E} (hv : LinearIndependent 𝕜 v) :
Grassmannian.mk 𝕜 v hv ∈ Goodset φ ↔ LinearIndependent 𝕜 (φ ∘ v) := by --sorry
  rw [Goodset]
  simp only [ge_iff_le, Set.mem_setOf_eq]
  rw [Grassmannian.mk_apply, ←disjoint_iff]
  exact ⟨fun h => LinearIndependent.map hv h, fun h => Submodule.range_ker_disjoint h⟩

lemma GoodsetPreimage_unit (φ : E →L[𝕜] (Fin r → 𝕜)) (v : Fin r → E)  :
LinearIndependent 𝕜 (φ.toLinearMap ∘ v) ↔ 
IsUnit (φ.comp (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v)) := by --sorry
  rw [GoodsetPreimage_iff_equiv']
  letI : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range v)) := by
    apply FiniteDimensional.span_of_finite 
    apply Set.finite_range 
  constructor 
  . intro hbij 
    set e := LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective _ hbij) 
    have heq : φ.comp (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v) = e.toContinuousLinearMap := by
      ext u
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Basis.constrL_apply, Pi.basisFun_equivFun,
        LinearEquiv.refl_apply, ContinuousLinearMap.coe_comp, Basis.coe_constrL, ContinuousLinearEquiv.coe_coe,
        LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.ofBijective_apply, LinearMap.coe_comp,
        ContinuousLinearMap.coe_coe, Basis.constr_apply_fintype]
    rw [heq]
    apply Units.isUnit (ContinuousLinearEquiv.toUnit e)
  . intro hunit
    set e := ContinuousLinearEquiv.ofUnit (IsUnit.unit hunit) 
    have heq : φ.comp (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v) = e.toContinuousLinearMap := by
      ext u
      erw [ContinuousLinearEquiv.unitsEquiv_apply]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Basis.constrL_apply, Pi.basisFun_equivFun,
        LinearEquiv.refl_apply, IsUnit.unit_spec]
    rw [heq]
    exact ContinuousLinearEquiv.bijective e 


lemma Goodset_iff_equiv (φ : E →ₗ[𝕜] (Fin r → 𝕜)) (W : Grassmannian 𝕜 E r) :
W ∈ Goodset φ ↔ Function.Bijective (LinearMap.domRestrict φ W.1) := by --sorry
  rw [←Grassmannian.mk_rep W, GoodsetPreimage, GoodsetPreimage_iff_equiv] 
  rfl


/- The goodset of a continuous linear map φ : E → (Fin r → 𝕜) is open.-/

lemma GoodsetIsOpen_aux1 (φ : E →L[𝕜] (Fin r → 𝕜)) : IsOpen {v : Fin r → E | LinearIndependent 𝕜 (φ ∘ v)} := by --sorry
  have heq : {v : Fin r → E | LinearIndependent 𝕜 (φ ∘ v)} = (fun (v : Fin r → E) => φ ∘ v)⁻¹'
    {u : Fin r → (Fin r → 𝕜) | LinearIndependent 𝕜 u} := by
    simp only [Set.preimage_setOf_eq]
  rw [heq]
  apply IsOpen.preimage
  . apply Pi.continuous_postcomp φ.continuous
  . exact isOpen_setOf_linearIndependent 

lemma GoodsetIsOpen_aux2 (φ : E →L[𝕜] (Fin r → 𝕜)) : IsOpen {v : {v : Fin r → E // LinearIndependent 𝕜 v} 
| LinearIndependent 𝕜 (φ ∘ v.1)} := by --sorry
  have heq : {v : {v : Fin r → E // LinearIndependent 𝕜 v} | LinearIndependent 𝕜 (φ ∘ v.1)} = 
    ({v : Fin r → E | LinearIndependent 𝕜 v}.restrict (fun (v : Fin r → E) => φ ∘ v))⁻¹'
    {u : Fin r → (Fin r → 𝕜) | LinearIndependent 𝕜 u} := by 
    simp only [Set.coe_setOf, Set.preimage_setOf_eq, Set.restrict_apply, Set.mem_setOf_eq]
  rw [heq]
  apply IsOpen.preimage
  . rw [Set.restrict_eq]
    apply Continuous.comp
    . apply Pi.continuous_postcomp φ.continuous 
    . exact continuous_subtype_val
  . exact isOpen_setOf_linearIndependent  


lemma GoodsetIsOpen (φ : E →L[𝕜] (Fin r → 𝕜)) : IsOpen (Goodset (φ : E →ₗ[𝕜] Fin r → 𝕜)) := by --sorry
  rw [isOpen_coinduced]
  have heq : (Grassmannian.mk' 𝕜)⁻¹' (Goodset φ.toLinearMap) = 
    {v : {v : Fin r → E // LinearIndependent 𝕜 v} | LinearIndependent 𝕜 (φ ∘ v.1)} := by
    ext v 
    simp only [Set.mem_preimage, mk'_eq_mk, Set.mem_setOf_eq] 
    exact GoodsetPreimage φ.toLinearMap v.2
  rw [heq]
  exact GoodsetIsOpen_aux2 φ


/- Definition of the charts.-/

def ChartAux (φ : E →L[𝕜] Fin r → 𝕜) (W : Grassmannian 𝕜 E r) : (Fin r → 𝕜) →L[𝕜] W.1 := by 
  by_cases hW : W ∈ Goodset φ
  . rw [Goodset_iff_equiv] at hW 
    letI := W.2.1 
    exact (LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective 
      (φ.domRestrict W.1) hW)).symm.toContinuousLinearMap 
  . exact 0 

def Chart (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) (W : Grassmannian 𝕜 E r) : ((Fin r → 𝕜) →L[𝕜] U) := 
((ContinuousLinearMap.snd 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap).comp ((Submodule.subtypeL W.1).comp 
      (ChartAux ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) W))
  

/- We lift the chart to a map on (Fin r → E).-/

variable (𝕜)

def LinearMapToSpan (v : Fin r → E) : (Fin r → 𝕜) →L[𝕜] Submodule.span 𝕜 (Set.range v) := by
  refine ContinuousLinearMap.codRestrict (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v) (Submodule.span 𝕜 (Set.range v)) ?_
  rw [←(Basis.constr_range (Pi.basisFun 𝕜 (Fin r)) ℤ )]
  intro a 
  rw [Basis.constrL_apply]
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply, LinearMap.mem_range, Basis.constr_apply_fintype,
    exists_apply_eq_apply]

variable {𝕜}

lemma LinearMapToSpan_vs_Basis.constr (v : Fin r → E) :
(Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v) = ContinuousLinearMap.comp
(Submodule.subtypeL (Submodule.span 𝕜 (Set.range v))) (LinearMapToSpan 𝕜 v) := by --sorry
  unfold LinearMapToSpan
  ext a 
  simp only [Basis.constrL_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply, ContinuousLinearMap.coe_comp',
    Submodule.coe_subtypeL', Submodule.coeSubtype, Function.comp_apply, ContinuousLinearMap.coe_codRestrict_apply]


lemma LinearMapToSpan.bijective_iff (v : Fin r → E) : 
Function.Bijective (LinearMapToSpan 𝕜 v) ↔ LinearIndependent 𝕜 v := by --sorry
  have heq : Function.Bijective (LinearMapToSpan 𝕜 v) ↔ Function.Injective (LinearMapToSpan 𝕜 v) := by --sorry
    change _ ∧_ ↔ _ 
    simp only [and_iff_left_iff_imp] 
    intro _ 
    intro ⟨v, hv⟩ 
    rw [←(Basis.constr_range (Pi.basisFun 𝕜 (Fin r)) ℤ)] at hv
    unfold LinearMapToSpan 
    simp only [LinearMap.mem_range] at hv
    obtain ⟨a, ha⟩ := hv
    existsi a 
    rw [←SetCoe.ext_iff, ContinuousLinearMap.coe_codRestrict_apply]
    exact ha    
  rw [heq]
  change Function.Injective (LinearMapToSpan 𝕜 v).toLinearMap ↔ _ 
  rw [←LinearMap.ker_eq_bot]
  unfold LinearMapToSpan
  erw [ContinuousLinearMap.ker_codRestrict]; rw [Fintype.linearIndependent_iff] 
  constructor 
  . intro h f hf
    have hker : f ∈ LinearMap.ker (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v) := by
      simp only [LinearMap.mem_ker, Basis.constrL_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply]
      exact hf 
    rw [h] at hker 
    simp only [Submodule.mem_bot] at hker  
    rw [hker]
    simp only [Pi.zero_apply, implies_true]
  . intro h 
    ext f 
    simp only [LinearMap.mem_ker, Basis.constrL_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply, Submodule.mem_bot]
    constructor 
    . intro hker 
      ext i 
      simp only [Pi.zero_apply]
      exact h f hker i
    . exact fun h => by rw [h]; simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]

    
def ChartAuxLift (φ : E →L[𝕜] Fin r → 𝕜) (v : Fin r → E) : 
(Fin r → 𝕜) →L[𝕜] Submodule.span 𝕜 (Set.range v) := by
  by_cases hgood : LinearIndependent 𝕜 (φ.toLinearMap ∘ v) 
  . have hv : LinearIndependent 𝕜 v := LinearIndependent.of_comp φ.toLinearMap hgood  
    rw [←(GoodsetPreimage (hv := hv)), Goodset_iff_equiv] at hgood
    have hbij : Function.Bijective (((φ.comp (Submodule.subtypeL (Grassmannian.mk 𝕜 v hv).1))).comp 
      (LinearMapToSpan 𝕜 v)) := by
      rw [ContinuousLinearMap.coe_comp']
      exact Function.Bijective.comp hgood ((LinearMapToSpan.bijective_iff v).mpr hv)
    exact (LinearMapToSpan 𝕜 v).comp (LinearEquiv.toContinuousLinearEquiv 
      (LinearEquiv.ofBijective _ hbij)).symm.toContinuousLinearMap  
  . exact 0 


lemma ChartAuxLift.isLift (φ : E →L[𝕜] Fin r → 𝕜) {v : Fin r → E} 
(hv : LinearIndependent 𝕜 v) :
ChartAux φ (Grassmannian.mk 𝕜 v hv) = ChartAuxLift φ v := by --sorry
  unfold ChartAux ChartAuxLift
  by_cases hgood : Grassmannian.mk 𝕜 v hv ∈ Goodset φ
  . simp only [hgood, dite_true]
    rw [GoodsetPreimage] at hgood
    simp only [hgood, dite_true]
    apply ContinuousLinearMap.coe_injective  
    apply LinearMap.coe_injective 
    rw [ContinuousLinearMap.coe_comp (LinearMapToSpan 𝕜 v)]
    erw [LinearMap.coe_comp (LinearMapToSpan 𝕜 v).toLinearMap]
    letI := (Grassmannian.mk 𝕜 v hv).2.1
    rw [LinearEquiv.coe_toContinuousLinearEquiv_symm, LinearEquiv.coe_toContinuousLinearEquiv_symm]
    erw [LinearEquiv.eq_comp_symm, LinearEquiv.symm_comp_eq]
    ext u 
    simp only [LinearEquiv.ofBijective_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.domRestrict_apply]
    rfl 
  . simp only [hgood, dite_false]
    rw [GoodsetPreimage] at hgood
    simp only [hgood, dite_false]

-- Useless ?
/-
def ChartLiftAux (φ : E ≃L[𝕜] (Fin r → 𝕜) × U)  (v : Fin r → E) : ((Fin r → 𝕜) →L[𝕜] E) :=
(Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v).comp 
(Ring.inverse (ContinuousLinearMap.comp ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) 
(Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v)))
-/

def ChartLift (φ : E ≃L[𝕜] (Fin r → 𝕜) × U)  (v : Fin r → E) : ((Fin r → 𝕜) →L[𝕜] U) := 
  ((ContinuousLinearMap.snd 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap).comp 
  ((Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v).comp 
(Ring.inverse (ContinuousLinearMap.comp ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) 
(Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v))))


lemma ChartLift_vs_ChartAuxLift(φ : E ≃L[𝕜] (Fin r → 𝕜) × U)  (v : Fin r → E) :
ChartLift φ v = ((ContinuousLinearMap.snd 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap).comp
((Submodule.subtypeL (Submodule.span 𝕜 (Set.range v))).comp 
(ChartAuxLift (((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap)) v)) := by --sorry
  set φ₁ := (ContinuousLinearMap.comp (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U) φ.toContinuousLinearMap) with h1def 
  unfold ChartLift
  apply congrArg
  rw [LinearMapToSpan_vs_Basis.constr, ContinuousLinearMap.comp_assoc]
  apply congrArg
  by_cases hgood : LinearIndependent 𝕜 (φ₁.toLinearMap ∘ v)
  . have hinj : Function.Injective (ContinuousLinearMap.comp (ContinuousLinearMap.comp 
        (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U) φ.toContinuousLinearMap)
        (Submodule.subtypeL (Submodule.span 𝕜 (Set.range v)))) := by
        erw [GoodsetPreimage_iff_equiv (((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap))] at hgood
        exact hgood.1 
    suffices h : ContinuousLinearMap.comp ((ContinuousLinearMap.comp (ContinuousLinearMap.comp 
        (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U) φ.toContinuousLinearMap)
        (Submodule.subtypeL (Submodule.span 𝕜 (Set.range v))))) (ContinuousLinearMap.comp (LinearMapToSpan 𝕜 v) (Ring.inverse
        (ContinuousLinearMap.comp (ContinuousLinearMap.comp (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U) 
        φ.toContinuousLinearMap) (ContinuousLinearMap.comp (Submodule.subtypeL (Submodule.span 𝕜 (Set.range v))) 
        (LinearMapToSpan 𝕜 v))))) = ContinuousLinearMap.comp ((ContinuousLinearMap.comp (ContinuousLinearMap.comp 
        (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U) φ.toContinuousLinearMap)
        (Submodule.subtypeL (Submodule.span 𝕜 (Set.range v))))) (ChartAuxLift φ₁ v) 
    . ext a 
      apply_fun (fun h => h a) at h 
      rw [ContinuousLinearMap.comp_apply] at h 
      conv at h => rhs 
                   rw [ContinuousLinearMap.comp_apply]
      rw [SetCoe.ext_iff]
      exact hinj h  
    . unfold ChartAuxLift
      simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, LinearMap.coe_comp,
        ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe] at hgood  
      simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, LinearMap.coe_comp,
        ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, hgood, Submodule.coe_subtypeL, dite_true]
      simp_rw [←h1def]
      rw [←ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc φ₁ _ _,
         ←LinearMapToSpan_vs_Basis.constr]
      change (ContinuousLinearMap.comp φ₁ ((Basis.constrL (Pi.basisFun 𝕜 (Fin r))) v)) * 
              (Ring.inverse (ContinuousLinearMap.comp φ₁ ((Basis.constrL (Pi.basisFun 𝕜 (Fin r))) v))) = _
      erw [GoodsetPreimage_unit φ₁] at hgood
      rw [Ring.mul_inverse_cancel _ hgood]
      rw [←ContinuousLinearMap.comp_assoc]
      apply ContinuousLinearMap.coe_injective
      rw [ContinuousLinearMap.coe_comp]
      have heq : (ContinuousLinearMap.comp (ContinuousLinearMap.comp φ₁ (Submodule.subtypeL 
        (Submodule.span 𝕜 (Set.range v)))) (LinearMapToSpan 𝕜 v)).toLinearMap = 
        LinearMap.comp (LinearMap.comp φ₁.toLinearMap (Submodule.subtype (Submodule.span 𝕜 (Set.range v))))
        (LinearMapToSpan 𝕜 v).toLinearMap := by
        ext u
        simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, Submodule.coe_subtypeL,
          LinearMap.coe_comp, ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, Submodule.coeSubtype,
          LinearMap.coe_single, Function.comp_apply, LinearMap.fst_apply]
      simp_rw [heq]
      simp_rw [←h1def]
      apply LinearMap.coe_injective
      rw [LinearMap.coe_comp]
      simp only [ContinuousLinearEquiv.coe_coe, 
        LinearEquiv.coe_toContinuousLinearEquiv_symm, LinearEquiv.coe_coe]
      erw [LinearEquiv.eq_comp_symm]
      ext u
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst,
        LinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.ofBijective_apply,
        Submodule.coeSubtype, LinearMap.fst_apply, ContinuousLinearMap.one_apply]
  . unfold ChartAuxLift
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, LinearMap.coe_comp,
      ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe] at hgood  
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, LinearMap.coe_comp,
      ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, hgood, Submodule.coe_subtypeL, dite_false]
    erw [GoodsetPreimage_unit φ₁] at hgood 
    erw [Ring.inverse_non_unit _ hgood] 
    simp only [ContinuousLinearMap.comp_zero] 


lemma ChartLift_isLift (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) {v : Fin r → E} (hv : LinearIndependent 𝕜 v) :
Chart φ (Grassmannian.mk 𝕜 v hv) = ChartLift φ v := by
  rw [ChartLift_vs_ChartAuxLift, ←ChartAuxLift.isLift]
  rfl 


/- Definition of the inverse chart.-/


def InverseChart (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) : ((Fin r → 𝕜) →L[𝕜] U) → Grassmannian 𝕜 E r := by  
  intro f 
  refine ⟨Submodule.map φ.symm (LinearMap.graph f), ?_⟩
  unfold Grassmannian
  simp only [Set.mem_setOf_eq]
  constructor
  . letI := LinearEquiv.finiteDimensional (LinearMap.graph_equiv_fst f.toLinearMap).symm 
    apply Module.Finite.map 
  . erw [LinearEquiv.finrank_map_eq φ.toLinearEquiv.symm]
    rw [LinearEquiv.finrank_eq (LinearMap.graph_equiv_fst f.toLinearMap)]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]


lemma InverseChart_codomainGoodset (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →L[𝕜] U) :
InverseChart φ f ∈ Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) := by --sorry
  rw [Goodset_iff_equiv]
  unfold InverseChart
  simp only
  erw [LinearMap.coe_comp]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.coe_coe, Submodule.coeSubtype]
  rw [Set.bijective_iff_bijOn_univ]
  apply Set.BijOn.comp (t := Submodule.map (LinearEquiv.symm φ.toLinearEquiv) (LinearMap.graph f.toLinearMap))
  . apply Set.BijOn.comp (t := LinearMap.graph f.toLinearMap)
    . apply Set.BijOn.mk
      . apply Set.mapsTo_univ
      . rw [Set.injOn_iff_injective]
        exact LinearMap.graph_fst_injective f.toLinearMap         
      . rw [Set.surjOn_iff_surjective]
        exact LinearMap.graph_fst_surjective f.toLinearMap                 
    . simp only [Submodule.map_coe]
      apply Equiv.bijOn' φ.toEquiv 
      . simp only [LinearEquiv.coe_toEquiv, ContinuousLinearEquiv.coe_toLinearEquiv, Set.maps_image_to]
        intro u
        simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]
        rw [←LinearEquiv.invFun_eq_symm]
        erw [←LinearEquiv.toFun_eq_coe]
        rw [LinearEquiv.right_inv, imp_self]
        simp only  
      . simp only [LinearEquiv.coe_toEquiv_symm]
        intro u
        simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, ContinuousLinearMap.coe_coe, Set.mem_image, Prod.exists,
          exists_eq_left]
        intro hu
        existsi u.1 
        rw [←hu]
        simp only [Prod.mk.eta]
        rfl
  . constructor 
    . simp only [Submodule.map_coe, Set.maps_univ_to, Set.mem_image, SetLike.mem_coe, LinearMap.mem_graph_iff,
      ContinuousLinearMap.coe_coe, Prod.exists, exists_eq_left, Subtype.forall, Submodule.mem_map, forall_exists_index,
      forall_apply_eq_imp_iff']
      intro a 
      existsi a 
      rfl
    . rw [and_iff_right Set.injOn_subtype_val]
      have heq : Submodule.map (LinearEquiv.symm φ.toLinearEquiv) (LinearMap.graph f.toLinearMap) = 
        (fun (x : Submodule.map (LinearEquiv.symm φ.toLinearEquiv) (LinearMap.graph f.toLinearMap)) => x.1) '' 
        Set.univ := by
        simp only [Submodule.map_coe, Set.image_univ, Subtype.range_coe_subtype, Submodule.mem_map,
          LinearMap.mem_graph_iff, ContinuousLinearMap.coe_coe, Prod.exists, exists_eq_left]
        ext u
        simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_graph_iff, ContinuousLinearMap.coe_coe, Prod.exists,
          exists_eq_left, Set.mem_setOf_eq]
      rw [heq]
      apply Set.surjOn_image 


def InverseChartLift (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →L[𝕜] U) : Fin r → E :=
φ.symm ∘ (ContinuousLinearMap.prod (ContinuousLinearMap.id _ _) f) ∘ (fun i => (Pi.basisFun 𝕜 (Fin r)) i)


lemma InverseChartLift_codomain (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →L[𝕜] U) :
LinearIndependent 𝕜 (((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) ∘ 
(InverseChartLift φ f)) := by --sorry
  unfold InverseChartLift
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst', ContinuousLinearEquiv.coe_coe,
    Pi.basisFun_apply]
  rw [←Function.comp.assoc, Function.comp.assoc _ φ _]
  rw [Fintype.linearIndependent_iff]
  intro a
  simp only [ContinuousLinearEquiv.self_comp_symm, Function.comp.right_id, Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq]
  intro ha i 
  apply_fun (fun h => h i) at ha 
  simp only [Finset.sum_apply, Pi.smul_apply, LinearMap.stdBasis_apply', smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply] at ha   
  exact ha 



lemma InverseChartLift_codomain' (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →L[𝕜] U) :
LinearIndependent 𝕜 (InverseChartLift φ f) := 
LinearIndependent.of_comp _ (InverseChartLift_codomain φ f)


lemma InverseChartLift_isLift (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →L[𝕜] U) :
InverseChart φ f = Grassmannian.mk 𝕜 (InverseChartLift φ f) (InverseChartLift_codomain' φ f) := by --sorry
  unfold InverseChart
  rw [←SetCoe.ext_iff, Grassmannian.mk_apply]
  simp only
  unfold InverseChartLift
  rw [Set.range_comp, Submodule.span_image]
  apply congrArg
  rw [LinearMap.graph_eq_range_prod]
  rw [Set.range_comp, Submodule.span_image, LinearMap.range_eq_map]
  apply congrArg
  rw [Basis.span_eq]



/- We prove that the charts are inverses.-/

lemma InverseChartChart_aux1 (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) {x : Grassmannian 𝕜 E r}
(hx : x ∈ Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap)) {u : E} (hu : u ∈ x.1) :
(Chart φ x) (φ u).1 = (φ u).2 := by --sorry
  unfold Chart ChartAux 
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst] at hx  
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, hx, dite_true, ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe, Submodule.coe_subtypeL', Submodule.coeSubtype,
    Function.comp_apply]
  have heq : (φ u).1 = (((ContinuousLinearMap.fst 𝕜 _ _).comp φ.toContinuousLinearMap).comp 
    (Submodule.subtypeL x.1)) ⟨u, hu⟩ := by
    simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst', ContinuousLinearEquiv.coe_coe,
      Submodule.coe_subtypeL', Submodule.coeSubtype, Function.comp_apply]   
  letI := x.2.1
  rw [LinearEquiv.coe_toContinuousLinearEquiv_symm']
  rw [←LinearEquiv.invFun_eq_symm]
  rw [heq]
  erw [LinearEquiv.left_inv]


lemma InverseChartChart_aux2 (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) {x : Grassmannian 𝕜 E r}
(hx : x ∈ Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap)) :
Submodule.map φ x.1 = LinearMap.graph (Chart φ x).toLinearMap := by --sorry
  letI := LinearEquiv.finiteDimensional (LinearMap.graph_equiv_fst (Chart φ x).toLinearMap).symm
  apply FiniteDimensional.eq_of_le_of_finrank_eq
  . intro u 
    simp only [Submodule.mem_map, LinearMap.mem_graph_iff, ContinuousLinearMap.coe_coe, forall_exists_index, and_imp]
    intro v hvx hvu 
    rw [←hvu]
    apply Eq.symm
    exact InverseChartChart_aux1 φ hx hvx
  . erw [LinearEquiv.finrank_map_eq φ.toLinearEquiv]
    rw [LinearEquiv.finrank_eq (LinearMap.graph_equiv_fst (Chart φ x).toLinearMap), x.2.2]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]


lemma InverseChartChart (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) {x : Grassmannian 𝕜 E r} 
(hx : x ∈ Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap)) :
InverseChart φ (Chart φ x) = x := by --sorry
  unfold InverseChart 
  simp_rw [←(InverseChartChart_aux2 φ hx)]
  ext u
  simp only [Submodule.mem_map, exists_exists_and_eq_and, ContinuousLinearEquiv.symm_apply_apply, exists_eq_right]


lemma ChartInverseChart_aux (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →L[𝕜] U) {u : E}
(hu : u ∈ φ.symm '' (LinearMap.graph f.toLinearMap)) :
(φ u).2 = f (φ u).1 := by --sorry
  rw [ContinuousLinearEquiv.image_symm_eq_preimage] at hu
  simp only [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_graph_iff, ContinuousLinearMap.coe_coe] at hu  
  exact hu


lemma ChartInverseChart (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →L[𝕜] U) :
Chart φ (InverseChart φ f) = f := by --sorry
  unfold Chart ChartAux 
  have h := InverseChart_codomainGoodset φ f
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst] at h  
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, h, dite_true]
  apply ContinuousLinearMap.ext 
  intro v 
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
    Submodule.coe_subtypeL', Submodule.coeSubtype, Function.comp_apply]
  rw [ChartInverseChart_aux φ f]
  . apply congrArg
    change LinearMap.fst 𝕜 _ _ _ = v 
    erw [←(LinearMap.comp_apply (f := LinearMap.fst 𝕜 _ _) (g := φ.toLinearMap))]
    have hf := InverseChart_codomainGoodset φ f
    rw [Goodset_iff_equiv] at hf  
    erw [←(LinearMap.comp_apply (f := LinearMap.comp (LinearMap.fst 𝕜 _ _) φ.toLinearMap) (x := v)
      (g := LinearMap.comp (Submodule.subtype _) (LinearEquiv.symm (LinearEquiv.ofBijective _ hf)).toLinearMap))]
    conv => rhs 
            rw [←(LinearMap.id_apply (R := 𝕜) (M := Fin r → 𝕜) v)]
    apply congrFun
    rw [←LinearMap.comp_assoc]
    change 
      ↑(LinearMap.comp (LinearMap.domRestrict (LinearMap.comp (LinearMap.fst 𝕜 _ _) φ.toLinearMap) (InverseChart φ f).1) 
      (LinearEquiv.symm (LinearEquiv.ofBijective _ hf)).toLinearMap) = fun v => LinearMap.id v 
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] 
    rw [←LinearEquiv.invFun_eq_symm]
    have heq : (LinearMap.domRestrict (LinearMap.comp (LinearMap.fst 𝕜 (Fin r → 𝕜) U) φ.toLinearMap) (InverseChart φ f).1) =
      (LinearEquiv.ofBijective _ hf).toLinearMap := by 
      ext u
      simp only [LinearMap.domRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, Function.comp_apply, LinearMap.fst_apply, ContinuousLinearMap.coe_comp,
        ContinuousLinearMap.coe_fst, LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearEquiv.coe_coe]
    nth_rewrite 1 [heq]
    erw [←LinearEquiv.toFun_eq_coe]
    ext v 
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm,
      Function.comp_apply, LinearEquiv.apply_symm_apply]   
  . change _ ∈ Submodule.map φ.symm (LinearMap.graph f)
    unfold InverseChart
    simp only [SetLike.coe_mem]


/- Definition of the chart as LocalEquiv.-/

def Chart_LocalEquiv (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) : LocalEquiv (Grassmannian 𝕜 E r) ((Fin r → 𝕜) →L[𝕜] U) :=
{
  toFun := Chart φ
  invFun := InverseChart φ 
  source := Goodset ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap)
  target := ⊤
  map_source' := by tauto 
  map_target' := fun f _ => InverseChart_codomainGoodset φ f
  left_inv' := fun _ hW  => InverseChartChart φ hW  
  right_inv' := fun f _ => ChartInverseChart φ f   
}

end Grassmannian


