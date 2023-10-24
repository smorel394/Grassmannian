import Mathlib.Tactic
import Mathlib.LinearAlgebra.ProjectiveSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Grassmannian.Grassmannian 
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.FiniteDimension


open Classical
noncomputable section 


section NoTopology 

variable {r : ℕ} {𝕜 E U : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U]

namespace Grassmannian

/- We define what will be charts on Grassmannian 𝕜 E r. The charts are indexed by linear equivalences
φ : E ≃ₗ[𝕜] U × (Fin r → 𝕜), the model of each chart is ((Fin r → 𝕜) →ₗ[𝕜] U). The source of the chart is
the set of r-dimensional subspaces W such that φ.2 induces an isomorphism W ≃ (Fin r → 𝕜), or equivalently
such that W intersects Ker φ.1 trivially; we call this the Goodset of φ.1; its image is all of the codomain.
To have a chart defined at each point, we will need to assume that there exists a linear equivalence between E and 
(Fin r → 𝕜) × U, but we do that later.-/

/- Definition of the sources and lemmas about it.-/



def Goodset (φ : E →ₗ[𝕜] (Fin r → 𝕜)) : Set (Grassmannian 𝕜 E r) :=
{W : Grassmannian 𝕜 E r | W.1 ⊓ (LinearMap.ker φ) = ⊥}

lemma GoodsetPreimage_iff_equiv (φ : E →ₗ[𝕜] (Fin r → 𝕜)) (v : Fin r → E)  :
LinearIndependent 𝕜 (φ ∘ v) ↔ Function.Bijective (LinearMap.domRestrict φ 
(Submodule.span 𝕜 (Set.range v))) := by 
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

lemma GoodsetPreimage (φ : E →ₗ[𝕜] Fin r → 𝕜) {v : Fin r → E} (hv : LinearIndependent 𝕜 v) :
Grassmannian.mk 𝕜 v hv ∈ Goodset φ ↔ LinearIndependent 𝕜 (φ ∘ v) := by
  rw [Goodset]
  simp only [ge_iff_le, Set.mem_setOf_eq]
  rw [Grassmannian.mk_apply, ←disjoint_iff]
  exact ⟨fun h => LinearIndependent.map hv h, fun h => Submodule.range_ker_disjoint h⟩

lemma GoodsetPreimage_unit (φ : E →ₗ[𝕜] (Fin r → 𝕜)) (v : Fin r → E)  :
LinearIndependent 𝕜 (φ ∘ v) ↔ 
IsUnit (φ.comp (Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v)) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot]
  have heq : φ.comp (Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v) = 
    (Finsupp.total (Fin r) (Fin r → 𝕜) 𝕜 (φ ∘ v)).comp
    (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin r)).symm.toLinearMap := by
    apply LinearMap.ext 
    intro u
    simp only [LinearMap.coe_comp, Function.comp_apply, Basis.constr_apply_fintype, Pi.basisFun_equivFun,
      LinearEquiv.refl_apply, map_sum, map_smul, LinearEquiv.coe_coe]
    rw [Finsupp.total_eq_fintype_total_apply (S := ℤ) (R := 𝕜), Fintype.total_apply]
    rfl
  rw [heq, LinearMap.ker_eq_bot, LinearMap.coe_comp]
  rw [Function.Injective.of_comp_iff', ←LinearMap.ker_eq_bot]
  rfl
  apply LinearEquiv.bijective  


lemma Goodset_iff_equiv (φ : E →ₗ[𝕜] (Fin r → 𝕜)) (W : Grassmannian 𝕜 E r) :
W ∈ Goodset φ ↔ Function.Bijective (LinearMap.domRestrict φ W.1) := by
  rw [←Grassmannian.mk_rep W, GoodsetPreimage, GoodsetPreimage_iff_equiv] 
  rfl



/- Definition of the charts.-/

def ChartAux (φ : E →ₗ[𝕜] Fin r → 𝕜) (W : Grassmannian 𝕜 E r) : (Fin r → 𝕜) →ₗ[𝕜] W.1 := by 
  by_cases hW : W ∈ Goodset φ
  . rw [Goodset_iff_equiv] at hW 
    exact (LinearEquiv.ofBijective (φ.domRestrict W.1) hW).symm.toLinearMap 
  . exact 0 

def Chart (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (W : Grassmannian 𝕜 E r) : ((Fin r → 𝕜) →ₗ[𝕜] U) := 
((LinearMap.snd 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap).comp ((Submodule.subtype W.1).comp 
      (ChartAux ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap) W))
  

/- We lift the chart to a map on (Fin r → E).-/

variable (𝕜)

def LinearMapToSpan (v : Fin r → E) : (Fin r → 𝕜) →ₗ[𝕜] Submodule.span 𝕜 (Set.range v) := by
  refine LinearMap.codRestrict (Submodule.span 𝕜 (Set.range v)) (Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v) ?_
  rw [←(Basis.constr_range (Pi.basisFun 𝕜 (Fin r)) ℤ )]
  simp only [Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply, LinearMap.mem_range,
    exists_apply_eq_apply, forall_const]

variable {𝕜}

lemma LinearMapToSpan_vs_Basis.constr (v : Fin r → E) :
(Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v) = LinearMap.comp
(Submodule.subtype (Submodule.span 𝕜 (Set.range v))) (LinearMapToSpan 𝕜 v) := by
  unfold LinearMapToSpan
  simp only [LinearMap.subtype_comp_codRestrict]

lemma LinearMapToSpan.bijective_iff (v : Fin r → E) : 
Function.Bijective (LinearMapToSpan 𝕜 v) ↔ LinearIndependent 𝕜 v := by
  have heq : Function.Bijective (LinearMapToSpan 𝕜 v) ↔ Function.Injective (LinearMapToSpan 𝕜 v) := by
    change _ ∧_ ↔ _ 
    simp only [and_iff_left_iff_imp] 
    intro _ 
    intro ⟨v, hv⟩ 
    rw [←(Basis.constr_range (Pi.basisFun 𝕜 (Fin r)) ℤ)] at hv
    unfold LinearMapToSpan 
    simp only [LinearMap.mem_range] at hv
    obtain ⟨a, ha⟩ := hv
    existsi a 
    rw [←SetCoe.ext_iff, LinearMap.codRestrict_apply]
    exact ha    
  rw [heq, ←LinearMap.ker_eq_bot]
  unfold LinearMapToSpan
  rw [LinearMap.ker_codRestrict, Fintype.linearIndependent_iff] 
  constructor 
  . intro h f hf
    have hker : f ∈ LinearMap.ker (Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ v) := by
      simp only [LinearMap.mem_ker, Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply]
      exact hf 
    rw [h] at hker 
    simp only [Submodule.mem_bot] at hker  
    rw [hker]
    simp only [Pi.zero_apply, implies_true]
  . intro h 
    ext f 
    simp only [LinearMap.mem_ker, Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
      Submodule.mem_bot]
    constructor 
    . intro hker 
      ext i 
      simp only [Pi.zero_apply]
      exact h f hker i
    . exact fun h => by rw [h]; simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    
    
def ChartAuxLift (φ : E →ₗ[𝕜] Fin r → 𝕜) (v : Fin r → E) : 
(Fin r → 𝕜) →ₗ[𝕜] Submodule.span 𝕜 (Set.range v) := by
  by_cases hgood : LinearIndependent 𝕜 (φ ∘ v) 
  . have hv : LinearIndependent 𝕜 v := LinearIndependent.of_comp φ hgood 
    rw [←(GoodsetPreimage (hv := hv)), Goodset_iff_equiv] at hgood
    have hbij : Function.Bijective (((LinearMap.domRestrict φ (Grassmannian.mk 𝕜 v hv).1)).comp 
      (LinearMapToSpan 𝕜 v)) := by
      rw [LinearMap.coe_comp]
      exact Function.Bijective.comp hgood ((LinearMapToSpan.bijective_iff v).mpr hv)
    exact (LinearMapToSpan 𝕜 v).comp (LinearEquiv.ofBijective _ hbij).symm.toLinearMap  
  . exact 0 

lemma ChartAuxLift.isLift (φ : E →ₗ[𝕜] Fin r → 𝕜) {v : Fin r → E} 
(hv : LinearIndependent 𝕜 v) :
ChartAux φ (Grassmannian.mk 𝕜 v hv) = ChartAuxLift φ v := by
  unfold ChartAux ChartAuxLift
  by_cases hgood : Grassmannian.mk 𝕜 v hv ∈ Goodset φ
  . simp only [hgood, dite_true]
    rw [GoodsetPreimage] at hgood
    simp only [hgood, dite_true]
    apply LinearMap.coe_injective  
    erw [LinearMap.coe_comp (LinearMapToSpan 𝕜 v)]
    erw [LinearEquiv.eq_comp_symm, LinearEquiv.symm_comp_eq]
    ext u 
    simp only [LinearEquiv.ofBijective_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.domRestrict_apply]
    rfl 
  . simp only [hgood, dite_false]
    rw [GoodsetPreimage] at hgood
    simp only [hgood, dite_false]


def ChartLiftAux (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U)  (v : Fin r → E) : ((Fin r → 𝕜) →ₗ[𝕜] E) :=
(Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v).comp 
(Ring.inverse (LinearMap.comp ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap) 
(Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v)))


def ChartLift (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U)  (v : Fin r → E) : ((Fin r → 𝕜) →ₗ[𝕜] U) := 
  ((LinearMap.snd 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap).comp 
  ((Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v).comp 
(Ring.inverse (LinearMap.comp ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap) 
(Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ  v))))

lemma ChartLift_vs_ChartAuxLift(φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U)  (v : Fin r → E) :
ChartLift φ v = ((LinearMap.snd 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap).comp
((Submodule.subtype (Submodule.span 𝕜 (Set.range v))).comp 
(ChartAuxLift (((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)) v)) := by
  set φ₁ := (LinearMap.comp (LinearMap.fst 𝕜 (Fin r → 𝕜) U) φ.toLinearMap) with h1def 
  unfold ChartLift
  apply congrArg 
  unfold ChartAuxLift 
  by_cases hgood : LinearIndependent 𝕜 ((((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)) ∘ v)
  . simp only [LinearMap.coe_comp, LinearEquiv.coe_coe] at hgood 
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, hgood, dite_true]
    have hgood' := hgood
    erw [GoodsetPreimage_unit (((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap))] at hgood 
    rw [LinearMapToSpan_vs_Basis.constr, LinearMap.comp_assoc]
    apply congrArg 
    have hinj : Function.Injective (LinearMap.comp (LinearMap.comp (LinearMap.fst 𝕜 (Fin r → 𝕜) U) φ.toLinearMap)
      (Submodule.subtype (Submodule.span 𝕜 (Set.range v)))) := by
      erw [GoodsetPreimage_iff_equiv (((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap))] at hgood' 
      exact hgood'.1 
    rw [←(LinearMap.cancel_left hinj)]
    simp_rw [←h1def]
    rw [LinearMap.comp_assoc, ←(LinearMap.comp_assoc _ (LinearMapToSpan 𝕜 v)), ←LinearMapToSpan_vs_Basis.constr]
    change (LinearMap.comp φ₁ ((Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ) v)) * 
              (Ring.inverse (LinearMap.comp φ₁ ((Basis.constr (Pi.basisFun 𝕜 (Fin r)) ℤ) v))) = _ 
    rw [Ring.mul_inverse_cancel _ hgood]
    rw [←LinearMap.comp_assoc]
    apply LinearMap.coe_injective
    rw [LinearMap.coe_comp]
    erw [LinearEquiv.eq_comp_symm]
    ext u
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.ofBijective_apply,
      LinearMap.domRestrict_apply, LinearMap.fst_apply, LinearMap.one_apply, Submodule.coeSubtype]
    rfl
  . simp only [LinearMap.coe_comp, LinearEquiv.coe_coe] at hgood  
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, hgood, dite_false, LinearMap.comp_zero]
    erw [GoodsetPreimage_unit (((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap))] at hgood 
    rw [Ring.inverse_non_unit _ hgood] 
    simp only [LinearMap.comp_zero]


lemma ChartLift_isLift (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) {v : Fin r → E} (hv : LinearIndependent 𝕜 v) :
Chart φ (Grassmannian.mk 𝕜 v hv) = ChartLift φ v := by
  rw [ChartLift_vs_ChartAuxLift, ←ChartAuxLift.isLift]
  rfl 



/- Definition of the inverse chart.-/


def InverseChart (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) : ((Fin r → 𝕜) →ₗ[𝕜] U) → Grassmannian 𝕜 E r := by 
  intro f 
  refine ⟨Submodule.map φ.symm (LinearMap.graph f), ?_⟩
  unfold Grassmannian
  simp only [Set.mem_setOf_eq]
  constructor
  . letI := LinearEquiv.finiteDimensional (LinearMap.graph_equiv_fst f).symm 
    apply Module.Finite.map 
  . erw [LinearEquiv.finrank_map_eq φ.symm]
    rw [LinearEquiv.finrank_eq (LinearMap.graph_equiv_fst f)]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]

lemma InverseChart_codomainGoodset (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) :
InverseChart φ f ∈ Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap) := by
  rw [Goodset_iff_equiv]
  unfold InverseChart
  simp only
  erw [LinearMap.coe_comp]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Submodule.coeSubtype]
  rw [Set.bijective_iff_bijOn_univ]
  apply Set.BijOn.comp (t := Submodule.map (LinearEquiv.symm φ) (LinearMap.graph f))
  . apply Set.BijOn.comp (t := LinearMap.graph f)
    . apply Set.BijOn.mk
      . apply Set.mapsTo_univ
      . rw [Set.injOn_iff_injective]
        exact LinearMap.graph_fst_injective f         
      . rw [Set.surjOn_iff_surjective]
        exact LinearMap.graph_fst_surjective f                 
    . simp only [Submodule.map_coe]
      apply Equiv.bijOn' φ.toEquiv 
      . simp only [LinearEquiv.coe_toEquiv, Set.maps_image_to]
        intro u
        simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Function.comp_apply, LinearEquiv.apply_symm_apply,
          imp_self]
      . simp only [LinearEquiv.coe_toEquiv_symm]
        intro u
        simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_image, Prod.exists, exists_eq_left]
        intro hu
        existsi u.1 
        rw [←hu]
        simp only [Prod.mk.eta]
        rfl
  . constructor 
    . simp only [Submodule.map_coe, Set.maps_univ_to, Set.mem_image, SetLike.mem_coe, LinearMap.mem_graph_iff,
      Prod.exists, exists_eq_left, Subtype.forall, Submodule.mem_map, forall_exists_index, forall_apply_eq_imp_iff',
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, forall_const]
    . rw [and_iff_right Set.injOn_subtype_val]
      have heq : Submodule.map (LinearEquiv.symm φ) (LinearMap.graph f) = (fun (x : Submodule.map 
        (LinearEquiv.symm φ) (LinearMap.graph f)) => x.1) '' Set.univ := by
        simp only [Submodule.map_coe, Set.image_univ, Subtype.range_coe_subtype, Submodule.mem_map,
          LinearMap.mem_graph_iff, Prod.exists, exists_eq_left]
        ext u
        simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_graph_iff, Prod.exists, exists_eq_left,
          Set.mem_setOf_eq]
      rw [heq]
      apply Set.surjOn_image 

def InverseChartLift (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) : Fin r → E :=
φ.symm ∘ (LinearMap.prod LinearMap.id f) ∘ (fun i => (Pi.basisFun 𝕜 (Fin r)) i)

lemma InverseChartLift_codomain (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) :
LinearIndependent 𝕜 (((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap) ∘ (InverseChartLift φ f)) := by
  unfold InverseChartLift
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  rw [←Function.comp.assoc, Function.comp.assoc _ φ _]
  rw [Fintype.linearIndependent_iff]
  intro a
  simp only [Function.comp_apply, LinearEquiv.apply_symm_apply, LinearMap.fst_apply]
  intro ha i 
  apply_fun (fun h => h i) at ha 
  simp only [Finset.sum_apply, Pi.smul_apply, ne_eq, smul_eq_mul, Pi.zero_apply] at ha  
  rw [←(Finset.sum_subset (s₁ := {i}))] at ha 
  . simp only [Pi.basisFun_apply, LinearMap.prod_apply, Pi.prod, LinearMap.id_coe, id_eq, LinearMap.stdBasis_apply',
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_singleton, ite_true] at ha  
    exact ha 
  . simp only [Finset.subset_univ]
  . intro j _ hj 
    simp only [Finset.mem_singleton] at hj 
    simp only [Pi.basisFun_apply, LinearMap.prod_apply, Pi.prod, LinearMap.id_coe, id_eq, LinearMap.stdBasis_apply',
      mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    simp only [hj, IsEmpty.forall_iff]

lemma InverseChartLift_codomain' (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) :
LinearIndependent 𝕜 (InverseChartLift φ f) := 
LinearIndependent.of_comp _ (InverseChartLift_codomain φ f)

lemma InverseChartLift_isLift (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) :
InverseChart φ f = Grassmannian.mk 𝕜 (InverseChartLift φ f) (InverseChartLift_codomain' φ f) := by
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

lemma InverseChartChart_aux1 (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) {x : Grassmannian 𝕜 E r}
(hx : x ∈ Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)) {u : E} (hu : u ∈ x.1) :
(Chart φ x) (φ u).1 = (φ u).2 := by
  unfold Chart
  simp only [hx, dite_true, LinearMap.coe_comp, LinearEquiv.coe_coe, Submodule.coeSubtype, Function.comp_apply,
    LinearMap.snd_apply]
  have heq : (φ u).1 = ((LinearMap.fst 𝕜 _ _).comp φ.toLinearMap).domRestrict x.1 ⟨u, hu⟩ := by
    simp only [LinearMap.domRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.fst_apply]
  unfold ChartAux 
  simp only [hx, dite_true, LinearMap.domRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.fst_apply]
  rw [←LinearEquiv.invFun_eq_symm]
  rw [heq]
  erw [LinearEquiv.left_inv]
 

lemma InverseChartChart_aux2 (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) {x : Grassmannian 𝕜 E r}
(hx : x ∈ Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)) :
Submodule.map φ x.1 = LinearMap.graph (Chart φ x) := by
  letI := LinearEquiv.finiteDimensional (LinearMap.graph_equiv_fst (Chart φ x)).symm
  apply FiniteDimensional.eq_of_le_of_finrank_eq
  . intro u 
    simp only [Submodule.mem_map, LinearMap.mem_graph_iff, forall_exists_index, and_imp] 
    intro v hvx hvu 
    rw [←hvu]
    apply Eq.symm
    exact InverseChartChart_aux1 φ hx hvx
  . erw [LinearEquiv.finrank_map_eq φ]
    rw [LinearEquiv.finrank_eq (LinearMap.graph_equiv_fst (Chart φ x)), x.2.2]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]


lemma InverseChartChart (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) {x : Grassmannian 𝕜 E r} 
(hx : x ∈ Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)) :
InverseChart φ (Chart φ x) = x := by
  unfold InverseChart 
  simp_rw [←(InverseChartChart_aux2 φ hx)]
  ext u
  simp only [Submodule.mem_map, exists_exists_and_eq_and, LinearEquiv.symm_apply_apply, exists_eq_right]
   

lemma ChartInverseChart_aux (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) {u : E}
(hu : u ∈ φ.symm '' (LinearMap.graph f)) :
(φ u).2 = f (φ u).1 := by
  rw [LinearEquiv.image_symm_eq_preimage] at hu
  simp only [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_graph_iff] at hu 
  exact hu

lemma ChartInverseChart (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) :
Chart φ (InverseChart φ f) = f := by
  unfold Chart ChartAux 
  simp only [InverseChart_codomainGoodset, dite_true]
  apply LinearMap.ext 
  intro v 
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Submodule.coeSubtype, Function.comp_apply, LinearMap.snd_apply]
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
      simp only [LinearMap.domRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.fst_apply, LinearEquiv.ofBijective_apply]
    nth_rewrite 1 [heq]
    erw [←LinearEquiv.toFun_eq_coe]
    ext v 
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm,
      Function.comp_apply, LinearEquiv.apply_symm_apply]   
  . change _ ∈ Submodule.map φ.symm (LinearMap.graph f)
    unfold InverseChart
    simp only [SetLike.coe_mem]

/- Definition of the chart as LocalEquiv.-/

def Chart_LocalEquiv (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) : LocalEquiv (Grassmannian 𝕜 E r) ((Fin r → 𝕜) →ₗ[𝕜] U) :=
{
  toFun := Chart φ
  invFun := InverseChart φ 
  source := Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)
  target := ⊤
  map_source' := by tauto 
  map_target' := fun f _ => InverseChart_codomainGoodset φ f
  left_inv' := fun _ hW  => InverseChartChart φ hW  
  right_inv' := fun f _ => ChartInverseChart φ f   
}

end Grassmannian
end NoTopology

