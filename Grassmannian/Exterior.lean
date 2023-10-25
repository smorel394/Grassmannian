import Mathlib.Tactic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating



variable (R M N N' : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] 
  [AddCommGroup N'] [Module R N'] (n : ℕ)

abbrev ExteriorAlgebra.GradedPiece := (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n) 

def ExteriorAlgebra.GradedPiece.Finite [Module.Finite R M]: Module.Finite R 
(ExteriorAlgebra.GradedPiece R M n) := by
  apply Module.Finite.mk 
  rw [Submodule.fg_top]
  apply Submodule.FG.pow 
  rw [LinearMap.range_eq_map]
  apply Submodule.FG.map 
  rw [←Module.finite_def]
  exact inferInstance 

variable {R M N N'}

def ExteriorAlgebra.GradedPiece.liftAlternating_aux : (AlternatingMap R M N (Fin n)) →ₗ[R] 
((i : ℕ) → AlternatingMap R M N (Fin i)) := by
  apply LinearMap.pi
  intro i
  by_cases h : i = n 
  . rw [h]; exact LinearMap.id 
  . exact 0 


def ExteriorAlgebra.GradedPiece.liftAlternating : (AlternatingMap R M N (Fin n)) →ₗ[R] 
ExteriorAlgebra.GradedPiece R M n →ₗ[R] N := by
  set F := LinearMap.comp (ExteriorAlgebra.liftAlternating (R := R) (M := M) (N :=N)) 
    (ExteriorAlgebra.GradedPiece.liftAlternating_aux n)
  exact {toFun := fun f => LinearMap.domRestrict (F f) (ExteriorAlgebra.GradedPiece R M n)
         map_add' := by intro f g 
                        simp only [map_add, LinearMap.coe_comp, Function.comp_apply]
                        ext u 
                        simp only [LinearMap.domRestrict_apply, LinearMap.add_apply]
         map_smul' := by intro a f 
                         simp only [map_smul, LinearMap.coe_comp, Function.comp_apply, RingHom.id_apply]
                         ext u 
                         simp only [LinearMap.domRestrict_apply, LinearMap.smul_apply]
         }

variable (R)

def ExteriorAlgebra.ιMulti_fixedDegree : AlternatingMap R M (ExteriorAlgebra.GradedPiece R M n) (Fin n) := by
  apply AlternatingMap.codRestrict (ExteriorAlgebra.ιMulti R n) (ExteriorAlgebra.GradedPiece R M n)
  intro a
  rw [ExteriorAlgebra.ιMulti_apply]
  apply Submodule.pow_subset_pow
  rw [Set.mem_pow]
  existsi fun i => ⟨(ExteriorAlgebra.ι R) (a i), by simp only [SetLike.mem_coe, LinearMap.mem_range, ι_inj,
    exists_eq]⟩
  simp only

@[simp] lemma ExteriorAlgebra.ιMulti_fixedDegree_apply (a : Fin n → M) :
ExteriorAlgebra.ιMulti_fixedDegree R n a = ExteriorAlgebra.ιMulti R n a := by
  unfold ExteriorAlgebra.ιMulti_fixedDegree 
  simp only [AlternatingMap.codRestrict_apply_coe]


lemma ExteriorAlgebra.ιMulti_span_range : 
Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R n)) = 
ExteriorAlgebra.GradedPiece R M n := by 
  apply le_antisymm
  . rw [Submodule.span_le]
    intro u 
    simp only [Set.mem_range, SetLike.mem_coe, forall_exists_index]
    intro a hau
    apply Submodule.pow_subset_pow
    rw [Set.mem_pow, ←hau, ExteriorAlgebra.ιMulti_apply]
    existsi fun i => ⟨ExteriorAlgebra.ι R (a i), by simp only [SetLike.mem_coe, LinearMap.mem_range, ι_inj,
      exists_eq]⟩
    simp only
  . change (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n) ≤ _ 
    rw [Submodule.pow_eq_span_pow_set, Submodule.span_le]
    intro u hu
    apply Submodule.subset_span 
    simp only [Set.mem_range]
    rw [Set.mem_pow] at hu
    obtain ⟨f, hfu⟩ := hu 
    rw [←hfu]
    existsi fun i => ExteriorAlgebra.ιInv (f i).1  
    rw [ExteriorAlgebra.ιMulti_apply]
    apply congrArg; apply congrArg
    ext i 
    have h : (f i).1 ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M)) := by simp only [SetLike.coe_mem]
    rw [LinearMap.mem_range] at h 
    obtain ⟨v, hv⟩ := h 
    rw [←hv, ExteriorAlgebra.ι_inj]
    erw [ExteriorAlgebra.ι_leftInverse]
    


lemma ExteriorAlgebra.ιMulti_fixedDegree_span_range : 
Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_fixedDegree R n)) = 
(⊤ : Submodule R (ExteriorAlgebra.GradedPiece R M n)) := by 
  apply LinearMap.map_injective (Submodule.ker_subtype (ExteriorAlgebra.GradedPiece R M n))
  rw [LinearMap.map_span, ←Set.image_univ, Set.image_image]
  simp only [Submodule.coeSubtype, ιMulti_fixedDegree_apply, Set.image_univ, Submodule.map_top, Submodule.range_subtype]
  exact ExteriorAlgebra.ιMulti_span_range R n 

@[ext]
lemma ExteriorAlgebra.GradedPiece.lhom_ext ⦃f : ExteriorAlgebra.GradedPiece R M n →ₗ[R] N⦄
⦃g : ExteriorAlgebra.GradedPiece R M n →ₗ[R] N⦄ 
(heq : (LinearMap.compAlternatingMap f) (ExteriorAlgebra.ιMulti_fixedDegree R n) = 
(LinearMap.compAlternatingMap g) (ExteriorAlgebra.ιMulti_fixedDegree R n)) : f = g := by
  ext u
  have hu : u ∈ (⊤ : Submodule R (ExteriorAlgebra.GradedPiece R M n)) := Submodule.mem_top   
  rw [←ExteriorAlgebra.ιMulti_fixedDegree_span_range] at hu
  apply Submodule.span_induction hu (p := fun u => f u = g u)
  . intro _ h
    rw [Set.mem_range] at h
    obtain ⟨a, ha⟩ := h
    apply_fun (fun F => F a) at heq; simp only [LinearMap.compAlternatingMap_apply] at heq 
    rw [←ha, heq]
  . rw [LinearMap.map_zero, LinearMap.map_zero]
  . exact fun _ _ h h' => by rw [LinearMap.map_add, LinearMap.map_add, h, h']
  . exact fun _ _ h => by rw [LinearMap.map_smul, LinearMap.map_smul, h] 


/- Useless ? 
lemma ExteriorAlgebra.ιMulti_fixedDegree_submodule : LinearMap.compAlternatingMap 
(Submodule.subtype (ExteriorAlgebra.GradedPiece R M n))
(ExteriorAlgebra.ιMulti_fixedDegree R n) = ExteriorAlgebra.ιMulti R n := by
  ext a 
  simp only [LinearMap.compAlternatingMap_apply, Submodule.coeSubtype]
  rw [ExteriorAlgebra.ιMulti_fixedDegree_apply]
-/

@[simp] lemma ExteriorAlgebra.GradedPiece.liftAlternating_apply_ιMulti (f : AlternatingMap R M N (Fin n)) 
(a : Fin n → M) :
ExteriorAlgebra.GradedPiece.liftAlternating n f (ExteriorAlgebra.ιMulti_fixedDegree R n a) = f a := by
  unfold ExteriorAlgebra.GradedPiece.liftAlternating 
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.domRestrict_apply]
  rw [ExteriorAlgebra.ιMulti_fixedDegree_apply, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  unfold ExteriorAlgebra.GradedPiece.liftAlternating_aux
  simp only [eq_mpr_eq_cast, LinearMap.pi_apply, cast_eq, dite_eq_ite, ite_true, LinearMap.id_coe, id_eq]

/- Useless ?
@[simp] lemma ExteriorAlgebra.GradedPiece.liftAlternating_apply_ιMulti_other {i : ℕ} (hi : i ≠ n)
(f : AlternatingMap R M N (Fin n)) (a : Fin i → M) :
ExteriorAlgebra.liftAlternating (ExteriorAlgebra.GradedPiece.liftAlternating_aux n f) 
(ExteriorAlgebra.ιMulti_fixedDegree R i a) = 0 := by 
  unfold ExteriorAlgebra.GradedPiece.liftAlternating_aux
  simp only [eq_mpr_eq_cast, ιMulti_fixedDegree_apply, ExteriorAlgebra.liftAlternating_apply_ιMulti, LinearMap.pi_apply,
    hi, dite_false, LinearMap.zero_apply, AlternatingMap.zero_apply] 
-/

@[simp] lemma ExteriorAlgebra.GradedPiece.liftAlternating_comp_ιMulti (f : AlternatingMap R M N (Fin n)) :
(LinearMap.compAlternatingMap (ExteriorAlgebra.GradedPiece.liftAlternating n f)) 
(ExteriorAlgebra.ιMulti_fixedDegree R n) = f := by
  ext a
  simp only [LinearMap.compAlternatingMap_apply]
  rw [ExteriorAlgebra.GradedPiece.liftAlternating_apply_ιMulti]

/- Useless ?
@[simp] lemma ExteriorAlgebra.GradedPiece.liftAlternating_comp_ιMulti_other {i : ℕ} (hi : i ≠ n)
(f : AlternatingMap R M N (Fin n)) : LinearMap.compAlternatingMap
(ExteriorAlgebra.liftAlternating (ExteriorAlgebra.GradedPiece.liftAlternating_aux n f)) 
(ExteriorAlgebra.ιMulti R i) = 0 := by sorry
-/

@[simp] lemma ExteriorAlgebra.GradedPiece.liftAlternating_ιMulti :
ExteriorAlgebra.GradedPiece.liftAlternating n (R := R) (M := M) (ExteriorAlgebra.ιMulti_fixedDegree R n) = LinearMap.id := by
  ext u 
  simp only [liftAlternating_comp_ιMulti, ιMulti_fixedDegree_apply, LinearMap.compAlternatingMap_apply,
    LinearMap.id_coe, id_eq]

  
@[simp]
lemma ExteriorAlgebra.GradedPiece.liftAlternating_comp (g : N →ₗ[R] N') (f : AlternatingMap R M N (Fin n)) :
ExteriorAlgebra.GradedPiece.liftAlternating n (LinearMap.compAlternatingMap g f) =   
LinearMap.comp g (ExteriorAlgebra.GradedPiece.liftAlternating n f) := by
  ext u
  simp only [liftAlternating_comp_ιMulti, LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    liftAlternating_apply_ιMulti]

@[simps apply symm_apply]
def ExteriorAlgebra.GradedPiece.liftAlternatingEquiv :
AlternatingMap R M N (Fin n) ≃ₗ[R] ExteriorAlgebra.GradedPiece R M n →ₗ[R] N where
toFun := ExteriorAlgebra.GradedPiece.liftAlternating n 
map_add' := map_add _ 
map_smul' := map_smul _ 
invFun F := F.compAlternatingMap (ExteriorAlgebra.ιMulti_fixedDegree R n)
left_inv f := ExteriorAlgebra.GradedPiece.liftAlternating_comp_ιMulti R n f 
right_inv F := by ext u; simp only [liftAlternating_comp, liftAlternating_ιMulti, LinearMap.comp_id]

