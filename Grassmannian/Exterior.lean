import Mathlib.Tactic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.TensorPower
import Grassmannian.Lemmas 


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

lemma ExteriorAlgebra.ιMulti_range : Set.range (ExteriorAlgebra.ιMulti R n) ⊆ 
(ExteriorAlgebra.GradedPiece R M n : Set (ExteriorAlgebra R M)) := by
  rw [Set.range_subset_iff]
  intro v
  rw [ExteriorAlgebra.ιMulti_apply]
  apply Submodule.pow_subset_pow
  rw [Set.mem_pow]
  existsi fun i => ⟨(ExteriorAlgebra.ι R) (v i), by simp only [SetLike.mem_coe, LinearMap.mem_range, ι_inj,
    exists_eq]⟩
  simp only 

def ExteriorAlgebra.ιMulti_fixedDegree : AlternatingMap R M (ExteriorAlgebra.GradedPiece R M n) (Fin n) := by
  apply AlternatingMap.codRestrict (ExteriorAlgebra.ιMulti R n) (ExteriorAlgebra.GradedPiece R M n)
    (fun _ => ExteriorAlgebra.ιMulti_range R n (by simp only [Set.mem_range, exists_apply_eq_apply]))
 

@[simp] lemma ExteriorAlgebra.ιMulti_fixedDegree_apply (a : Fin n → M) :
ExteriorAlgebra.ιMulti_fixedDegree R n a = ExteriorAlgebra.ιMulti R n a := by
  unfold ExteriorAlgebra.ιMulti_fixedDegree 
  simp only [AlternatingMap.codRestrict_apply_coe]


lemma ExteriorAlgebra.ιMulti_span_range : 
Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R n)) = 
ExteriorAlgebra.GradedPiece R M n := by 
  apply le_antisymm
  . rw [Submodule.span_le]
    apply le_trans (ExteriorAlgebra.ιMulti_range R n) (le_refl _)
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


noncomputable def ExteriorAlgebra.ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) :
{s : Finset I // Finset.card s = n} → ExteriorAlgebra R M := by
  intro ⟨s, hs⟩
  have e := Finset.orderIsoOfFin s hs 
  exact ExteriorAlgebra.ιMulti R n (fun i => v (e i))

noncomputable def ExteriorAlgebra.ιMulti_fixedDegree_family {I : Type*} [LinearOrder I] (v : I → M) :
{s : Finset I // Finset.card s = n} → ExteriorAlgebra.GradedPiece R M n := 
fun ⟨s, hs⟩ => ExteriorAlgebra.ιMulti_fixedDegree R n (fun i => v (Finset.orderIsoOfFin s hs i))

lemma ExteriorAlgebra.ιMulti_family_coe {I : Type*} [LinearOrder I] (v : I → M) :
ExteriorAlgebra.ιMulti_family R n v = (Submodule.subtype _) ∘ (ExteriorAlgebra.ιMulti_fixedDegree_family R n v) := by
  ext s 
  unfold ExteriorAlgebra.ιMulti_fixedDegree_family
  simp only [Submodule.coeSubtype, Finset.coe_orderIsoOfFin_apply, Function.comp_apply, ιMulti_fixedDegree_apply]
  rfl

lemma ExteriorAlgebra.GradedPiece.span_of_span {I : Type*} [LinearOrder I] 
{v : I → M} (hv : Submodule.span R (Set.range v) = ⊤) : 
Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) = ExteriorAlgebra.GradedPiece R M n := by
  apply le_antisymm
  . rw [Submodule.span_le, Set.range_subset_iff]
    intro s 
    unfold ExteriorAlgebra.ιMulti_family
    simp only [Finset.coe_orderIsoOfFin_apply, SetLike.mem_coe]
    apply (ExteriorAlgebra.ιMulti_range R n) 
    simp only [Set.mem_range, exists_apply_eq_apply]
  . change (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n) ≤ _ 
    rw [LinearMap.range_eq_map, ←hv, Submodule.map_span, Submodule.span_pow, Submodule.span_le]
    intro u hu
    rw [Set.mem_pow] at hu
    obtain ⟨f, hf⟩ := hu
    set g : Fin n → M := fun i => ExteriorAlgebra.ιInv (f i).1
    have hfg : ∀ (i : Fin n), (f i).1 = ExteriorAlgebra.ι R (g i) := by
      intro i
      have h : (f i).1 ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M)) := by 
        have h' := (f i).2
        simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and] at h' 
        obtain ⟨i, hi⟩ := h'
        simp only [LinearMap.mem_range]
        existsi v i 
        exact hi 
      rw [LinearMap.mem_range] at h 
      obtain ⟨v, hv⟩ := h
      simp only 
      rw [←hv, ExteriorAlgebra.ι_inj]
      erw [ExteriorAlgebra.ι_leftInverse] 
    have hg : ∀ (i : Fin n), ∃ (j : I), g i = v j := by
      intro i
      have h := (f i).2
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and] at h  
      obtain ⟨j, hj⟩ := h
      rw [hfg i, ExteriorAlgebra.ι_inj] at hj
      existsi j
      rw [hj]
    have heq : u = ExteriorAlgebra.ιMulti R n g := by
      rw [ExteriorAlgebra.ιMulti_apply, ←hf]
      apply congrArg; apply congrArg
      ext i
      exact hfg i 
    rw [heq]
    set α : Fin n → I := fun i => Classical.choose (hg i)
    set αprop := fun i => Classical.choose_spec (hg i)
    by_cases hinj : Function.Injective α 
    . set s := Finset.image α Finset.univ  
      set h : Fin n → s := fun i => ⟨α i, by simp only [Finset.mem_image, Finset.mem_univ, true_and,
        exists_apply_eq_apply]⟩
      have hbij : Function.Bijective h := by
        constructor
        . intro i j hij
          rw [Subtype.mk.injEq] at hij 
          exact hinj hij 
        . intro ⟨i, hi⟩
          rw [Finset.mem_image] at hi
          obtain ⟨a, ha⟩ := hi
          existsi a 
          simp only [Subtype.mk.injEq]
          exact ha.2
      have hs : Finset.card s = n := by
        suffices h : Fintype.card s = n
        . rw [←h]; simp only [Finset.mem_image, Finset.mem_univ, true_and, Fintype.card_coe]
        . rw [←(Fintype.card_of_bijective hbij)]
          simp only [Fintype.card_fin]
      set e := Finset.orderIsoOfFin s hs 
      set g' : Fin n → M := fun i => v (e i)
      have hg' : ExteriorAlgebra.ιMulti R n g' ∈ Submodule.span R (Set.range (ιMulti_family R n v)) := by
        apply Submodule.subset_span
        rw [Set.mem_range]
        existsi ⟨s, hs⟩
        unfold ExteriorAlgebra.ιMulti_family
        simp only [Finset.coe_orderIsoOfFin_apply]
      set σ : Equiv.Perm (Fin n) := (Equiv.ofBijective h hbij).trans e.toEquiv.symm 
      have hgg' : g = g' ∘ σ := by
        ext i 
        rw [Function.comp_apply, Equiv.trans_apply]
        change g i = v (e (_))
        erw [Equiv.apply_symm_apply e.toEquiv (Equiv.ofBijective h hbij i)] 
        simp only [Equiv.ofBijective_apply]
        exact αprop i 
      rw [hgg', AlternatingMap.map_perm]
      exact Submodule.smul_mem _ _ hg' 
    . change ¬(∀ (a b : Fin n), _) at hinj 
      push_neg at hinj
      obtain ⟨i, j, hij1, hij2⟩ := hinj 
      have heq : g = Function.update g i (g j) := by
        ext k 
        by_cases hk : k = i 
        . rw [Function.update_apply]
          simp only [hk, ite_true]
          change g i = g j 
          rw [αprop i, αprop j]
          change v (α i) = v (α j)
          rw [hij1]
        . simp only [ne_eq, hk, not_false_eq_true, Function.update_noteq] 
      rw [heq, AlternatingMap.map_update_self _ _ hij2]
      simp only [SetLike.mem_coe, Submodule.zero_mem]


lemma ExteriorAlgebra.GradedPiece.span_of_span' {I : Type*} [LinearOrder I] 
{v : I → M} (hv : Submodule.span R (Set.range v) = ⊤) : 
Submodule.span R  (Set.range (ExteriorAlgebra.ιMulti_fixedDegree_family R n v)) = ⊤ := by
  rw [eq_top_iff]
  intro ⟨u, hu⟩ _ 
  set hu' := hu
  rw [←(ExteriorAlgebra.GradedPiece.span_of_span R n hv), ExteriorAlgebra.ιMulti_family_coe,
    Set.range_comp, ←Submodule.map_span, Submodule.mem_map] at hu'
  obtain ⟨v, hv, huv⟩ := hu'
  have heq : ⟨u, hu⟩ = v := by
    rw [←SetCoe.ext_iff]
    simp only
    simp only [Submodule.coeSubtype] at huv 
    exact (Eq.symm huv)  
  rw [heq]
  exact hv 

variable (M)

noncomputable def ExteriorAlgebra.GradedPiece.toTensor : ExteriorAlgebra.GradedPiece R M n →ₗ[R]
TensorPower R n M := ExteriorAlgebra.GradedPiece.liftAlternatingEquiv R n 
(MultilinearMap.alternatization (PiTensorProduct.tprod R (s := fun (_ : Fin n) => M)))

variable {M}

lemma ExteriorAlgebra.GradedPiece.toTensor_apply_ιMulti (v : Fin n → M) :
ExteriorAlgebra.GradedPiece.toTensor R M n (ExteriorAlgebra.ιMulti_fixedDegree R n v) =
Finset.sum Finset.univ (fun (σ : Equiv.Perm (Fin n)) => Equiv.Perm.sign σ • 
(PiTensorProduct.tprod R (fun i => v (σ i)))) := by
  unfold ExteriorAlgebra.GradedPiece.toTensor 
  simp only [liftAlternatingEquiv_apply, liftAlternating_apply_ιMulti] 
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply]

lemma ExteriorAlgebra.GradedPiece.toTensor_apply_ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) 
{s : Finset I} (hs : Finset.card s = n) :
ExteriorAlgebra.GradedPiece.toTensor R M n (ExteriorAlgebra.ιMulti_fixedDegree_family R n v ⟨s, hs⟩) =
Finset.sum Finset.univ (fun (σ : Equiv.Perm (Fin n)) => Equiv.Perm.sign σ • 
(PiTensorProduct.tprod R (fun i => v (Finset.orderIsoOfFin s hs (σ i))))) := by
  unfold ExteriorAlgebra.ιMulti_fixedDegree_family
  simp only [Finset.coe_orderIsoOfFin_apply]
  rw [ExteriorAlgebra.GradedPiece.toTensor_apply_ιMulti]

noncomputable def TensorPower.linearForm {I : Type*} [LinearOrder I] (b : Basis I R M)
{s : Finset I} (hs : Finset.card s = n) : TensorPower R n M →ₗ[R] R := by
  apply PiTensorProduct.lift.toFun 
  exact MultilinearMap.compLinearMap (MultilinearMap.mkPiRing R (Fin n) 1) 
    (fun i => b.coord (Finset.orderIsoOfFin s hs i))

lemma TensorPower.linearForm_apply_tprod {I : Type*} [LinearOrder I] (b : Basis I R M)
{s : Finset I} (hs : Finset.card s = n) (v : Fin n → M) :
TensorPower.linearForm R n b hs (PiTensorProduct.tprod R v) = 
Finset.prod Finset.univ (fun i => b.coord (Finset.orderIsoOfFin s hs i) (v i)) := by
  unfold TensorPower.linearForm 
  simp only [Finset.coe_orderIsoOfFin_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, Basis.coord_apply, MultilinearMap.mkPiRing_apply,
    smul_eq_mul, _root_.mul_one]


lemma TensorPower.linearForm_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
{s : Finset I} (hs : Finset.card s = n) : 
TensorPower.linearForm R n b hs (ExteriorAlgebra.GradedPiece.toTensor R M n
(ExteriorAlgebra.ιMulti_fixedDegree_family R n b ⟨s, hs⟩)) = 1 := by
  rw [ExteriorAlgebra.GradedPiece.toTensor_apply_ιMulti_family, map_sum]
  have hzero : ∀ (σ : Equiv.Perm (Fin n)), σ ∈ Finset.univ → ¬σ ∈ ({Equiv.refl (Fin n)} : 
    Finset (Equiv.Perm (Fin n))) → TensorPower.linearForm R n b hs 
    (Equiv.Perm.sign σ • ⨂ₜ[R] (i : Fin n), b ((Finset.orderIsoOfFin s hs) (σ i))) = 0 := by
    intro σ _ hσ
    simp only [Finset.mem_singleton] at hσ 
    erw [LinearMap.map_smul]
    apply smul_eq_zero_of_right
    rw [TensorPower.linearForm_apply_tprod]
    have h : ∃ (i : Fin n), ¬ σ i = i := by
      by_contra habs 
      push_neg at habs 
      apply hσ
      ext i 
      simp only [Equiv.refl_apply]
      rw [habs i]
    obtain ⟨i, hi⟩ := h  
    apply Finset.prod_eq_zero (a := i) (Finset.mem_univ _)
    rw [Basis.coord_apply, Basis.repr_self_apply]
    simp only [Finset.coe_orderIsoOfFin_apply, OrderEmbedding.eq_iff_eq, ite_eq_right_iff]
    simp only [hi, IsEmpty.forall_iff]
  have heq := Finset.sum_subset (s₁ := {Equiv.refl (Fin n)}) (Finset.subset_univ _) hzero 
  rw [←heq]
  simp only [Finset.coe_orderIsoOfFin_apply, LinearMap.map_smul_of_tower, Finset.sum_singleton, Equiv.Perm.sign_refl,
    Equiv.refl_apply, one_smul]
  rw [TensorPower.linearForm_apply_tprod]
  apply Finset.prod_eq_one 
  intro i _ 
  simp only [Finset.coe_orderIsoOfFin_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]

 
lemma TensorPower.linearForm_apply_nondiag_aux {I : Type*} [LinearOrder I] 
{s t : Finset I} (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) (σ : Equiv.Perm (Fin n)) : 
∃ (i : Fin n), (Finset.orderIsoOfFin s hs i).1 ≠ (Finset.orderIsoOfFin t ht (σ i)).1 := by 
  by_contra habs
  push_neg at habs
  apply hst 
  apply Finset.eq_of_subset_of_card_le 
  . intro a has
    set b := Finset.orderIsoOfFin t ht (σ ((Finset.orderIsoOfFin s hs).symm ⟨a, has⟩)) 
    have heq : a = b.1 := by
      rw [←habs]
      simp only [OrderIso.apply_symm_apply]
    rw [heq]
    exact b.2
  . rw [hs, ht]


lemma TensorPower.linearForm_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
{s t : Finset I} (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) : 
TensorPower.linearForm R n b hs (ExteriorAlgebra.GradedPiece.toTensor R M n
(ExteriorAlgebra.ιMulti_fixedDegree_family R n b ⟨t, ht⟩)) = 0 := by
  rw [ExteriorAlgebra.GradedPiece.toTensor_apply_ιMulti_family, map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  erw [LinearMap.map_smul]
  apply smul_eq_zero_of_right
  rw [TensorPower.linearForm_apply_tprod]
  obtain ⟨i, hi⟩ := TensorPower.linearForm_apply_nondiag_aux n hs ht hst σ 
  apply Finset.prod_eq_zero (a := i) (Finset.mem_univ _) 
  rw [Basis.coord_apply, Basis.repr_self_apply]
  simp only [Finset.coe_orderIsoOfFin_apply, ne_eq] at hi  
  simp only [Finset.coe_orderIsoOfFin_apply, Ne.symm hi, ite_false]


noncomputable def ExteriorAlgebra.GradedPiece.basis {I : Type*} [LinearOrder I] (b : Basis I R M) :
Basis {s : Finset I // Finset.card s = n} R (ExteriorAlgebra.GradedPiece R M n) := by
  apply Basis.mk (v := ExteriorAlgebra.ιMulti_fixedDegree_family R n b)
  . apply LinearIndependent.of_comp (ExteriorAlgebra.GradedPiece.toTensor R M n)
    apply linearIndependent_of_dualFamily R _
      (fun s => TensorPower.linearForm R n b s.2) 
    . intro ⟨s, hs⟩ ⟨t, ht⟩ hst 
      simp only [ne_eq, Subtype.mk.injEq] at hst   
      simp only [Function.comp_apply]
      apply TensorPower.linearForm_apply_nondiag
      exact hst 
    . intro ⟨s, hs⟩
      simp only [Function.comp_apply]
      apply TensorPower.linearForm_apply_diag 
  . rw [ExteriorAlgebra.GradedPiece.span_of_span']
    rw [Basis.span_eq]


