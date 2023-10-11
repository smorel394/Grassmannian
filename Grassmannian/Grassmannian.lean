import Mathlib.Tactic 
import Grassmannian.Lemmas 
import Mathlib.LinearAlgebra.FiniteDimensional 
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ProjectiveSpace.Independence



noncomputable section 

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
(r : ℕ)

/- First definition of the Grassmannian, as the set of sub-vector spaces of V of
dimension r.-/

def Grassmannian := 
{W : Submodule K V | FiniteDimensional K W ∧ FiniteDimensional.finrank K W = r}

/- Second definition of the Grassmannian, as a quotient.-/

/-- The setoid whose quotient is the projectivization of `V`. -/
def grassmannianSetoid : Setoid { v : Fin r → V // LinearIndependent K v} := 
Setoid.comap (fun v => Submodule.span K (Set.range v.1)) 
⟨(· = ·), eq_equivalence⟩ 

/-- The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred. -/
def QGrassmannian := Quotient (grassmannianSetoid K V r)

variable {V r}

/-- Construct an element of the projectivization from a nonzero vector. -/
def QGrassmannian.mk (v : Fin r → V) (hv : LinearIndependent K v) : QGrassmannian K V r :=
  Quotient.mk'' ⟨v, hv⟩


/-- A variant of `Projectivization.mk` in terms of a subtype. `mk` is preferred. -/
def QGrassmannian.mk' (v : { v : Fin r → V // LinearIndependent K v }) : QGrassmannian K V r :=
  Quotient.mk'' v

@[simp]
theorem QGrassmannian.mk'_eq_mk (v : { v : Fin r → V // LinearIndependent K v}) : 
QGrassmannian.mk' K v = QGrassmannian.mk K v.1 v.2 := rfl

variable {K}

/-- Choose a representative of `v : Projectivization K V` in `V`. -/
protected noncomputable def QGrassmannian.rep (x : QGrassmannian K V r) : Fin r → V :=
  x.out' 


theorem QGrassmannian.rep_linearIndependent (x : QGrassmannian K V r) : 
LinearIndependent K x.rep  :=
  x.out'.2

@[simp]
theorem QGrassmannian.mk_rep (x : QGrassmannian K V r) : 
QGrassmannian.mk K x.rep x.rep_linearIndependent = x := Quotient.out_eq' _

variable (K)

lemma QGrassmannian.mk_eq_mk_iff_span (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ 
Submodule.span K (Set.range v) = Submodule.span K (Set.range w) := by 
  unfold QGrassmannian.mk
  change (Setoid.ker (@Quotient.mk'' _ (grassmannianSetoid K V r))).r _ _  ↔ _ 
  rw [Setoid.ker_mk_eq]
  unfold grassmannianSetoid 
  change Submodule.span K (Set.range v) = _ ↔ _ 
  simp only


def MatrixAction (f : (Fin r → K) →ₗ[K] (Fin r → K)) (v : Fin r → V) : Fin r -> V := 
  (Basis.constr (M' := V) (Pi.basisFun K (Fin r)) ℤ).invFun 
    ((Basis.constr (Pi.basisFun K (Fin r)) ℤ  v).comp f)

lemma MatrixAction_vs_comp (f : (Fin r → K) →ₗ[K] (Fin r → K)) (v w : Fin r → V) :
v = MatrixAction K f w ↔ Basis.constr (Pi.basisFun K (Fin r)) ℤ v = 
  (Basis.constr (Pi.basisFun K (Fin r)) ℤ w).comp f := by 
  unfold MatrixAction
  constructor 
  . intro h 
    rw [h]
    simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply]
  . intro h 
    apply_fun (Basis.constr (M' := V) (Pi.basisFun K (Fin r)) ℤ).invFun at h 
    simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.symm_apply_apply] at h 
    exact h 
    

lemma MatrixAction_id (v : Fin r → V) : MatrixAction K LinearMap.id v = v := by
  unfold MatrixAction
  simp only [LinearMap.comp_id, LinearEquiv.invFun_eq_symm, LinearEquiv.symm_apply_apply]

lemma MatrixAction_mul (f g : (Fin r → K) →ₗ[K] (Fin r → K)) (v : Fin r → V) :
MatrixAction K (f.comp g) v = MatrixAction K g (MatrixAction K f v) := by 
  unfold MatrixAction
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
  apply LinearMap.comp_assoc 

def MatrixAction_inv (f : (Fin r → K) ≃ₗ[K] (Fin r → K)) (v w : Fin r → V) : 
w = MatrixAction K f v ↔ v = MatrixAction K f.symm w := by
  constructor 
  . intro h 
    rw [h, ←MatrixAction_mul]
    simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap]
    rw [MatrixAction_id]
  . intro h 
    rw [h, ←MatrixAction_mul]
    simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap]
    rw [MatrixAction_id]


lemma MatrixAction_apply (f : (Fin r → K) →ₗ[K] (Fin r → K)) (v : Fin r → V) (i : Fin r) :
MatrixAction K f v i = Finset.sum ⊤ (fun j => (f (Pi.basisFun K (Fin r) i) j) • v j) := by
  unfold MatrixAction
  conv => lhs
          rw [←(Basis.constr_basis (Pi.basisFun K (Fin r)) ℤ 
            ((Basis.constr (M' := V) (Pi.basisFun K (Fin r)) ℤ).invFun 
            ((Basis.constr (Pi.basisFun K (Fin r)) ℤ  v).comp f)) i)]
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply, Pi.basisFun_apply, LinearMap.coe_comp,
    Function.comp_apply, Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply, Finset.top_eq_univ]
  

lemma MatrixAction_span (f : (Fin r → K) →ₗ[K] (Fin r → K)) (v : Fin r → V) :
Submodule.span K (Set.range (MatrixAction K f v)) ≤ Submodule.span K (Set.range v) := by 
  rw [Submodule.span_le]
  intro u 
  simp only [Set.mem_range, SetLike.mem_coe, forall_exists_index]
  intro i heq
  rw [←heq, MatrixAction_apply]
  apply Submodule.sum_mem
  intro j _ 
  apply Submodule.smul_mem
  apply Submodule.subset_span
  simp only [Set.mem_range, exists_apply_eq_apply]


lemma MatrixAction_vs_SubmoduleSpan (v w : Fin r → V) :
Submodule.span K (Set.range v) ≤ Submodule.span K (Set.range w) ↔
∃ (f : (Fin r → K) →ₗ[K] (Fin r → K)), v = MatrixAction K f w := by
  constructor 
  . intro h 
    set f := Basis.constr (Pi.basisFun K (Fin r)) ℤ v with hfdef
    set g := Basis.constr (Pi.basisFun K (Fin r)) ℤ w with hgdef
    have hsub : LinearMap.range f ≤ LinearMap.range g := by 
      rw [Basis.constr_range, Basis.constr_range]
      exact h
    set f' := f.codRestrict (LinearMap.range g) 
      (by intro u; apply hsub; simp only [Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
        LinearMap.mem_range, exists_apply_eq_apply])
    set g' := g.rangeRestrict
    have hsur : Function.Surjective g' := by rw [←LinearMap.range_eq_top]; apply LinearMap.range_rangeRestrict
    obtain ⟨h, prop⟩ := Module.projective_lifting_property g' f' hsur 
    existsi h
    simp_rw [MatrixAction_vs_comp]
    rw [←hfdef, ←hgdef]
    have heq : g = (Submodule.subtype (LinearMap.range g)).comp g' := by 
      simp only [LinearMap.subtype_comp_codRestrict]
    rw [heq, LinearMap.comp_assoc, prop]
    simp only [LinearMap.subtype_comp_codRestrict]
  . intro h 
    obtain ⟨f, hf⟩ := h 
    rw [hf]
    apply MatrixAction_span 


lemma MatrixAction_uniqueness {v : Fin r → V} (hv : LinearIndependent K v)
(f g : (Fin r → K) →ₗ[K] (Fin r → K)) (heq : MatrixAction K f v = MatrixAction K g v) :
f = g := by 
  unfold MatrixAction at heq 
  apply_fun (fun h => (Basis.constr (Pi.basisFun K (Fin r)) ℤ) h) at heq
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply] at heq
  have hinj : Function.Injective (Basis.constr (Pi.basisFun K (Fin r)) ℤ v) := by 
    rw [←LinearMap.ker_eq_bot]
    apply Basis.constr_ker 
    exact hv 
  apply LinearMap.ext 
  intro u 
  apply_fun (fun h => h u) at heq
  simp only [LinearMap.coe_comp, Function.comp_apply] at heq
  exact hinj heq   




lemma QGrassmannian.mk_eq_mk_iff_matrixAction (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)), 
w = MatrixAction K f v := by
  rw [QGrassmannian.mk_eq_mk_iff_span]
  constructor 
  . intro heq 
    obtain ⟨f, hf⟩ := (MatrixAction_vs_SubmoduleSpan K v w).mp (le_of_eq heq)
    obtain ⟨g, hg⟩ := (MatrixAction_vs_SubmoduleSpan K w v).mp (le_of_eq (Eq.symm heq))
    have hgf : LinearMap.comp g f = LinearMap.id := by 
      rw [hg, ←MatrixAction_mul] at hf
      conv at hf => lhs
                    rw [←(MatrixAction_id K v)]
      apply Eq.symm
      exact MatrixAction_uniqueness K hv _ _ hf 
    have hfg : LinearMap.comp f g = LinearMap.id := by 
      rw [hf, ←MatrixAction_mul] at hg 
      conv at hg => lhs
                    rw [←(MatrixAction_id K w)]
      apply Eq.symm
      exact MatrixAction_uniqueness K hw _ _ hg 
    existsi LinearEquiv.ofLinear g f hgf hfg 
    exact hg
  . intro h 
    obtain ⟨f, hf⟩ := h
    apply le_antisymm
    . have heq : v = MatrixAction K f.symm.toLinearMap w := by 
        rw [MatrixAction_inv] at hf 
        exact hf 
      rw [heq]
      apply MatrixAction_span 
    . rw [hf]
      apply MatrixAction_span 

lemma QGrassmannian.mk_eq_mk_iff_matrixAction' (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) →ₗ[K] (Fin r → K)), 
w = MatrixAction K f v := by
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction]
  constructor 
  . exact fun h => by obtain ⟨f, hf⟩ := h; existsi f.toLinearMap; exact hf 
  . intro h 
    obtain ⟨f, hf⟩ := h
    have hf' := hf 
    rw [MatrixAction_vs_comp] at hf
    apply_fun (fun f => f.toFun) at hf 
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp] at hf  
    have hinj : Function.Injective f := by
      apply Function.Injective.of_comp (f := (Basis.constr (Pi.basisFun K (Fin r)) ℤ) v)
      rw [←hf, ←LinearMap.ker_eq_bot]
      apply Basis.constr_ker
      exact hw  
    existsi LinearEquiv.ofInjectiveEndo f hinj 
    exact hf' 

lemma QGrassmannian.exists_matrixAction_eq_mk_rep (v : Fin r → V) (hv : LinearIndependent K v) :
∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)), MatrixAction K f v = QGrassmannian.rep (QGrassmannian.mk K v hv) := by
  have heq := Eq.symm (QGrassmannian.mk_rep (QGrassmannian.mk K v hv))
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction] at heq 
  obtain ⟨f, hf⟩ := heq 
  existsi f 
  exact Eq.symm hf 

variable {K}

/-- An induction principle for `QGrassmannian`.
Use as `induction v using QGrassmannian.ind`. -/
@[elab_as_elim]
lemma QGrassmannian.ind {P : QGrassmannian K V r → Prop} (h : ∀ (v : Fin r → V) (h : LinearIndependent K v), 
P (QGrassmannian.mk K v h)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h


/-- Consider an element of the QGrassmannian as a submodule of `V`. -/
protected def QGrassmannian.submodule (x : QGrassmannian K V r) : Submodule K V :=
  (Quotient.liftOn' x fun v => Submodule.span K (Set.range v.1)) <| by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
    exact hvw 

@[simp]
lemma QGrassmannian.submodule_mk (v : Fin r → V) (hv : LinearIndependent K v) : 
(QGrassmannian.mk K v hv).submodule = Submodule.span K (Set.range v) := rfl 

lemma QGrassmannian.submodule_eq (x : QGrassmannian K V r) : x.submodule = Submodule.span K (Set.range x.rep) := by 
  conv_lhs => rw [← x.mk_rep]

instance QGrassmannian.finiteDimensional_submodule (x : QGrassmannian K V r) : FiniteDimensional K x.submodule := by 
  rw [QGrassmannian.submodule_eq]
  apply FiniteDimensional.span_of_finite 
  apply Set.finite_range 

lemma QGrassmannian.finrank_submodule (x : QGrassmannian K V r) : FiniteDimensional.finrank K x.submodule = r := by 
  rw [QGrassmannian.submodule_eq]
  rw [finrank_span_eq_card (QGrassmannian.rep_linearIndependent x)]
  simp only [Fintype.card_fin]


    

variable (K)



/- Comparison of the two definitions.-/

variable (V r)

-- This could probably be optimized now we have QGrassmannian.submodule and its associated lemmas.
def QGrassmannianToGrassmannian : QGrassmannian K V r → Grassmannian K V r := 
fun x => ⟨QGrassmannian.submodule x, ⟨QGrassmannian.finiteDimensional_submodule x, QGrassmannian.finrank_submodule x⟩⟩

lemma QGrassmannianToGrassmannian_apply' {v : Fin r → V} (hv : LinearIndependent K v) :
(QGrassmannianToGrassmannian K V r (QGrassmannian.mk K v hv)).1 = Submodule.span K (Set.range v) := by 
  unfold QGrassmannianToGrassmannian QGrassmannian.mk 
  simp only
  apply QGrassmannian.submodule_mk 


lemma QGrassmannianToGrassmannian_apply (x : QGrassmannian K V r) :
QGrassmannianToGrassmannian K V r x = ⟨Submodule.span K (Set.range x.rep),
⟨FiniteDimensional.span_of_finite K (Set.finite_range x.rep), 
by rw [finrank_span_eq_card (QGrassmannian.rep_linearIndependent x)]; simp only [Fintype.card_fin]⟩⟩ := by
  conv => lhs 
          rw [←(QGrassmannian.mk_rep x)]
  --rw [QGrassmannianToGrassmannian_apply']
  

def GrassmannianToQGrassmannian : Grassmannian K V r → QGrassmannian K V r := by 
  intro ⟨W, hW⟩
  haveI := hW.1 
  set B := FiniteDimensional.finBasisOfFinrankEq K W hW.2 
  refine QGrassmannian.mk K ((Submodule.subtype W) ∘ (FunLike.coe B)) ?_ 
  apply LinearIndependent.map' (Basis.linearIndependent B) _ (Submodule.ker_subtype W)


lemma QGrassmannianToGrassmannianToQGrassmannian (x : QGrassmannian K V r) :
GrassmannianToQGrassmannian K V r (QGrassmannianToGrassmannian K V r x) = x := by
  rw [QGrassmannianToGrassmannian_apply]
  unfold GrassmannianToQGrassmannian
  simp only [Submodule.coeSubtype]
  conv => rhs 
          rw [←(QGrassmannian.mk_rep x)]
  rw [QGrassmannian.mk_eq_mk_iff_span]
  rw [Set.range_comp]
  conv => lhs
          erw [←(LinearMap.map_span (Submodule.subtype _))]
  simp only [Basis.span_eq, Submodule.map_top, Submodule.range_subtype]  

lemma GrassmannianToQGrassmannianToGrassmannian (W : Grassmannian K V r) :
QGrassmannianToGrassmannian K V r (GrassmannianToQGrassmannian K V r W) = W := by
  unfold GrassmannianToQGrassmannian
  simp only [Submodule.coeSubtype]
  rw [←SetCoe.ext_iff, QGrassmannianToGrassmannian_apply', Set.range_comp]
  erw [←(LinearMap.map_span (Submodule.subtype _))]
  simp only [Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
  
noncomputable def QGrassmannianEquivGrassmannian : QGrassmannian K V r ≃ Grassmannian K V r :=
{
  toFun := QGrassmannianToGrassmannian K V r
  invFun := GrassmannianToQGrassmannian K V r 
  left_inv := QGrassmannianToGrassmannianToQGrassmannian K V r 
  right_inv := GrassmannianToQGrassmannianToGrassmannian K V r
}

/- Since we have equivalence, we can define Grassmannian.mk and Grassmannian.rep by composing the QGrassmannian
versions with the equivalence.-/

variable {V r}

def Grassmannian.mk (v : Fin r → V) (hv : LinearIndependent K v) : Grassmannian K V r :=
QGrassmannianEquivGrassmannian K V r (QGrassmannian.mk K v hv)

def Grassmannian.mk' (v : { v : Fin r → V // LinearIndependent K v }) : Grassmannian K V r :=
QGrassmannianEquivGrassmannian K V r (QGrassmannian.mk' K v)
  

@[simp]
theorem Grassmannian.mk'_eq_mk (v : { v : Fin r → V // LinearIndependent K v}) : 
Grassmannian.mk' K v = Grassmannian.mk K v.1 v.2 := rfl

lemma Grassmannian.mk_apply (v : Fin r → V) (hv : LinearIndependent K v) :
(Grassmannian.mk K v hv).1 = Submodule.span K (Set.range v) := by
  unfold Grassmannian.mk 
  erw [QGrassmannianToGrassmannian_apply']

variable {K}

def Grassmannian.rep (x : Grassmannian K V r) : Fin r → V :=
QGrassmannian.rep ((QGrassmannianEquivGrassmannian K V r).symm x)

lemma Grassmannian.rep_linearIndependent (x : Grassmannian K V r) :
LinearIndependent K (Grassmannian.rep x) := 
QGrassmannian.rep_linearIndependent _ 


@[simp]
theorem Grassmannian.mk_rep (x : Grassmannian K V r) : 
Grassmannian.mk K (Grassmannian.rep x) (Grassmannian.rep_linearIndependent x) = x := by 
  unfold Grassmannian.mk Grassmannian.rep 
  rw [QGrassmannian.mk_rep]
  simp only [Equiv.apply_symm_apply]


variable (K)


lemma Grassmannian.mk_eq_mk_iff_span (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
Grassmannian.mk K v hv = Grassmannian.mk K w hw ↔ 
Submodule.span K (Set.range v) = Submodule.span K (Set.range w) := by 
  unfold Grassmannian.mk
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [QGrassmannian.mk_eq_mk_iff_span]


lemma Grassmannian.mk_eq_mk_iff_matrixAction (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
Grassmannian.mk K v hv = Grassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)), 
w = MatrixAction K f v := by 
  unfold Grassmannian.mk
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction]


lemma Grassmannian.mk_eq_mk_iff_matrixAction' (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
Grassmannian.mk K v hv = Grassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) →ₗ[K] (Fin r → K)), 
w = MatrixAction K f v := by
  unfold Grassmannian.mk
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction']

lemma Grassmannian.exists_matrixAction_eq_mk_rep (v : Fin r → V) (hv : LinearIndependent K v) :
∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)), MatrixAction K f v = Grassmannian.rep (Grassmannian.mk K v hv) := by
  unfold Grassmannian.rep Grassmannian.mk
  simp only [Equiv.symm_apply_apply]
  exact QGrassmannian.exists_matrixAction_eq_mk_rep K v hv 

/- The case r = 1.-/
variable {K}

def QGrassmannianToProjectiveSpace (x : QGrassmannian K V 1) : ℙ K V := 
Quotient.liftOn' x (fun v => Projectivization.mk K (v.1 default) (LinearIndependent.ne_zero default v.2)) 
  (by intro ⟨v, hv⟩ ⟨w, hw⟩ hvw
      change Submodule.span K _ = Submodule.span K _ at hvw 
      rw [Set.range_unique, Set.range_unique] at hvw
      simp only [Fin.default_eq_zero] at hvw  
      rw [Submodule.span_singleton_eq_span_singleton] at hvw 
      simp only [Fin.default_eq_zero]
      apply Eq.symm
      exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr hvw 
  )


lemma QGrassmannianToProjectiveSpace_mk (v : Fin 1 → V) (hv : LinearIndependent K v) :
QGrassmannianToProjectiveSpace (QGrassmannian.mk K v hv) = 
Projectivization.mk K (v default) (LinearIndependent.ne_zero default hv) := by
  unfold QGrassmannianToProjectiveSpace QGrassmannian.mk
  simp only [Fin.default_eq_zero, Quotient.liftOn'_mk'']
  


def ProjectiveSpaceToQGrassmannian (x : ℙ K V) : QGrassmannian K V 1 :=
Quotient.liftOn' x (fun v => QGrassmannian.mk K (fun _ => v.1) (linearIndependent_unique (fun _ => v.1) v.2)) 
(by intro ⟨v, hv⟩ ⟨w, hw⟩ hvw 
    rw [QGrassmannian.mk_eq_mk_iff_span]
    change ∃ _, _ at hvw 
    simp only at hvw  
    rw [Set.range_unique]
    simp only [Set.range_const]
    apply Eq.symm
    exact Submodule.span_singleton_eq_span_singleton.mpr hvw  
)
  

lemma ProjectiveSpaceToQGrassmannian_mk (v : V) (hv : v ≠ 0) :
ProjectiveSpaceToQGrassmannian (Projectivization.mk K v hv) = QGrassmannian.mk K (fun _ => v) 
(linearIndependent_unique (fun _ => v) hv) := by
  unfold ProjectiveSpaceToQGrassmannian Projectivization.mk
  simp only [ne_eq, Quotient.liftOn'_mk'']
 

lemma QGrassmannianToProjectiveSpaceToQGrassmannian (x : QGrassmannian K V 1) :
ProjectiveSpaceToQGrassmannian (QGrassmannianToProjectiveSpace x) = x := by
  conv => lhs
          congr
          congr
          rw [←(QGrassmannian.mk_rep x)]
  rw [QGrassmannianToProjectiveSpace_mk, ProjectiveSpaceToQGrassmannian_mk]
  conv => rhs
          rw [←(QGrassmannian.mk_rep x)]
          congr
          rw [eq_const_of_unique (QGrassmannian.rep x)]
  
lemma ProjectiveSpaceToQGrassmannianToProjectiveSpace (x : ℙ K V) :
QGrassmannianToProjectiveSpace (ProjectiveSpaceToQGrassmannian x) = x := by
  conv => lhs
          rw [←(Projectivization.mk_rep x)]
  rw [ProjectiveSpaceToQGrassmannian_mk, QGrassmannianToProjectiveSpace_mk, Projectivization.mk_rep]

def QGrassmannianEquivProjectiveSpace : QGrassmannian K V 1 ≃ ℙ K V :=
{
  toFun := QGrassmannianToProjectiveSpace 
  invFun := ProjectiveSpaceToQGrassmannian
  left_inv := QGrassmannianToProjectiveSpaceToQGrassmannian
  right_inv := ProjectiveSpaceToQGrassmannianToProjectiveSpace
}


variable (r) {V' : Type*} [AddCommGroup V'] [Module K V']

/-- An injective semilinear map of vector spaces induces a map on QGrassmannians. -/
-- Less general than the version for projective spaces because LinearIndependent.map' requires the tV'o rings to be equal.
def QGrassmannian.map (f : V →ₗ[K] V') (hf : Function.Injective f) : QGrassmannian K V r → QGrassmannian K V' r :=
  Quotient.map' (fun v => ⟨f ∘ v.1, by simp only; rw [←LinearMap.ker_eq_bot] at hf; exact LinearIndependent.map' v.2 f hf⟩)
    (by rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
        change Submodule.span K _ = _ at hvw
        change Submodule.span K _ = _
        simp only at hvw ⊢ 
        rw [Set.range_comp, Set.range_comp]
        rw [←LinearMap.map_span, ←LinearMap.map_span]
        rw [hvw])

lemma QGrassmannian.map_mk (f : V →ₗ[K] V') (hf : Function.Injective f) (v : Fin r → V) (hv : LinearIndependent K v) :
    QGrassmannian.map r f hf (mk K v hv) = QGrassmannian.mk K (f ∘ v) 
    (by rw [←LinearMap.ker_eq_bot] at hf; exact LinearIndependent.map' hv f hf) := rfl

/-- The map we have defined is injective. -/
theorem QGrassmannian.map_injective (f : V →ₗ[K] V') (hf : Function.Injective f) : 
Function.Injective (QGrassmannian.map r f hf) := by 
  intro x y hxy 
  induction' x using QGrassmannian.ind with v hv  
  induction' y using QGrassmannian.ind with w hw 
  rw [QGrassmannian.mk_eq_mk_iff_span]
  rw [QGrassmannian.map_mk, QGrassmannian.map_mk, QGrassmannian.mk_eq_mk_iff_span, Set.range_comp, Set.range_comp,
    ←LinearMap.map_span, ←LinearMap.map_span] at hxy 
  apply_fun (fun p => SetLike.coe p) at hxy 
  rw [Submodule.map_coe, Submodule.map_coe] at hxy  
  apply SetLike.coe_injective'  
  exact Function.Injective.image_injective hf hxy 


@[simp]
lemma QGrassmannian.map_id : QGrassmannian.map r (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  ext ⟨v⟩
  rfl


lemma QGrassmannian.map_comp {U : Type*} [AddCommGroup U] [Module K U] (f : V →ₗ[K] V') (hf : Function.Injective f)
    (g : V' →ₗ[K] U) (hg : Function.Injective g) :
    QGrassmannian.map r (g.comp f) (hg.comp hf) = QGrassmannian.map r g hg ∘ QGrassmannian.map r f hf := by 
  ext ⟨v⟩
  rfl 


/- And the versions with Grassmannians.-/


def Grassmannian.map (f : V →ₗ[K] V') (hf : Function.Injective f) : Grassmannian K V r → Grassmannian K V' r := by
  intro W
  refine ⟨Submodule.map f W.1, ?_, ?_⟩
  . letI := W.2.1 
    exact inferInstance 
  . set f' := f.domRestrict W.1 
    have heq : Submodule.map f W = LinearMap.range f' := by
      ext u
      simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.domRestrict_apply, Subtype.exists, exists_prop]  
    have hinj : Function.Injective f' := by
      rw [←LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro u 
      simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply]
      rw [←LinearMap.ker_eq_bot] at hf 
      intro hu 
      change u.1 ∈ LinearMap.ker f at hu 
      rw [hf] at hu 
      simp only [Submodule.mem_bot, ZeroMemClass.coe_eq_zero] at hu  
      exact hu
    rw [heq, LinearMap.finrank_range_of_inj hinj, W.2.2]


lemma Grassmannian.map_apply (f : V →ₗ[K] V') (hf : Function.Injective f) (W : Grassmannian K V r) :
    (Grassmannian.map r f hf W).1 = Submodule.map f W := by
    unfold Grassmannian.map 
    simp only


/-- The map we have defined is injective. -/
theorem Grassmannian.map_injective (f : V →ₗ[K] V') (hf : Function.Injective f) : 
Function.Injective (Grassmannian.map r f hf) := by 
  intro W W' hWW'
  rw [←SetCoe.ext_iff, Grassmannian.map_apply, Grassmannian.map_apply] at hWW'
  apply_fun (fun p => SetLike.coe p) at hWW' 
  rw [Submodule.map_coe, Submodule.map_coe] at hWW' 
  rw [←SetCoe.ext_iff, ←SetLike.coe_set_eq] 
  exact Function.Injective.image_injective hf hWW' 
  

@[simp]
lemma Grassmannian.map_id : Grassmannian.map r (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  apply funext  
  intro W
  rw [id_eq, ←SetCoe.ext_iff, Grassmannian.map_apply, Submodule.map_id]


lemma Grassmannian.map_comp {U : Type*} [AddCommGroup U] [Module K U] (f : V →ₗ[K] V') (hf : Function.Injective f)
    (g : V' →ₗ[K] U) (hg : Function.Injective g) :
    Grassmannian.map r (g.comp f) (hg.comp hf) = Grassmannian.map r g hg ∘ Grassmannian.map r f hf := by 
  apply funext
  intro W 
  rw [Function.comp_apply, ←SetCoe.ext_iff, Grassmannian.map_apply, Grassmannian.map_apply, Grassmannian.map_apply,
    Submodule.map_comp]



/- Nonemptiness of the Grassmannian.-/

lemma NonemptyGrassmannian_iff : Nonempty ({v : Fin r → V // LinearIndependent K v}) ↔ Nonempty (Grassmannian K V r) := by
  rw [←(nonempty_quotient_iff (grassmannianSetoid K V r))] 
  exact Equiv.nonempty_congr (QGrassmannianEquivGrassmannian K V r)

lemma NonemptyGrassmannian_of_finrank (hfinrank : r ≤ FiniteDimensional.finrank K V) : Nonempty (Grassmannian K V r) := by
  by_cases hr : r = 0
  . rw [hr]
    set W : Submodule K V := ⊥
    have hW1 : FiniteDimensional K W := inferInstance 
    have hW2 : FiniteDimensional.finrank K W = 0 := finrank_bot K V
    exact Nonempty.intro ⟨W, hW1, hW2⟩ 
  . rw [←(Nat.succ_pred hr), Nat.succ_le_iff] at hfinrank
    have hrank := Order.succ_le_of_lt (FiniteDimensional.lt_rank_of_lt_finrank hfinrank)
    rw [←Cardinal.nat_succ, Nat.succ_pred hr, le_rank_iff_exists_linearIndependent_finset] at hrank
    obtain ⟨s, hsr, hslin⟩ := hrank
    set v : Fin r → V := fun i => (Finset.equivFinOfCardEq hsr).symm i 
    have hv : LinearIndependent K v := by
      apply LinearIndependent.comp hslin 
      apply Equiv.injective   
    rw [←NonemptyGrassmannian_iff]
    exact Nonempty.intro ⟨v, hv⟩
    



/- Topologies. -/

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]

/-- We equip the QGrassmannian with the "coinduced" topology from the natural map
`mk' : {v : Fin r → E // LinearIndependent 𝕜 v} → QGrassmannanian 𝕜 V r`. -/
instance : TopologicalSpace (QGrassmannian 𝕜 E r) :=
TopologicalSpace.coinduced (QGrassmannian.mk' 𝕜) instTopologicalSpaceSubtype 

/- We equip the Grassmannian with the coinduced topology from the equivalence with the QGrassmannian. Note that this is also
an induced topology, see Equiv.induced_symm and Equiv.coinduced_symm.-/

instance : TopologicalSpace (Grassmannian 𝕜 E r) :=
TopologicalSpace.coinduced (Grassmannian.mk' 𝕜) instTopologicalSpaceSubtype 

end

  