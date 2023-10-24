import Mathlib.Tactic 
import Grassmannian.Lemmas 
import Mathlib.LinearAlgebra.FiniteDimensional 
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ProjectiveSpace.Independence




variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
(I : Type*) [Fintype I] (r : ℕ)

/- First definition of the Grassmannian, as the set of sub-vector spaces of V of
dimension r.-/

def Grassmannian := 
{W : Submodule K V | FiniteDimensional K W ∧ FiniteDimensional.finrank K W = r}

/- Second definition of the Grassmannian, as a quotient. Here we use I to index
the linearly independent families.-/

/-- The setoid whose quotient is the projectivization of `V`. -/
def grassmannianSetoid : Setoid { v : (I → K) →ₗ[K] V // Function.Injective v} := 
Setoid.comap (fun v => LinearMap.range v.1) 
⟨(· = ·), eq_equivalence⟩ 

/-- The I-Grassmannian of the `K`-vector space `V`, as a quotient.-/
def QGrassmannian := Quotient (grassmannianSetoid K V I)

variable {V r I}

/-- Construct an element of the projectivization from a nonzero vector. -/
def QGrassmannian.mk (v : (I → K) →ₗ[K] V) (hv : Function.Injective v) : QGrassmannian K V I :=
  Quotient.mk'' ⟨v, hv⟩


/-- A variant of `Grassmannian.mk` in terms of a subtype. `mk` is preferred. -/
def QGrassmannian.mk' (v : { v : (I → K) →ₗ[K] V // Function.Injective v }) : QGrassmannian K V I :=
  Quotient.mk'' v

@[simp]
theorem QGrassmannian.mk'_eq_mk (v : { v : (I → K) →ₗ[K] V // Function.Injective v}) : 
QGrassmannian.mk' K v = QGrassmannian.mk K v.1 v.2 := rfl

variable {K}

/-- Choose a representative of `v : QGrassmannian K V I` in `V`. -/
protected noncomputable def QGrassmannian.rep (x : QGrassmannian K V I) : (I → K) →ₗ[K] V :=
  x.out' 


theorem QGrassmannian.rep_injective (x : QGrassmannian K V I) : 
Function.Injective x.rep  :=
  x.out'.2

@[simp]
theorem QGrassmannian.mk_rep (x : QGrassmannian K V I) : 
QGrassmannian.mk K x.rep x.rep_injective = x := Quotient.out_eq' _

variable (K)

lemma QGrassmannian.mk_eq_mk_iff_range (v w : (I → K) →ₗ[K] V) (hv : Function.Injective v)
(hw : Function.Injective w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ 
LinearMap.range v = LinearMap.range w := by 
  unfold QGrassmannian.mk
  change (Setoid.ker (@Quotient.mk'' _ (grassmannianSetoid K V I))).r _ _  ↔ _ 
  rw [Setoid.ker_mk_eq]
  unfold grassmannianSetoid 
  change LinearMap.range v = _ ↔ _ 
  simp only


/-
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
-/


lemma QGrassmannian.mk_eq_mk_iff_matrixAction (v w : (I → K) →ₗ[K] V) (hv :  Function.Injective v)
(hw : Function.Injective w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ ∃ (f : (I → K) ≃ₗ[K] (I → K)), 
w = v.comp f.toLinearMap := by
  rw [QGrassmannian.mk_eq_mk_iff_range]
  constructor 
  . intro heq 
    set W := LinearMap.range v 
    set v' := LinearMap.rangeRestrict v 
    have hv' : Function.Bijective v' := by
      constructor 
      . rw [←LinearMap.ker_eq_bot, LinearMap.ker_rangeRestrict, LinearMap.ker_eq_bot]
        exact hv 
      . rw [←LinearMap.range_eq_top]
        exact LinearMap.range_rangeRestrict v 
    set ev := LinearEquiv.ofBijective v' hv' 
    have hvev : v = (Submodule.subtype W).comp ev.toLinearMap := by
      ext a 
      simp only [LinearMap.coe_comp, Submodule.coeSubtype, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.ofBijective_apply, LinearMap.codRestrict_apply]
    set w' := LinearMap.codRestrict W w (by intro u; rw [heq]; exact LinearMap.mem_range_self w u)
    have hw' : Function.Bijective w' := by
      constructor
      . rw [←LinearMap.ker_eq_bot, LinearMap.ker_codRestrict, LinearMap.ker_eq_bot]
        exact hw 
      . rw [←LinearMap.range_eq_top, LinearMap.range_codRestrict, heq, Submodule.comap_subtype_self]
    set ew := LinearEquiv.ofBijective w' hw'
    existsi LinearEquiv.trans ew ev.symm 
    simp_rw [hvev, LinearEquiv.coe_trans, LinearMap.comp_assoc, ←(LinearMap.comp_assoc _ _ 
      (LinearEquiv.ofBijective v' hv').toLinearMap)]
    simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.id_comp]
    ext a
    simp only [LinearMap.coe_comp, Submodule.coeSubtype, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.ofBijective_apply, LinearMap.codRestrict_apply]    
  . exact fun ⟨_, hf⟩ => by rw [hf]; simp only [LinearEquiv.range_comp]
  

lemma QGrassmannian.mk_eq_mk_iff_matrixAction' (v w : (I → K) →ₗ[K] V) (hv : Function.Injective v)
(hw : Function.Injective w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ ∃ (f : (I → K) →ₗ[K] (I → K)), 
w = v.comp f := by
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction]
  constructor 
  . exact fun h => by obtain ⟨f, hf⟩ := h; existsi f.toLinearMap; exact hf 
  . intro h 
    obtain ⟨f, hf⟩ := h 
    apply_fun (fun f => (f : (I → K) → V)) at hf 
    rw [LinearMap.coe_comp] at hf 
    have hinj : Function.Injective f := by
      rw [hf] at hw 
      apply Function.Injective.of_comp hw 
    existsi LinearEquiv.ofInjectiveEndo f hinj 
    change w = v.comp f
    apply LinearMap.coe_injective
    rw [LinearMap.coe_comp] 
    exact hf 


lemma QGrassmannian.exists_matrixAction_eq_mk_rep (v : (I → K) →ₗ[K] V) (hv : Function.Injective v) :
∃ (f : (I → K) ≃ₗ[K] (I → K)), v.comp f.toLinearMap = QGrassmannian.rep (QGrassmannian.mk K v hv) := by
  have heq := Eq.symm (QGrassmannian.mk_rep (QGrassmannian.mk K v hv))
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction] at heq 
  obtain ⟨f, hf⟩ := heq 
  existsi f 
  exact Eq.symm hf 


variable {K}

/-- An induction principle for `QGrassmannian`.
Use as `induction v using QGrassmannian.ind`. -/
@[elab_as_elim]
lemma QGrassmannian.ind {P : QGrassmannian K V I → Prop} (h : ∀ (v : (I → K) →ₗ[K] V) (hv : Function.Injective v), 
P (QGrassmannian.mk K v hv)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h


/-- Map from the Grassmannian to the set of submodules of `V`. -/
protected def QGrassmannian.submodule (v : QGrassmannian K V I) : Submodule K V :=
  (Quotient.liftOn' v fun v => LinearMap.range v.1) <| by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
    exact hvw 


@[simp]
lemma QGrassmannian.submodule_mk (v : (I → K) →ₗ[K] V) (hv : Function.Injective v) : 
(QGrassmannian.mk K v hv).submodule = LinearMap.range v := rfl 

lemma QGrassmannian.submodule_eq (v : QGrassmannian K V I) : v.submodule = LinearMap.range v.rep := by 
  conv_lhs => rw [← v.mk_rep]

instance QGrassmannian.finiteDimensional_submodule (v : QGrassmannian K V I) : FiniteDimensional K v.submodule := by 
  rw [QGrassmannian.submodule_eq]
  apply Module.Finite.range 


lemma QGrassmannian.finrank_submodule (v : QGrassmannian K V I) : 
FiniteDimensional.finrank K v.submodule = Fintype.card I := by 
  rw [QGrassmannian.submodule_eq, LinearMap.finrank_range_of_inj (v.rep_injective)]
  simp only [FiniteDimensional.finrank_fintype_fun_eq_card]
 

variable (K)


/- Comparison of the two definitions.-/

variable (V)
variable (hrI : Fintype.card I = r)

def QGrassmannianToGrassmannian : QGrassmannian K V I → Grassmannian K V r := 
fun x => ⟨QGrassmannian.submodule x, ⟨QGrassmannian.finiteDimensional_submodule x, 
by rw [←hrI]; exact QGrassmannian.finrank_submodule x⟩⟩

lemma QGrassmannianToGrassmannian_apply' {v : (I → K) →ₗ[K] V} (hv : Function.Injective v) :
(QGrassmannianToGrassmannian K V hrI (QGrassmannian.mk K v hv)).1 = LinearMap.range v := by 
  unfold QGrassmannianToGrassmannian QGrassmannian.mk 
  simp only
  apply QGrassmannian.submodule_mk 


lemma QGrassmannianToGrassmannian_apply (x : QGrassmannian K V I) :
QGrassmannianToGrassmannian K V hrI x = ⟨LinearMap.range x.rep,
⟨Module.Finite.range x.rep, 
by rw [←hrI, LinearMap.finrank_range_of_inj x.rep_injective, FiniteDimensional.finrank_fintype_fun_eq_card]⟩⟩ := by
  conv => lhs 
          rw [←(QGrassmannian.mk_rep x)]
  

noncomputable def GrassmannianToQGrassmannian : Grassmannian K V r → QGrassmannian K V I := by 
  intro W
  letI := W.2.1 
  refine QGrassmannian.mk K ((Submodule.subtype W).comp (Basis.equiv (Pi.basisFun K I) 
    (FiniteDimensional.finBasisOfFinrankEq K W W.2.2)
    (Fintype.equivFinOfCardEq hrI)).toLinearMap) ?_ 
  rw [LinearMap.coe_comp, Submodule.coeSubtype]
  apply Function.Injective.comp (Subtype.val_injective) (LinearEquiv.injective _) 


lemma QGrassmannianToGrassmannianToQGrassmannian (x : QGrassmannian K V I) :
GrassmannianToQGrassmannian K V hrI (QGrassmannianToGrassmannian K V hrI x) = x := by
  rw [QGrassmannianToGrassmannian_apply]
  unfold GrassmannianToQGrassmannian
  simp only
  conv => rhs 
          rw [←(QGrassmannian.mk_rep x)]
  rw [QGrassmannian.mk_eq_mk_iff_range]
  rw [LinearMap.range_comp]
  simp only [LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  

lemma GrassmannianToQGrassmannianToGrassmannian (W : Grassmannian K V r) :
QGrassmannianToGrassmannian K V hrI (GrassmannianToQGrassmannian K V hrI W) = W := by
  unfold GrassmannianToQGrassmannian 
  rw [←SetCoe.ext_iff, QGrassmannianToGrassmannian_apply', LinearMap.range_comp]
  simp only [LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  


noncomputable def QGrassmannianEquivGrassmannian : QGrassmannian K V I ≃ Grassmannian K V r :=
{
  toFun := QGrassmannianToGrassmannian K V hrI
  invFun := GrassmannianToQGrassmannian K V hrI 
  left_inv := QGrassmannianToGrassmannianToQGrassmannian K V hrI 
  right_inv := GrassmannianToQGrassmannianToGrassmannian K V hrI
}

/- Since we have an equivalence, we can define Grassmannian.mk and Grassmannian.rep by composing the QGrassmannian
versions with the equivalence.-/

variable {V hrI}


example : r = Fintype.card (Fin r) := by simp only [Fintype.card_fin]

noncomputable def Grassmannian.mk (v : (Fin r → K) →ₗ[K] V) (hv : Function.Injective v) : Grassmannian K V r :=
QGrassmannianEquivGrassmannian K V (Fintype.card_fin r) (QGrassmannian.mk K v hv)


noncomputable def Grassmannian.mk' (v : { v : (Fin r → K) →ₗ[K] V // Function.Injective v}) : Grassmannian K V r :=
QGrassmannianEquivGrassmannian K V (Fintype.card_fin r) (QGrassmannian.mk' K v)
  
@[simp]
theorem Grassmannian.mk'_eq_mk (v : { v : (Fin r → K) →ₗ[K] V // Function.Injective v}) : 
Grassmannian.mk' K v = Grassmannian.mk K v.1 v.2 := rfl

lemma Grassmannian.mk_apply (v : (Fin r → K) →ₗ[K] V) (hv : Function.Injective v) :
(Grassmannian.mk K v hv).1 = LinearMap.range v := by
  unfold Grassmannian.mk 
  erw [QGrassmannianToGrassmannian_apply']
  simp only [Fintype.card_fin]

variable {K}

noncomputable def Grassmannian.rep (x : Grassmannian K V r) : (Fin r → K) →ₗ[K] V :=
QGrassmannian.rep ((QGrassmannianEquivGrassmannian K V (Fintype.card_fin r)).symm x)

lemma Grassmannian.rep_linearIndependent (x : Grassmannian K V r) :
Function.Injective (Grassmannian.rep x) := 
QGrassmannian.rep_injective _ 


@[simp]
theorem Grassmannian.mk_rep (x : Grassmannian K V r) : 
Grassmannian.mk K (Grassmannian.rep x) (Grassmannian.rep_linearIndependent x) = x := by 
  unfold Grassmannian.mk Grassmannian.rep 
  rw [QGrassmannian.mk_rep]
  simp only [Equiv.apply_symm_apply]


variable (K)


lemma Grassmannian.mk_eq_mk_iff_range (v w : (Fin r → K) →ₗ[K] V) (hv : Function.Injective v)
(hw : Function.Injective w) :
Grassmannian.mk K v hv = Grassmannian.mk K w hw ↔ 
LinearMap.range v = LinearMap.range w := by 
  unfold Grassmannian.mk
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [QGrassmannian.mk_eq_mk_iff_range]


lemma Grassmannian.mk_eq_mk_iff_matrixAction (v w : (Fin r → K) →ₗ[K] V) (hv : Function.Injective v)
(hw : Function.Injective w) :
Grassmannian.mk K v hv = Grassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)), 
w = v.comp f.toLinearMap := by 
  unfold Grassmannian.mk
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction]


lemma Grassmannian.mk_eq_mk_iff_matrixAction' (v w : (Fin r → K) →ₗ[K] V) (hv : Function.Injective v)
(hw : Function.Injective w) :
Grassmannian.mk K v hv = Grassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) →ₗ[K] (Fin r → K)), 
w = v.comp f := by
  unfold Grassmannian.mk
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction']

lemma Grassmannian.exists_matrixAction_eq_mk_rep (v : (Fin r → K) →ₗ[K] V) (hv : Function.Injective v) :
∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)), v.comp f.toLinearMap = Grassmannian.rep (Grassmannian.mk K v hv) := by
  unfold Grassmannian.rep Grassmannian.mk
  simp only [Equiv.symm_apply_apply]
  exact QGrassmannian.exists_matrixAction_eq_mk_rep K v hv 


variable {K}
variable (r I) {V' : Type*} [AddCommGroup V'] [Module K V']

/-- An injective semilinear map of vector spaces induces a map on QGrassmannians. -/
-- Less general than the version for projective spaces because LinearIndependent.map' requires the tV'o rings to be equal.
def QGrassmannian.map (f : V →ₗ[K] V') (hf : Function.Injective f) : QGrassmannian K V I → QGrassmannian K V' I :=
  Quotient.map' (fun v => ⟨f.comp v.1, by rw [LinearMap.coe_comp]; exact Function.Injective.comp hf v.2⟩)
    (by rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
        change LinearMap.range _ = _ at hvw
        change LinearMap.range _ = _
        simp only at hvw ⊢ 
        rw [LinearMap.range_comp, LinearMap.range_comp]
        rw [hvw])

lemma QGrassmannian.map_mk (f : V →ₗ[K] V') (hf : Function.Injective f) (v : (I → K) →ₗ[K] V) (hv : Function.Injective v) :
    QGrassmannian.map I f hf (QGrassmannian.mk K v hv) = QGrassmannian.mk K (f.comp v) 
    (by rw [LinearMap.coe_comp]; exact Function.Injective.comp hf hv) := rfl

/-- The map we have defined is injective. -/
theorem QGrassmannian.map_injective (f : V →ₗ[K] V') (hf : Function.Injective f) : 
Function.Injective (QGrassmannian.map I f hf) := by 
  intro x y hxy 
  induction' x using QGrassmannian.ind with v hv  
  induction' y using QGrassmannian.ind with w hw 
  rw [QGrassmannian.mk_eq_mk_iff_range]
  rw [QGrassmannian.map_mk, QGrassmannian.map_mk, QGrassmannian.mk_eq_mk_iff_range, LinearMap.range_comp, 
    LinearMap.range_comp] at hxy 
  apply_fun (fun p => SetLike.coe p) at hxy 
  rw [Submodule.map_coe, Submodule.map_coe] at hxy  
  apply SetLike.coe_injective'  
  exact Function.Injective.image_injective hf hxy 


@[simp]
lemma QGrassmannian.map_id : QGrassmannian.map I (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  ext ⟨v⟩
  rfl


lemma QGrassmannian.map_comp {U : Type*} [AddCommGroup U] [Module K U] (f : V →ₗ[K] V') (hf : Function.Injective f)
    (g : V' →ₗ[K] U) (hg : Function.Injective g) :
    QGrassmannian.map I (g.comp f) (hg.comp hf) = QGrassmannian.map I g hg ∘ QGrassmannian.map I f hf := by 
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

variable {r I}
variable (K V hrI)

lemma NonemptyGrassmannian_iff : Nonempty ({v : (I → K) →ₗ[K] V // Function.Injective v}) ↔ Nonempty (Grassmannian K V r) := by
  rw [←(nonempty_quotient_iff (grassmannianSetoid K V I))] 
  exact Equiv.nonempty_congr (QGrassmannianEquivGrassmannian K V hrI)


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
    set b : Fin r → V := fun i => (Finset.equivFinOfCardEq hsr).symm i 
    have hb : LinearIndependent K b := by
      apply LinearIndependent.comp hslin 
      apply Equiv.injective   
    set v := LinearMap.lsum K (fun _ ↦ K) ℕ fun i ↦ LinearMap.id.smulRight (b i)
    rw [Fintype.linearIndependent_iff', LinearMap.ker_eq_bot] at hb
    rw [←(NonemptyGrassmannian_iff K V (Fintype.card_fin r))]
    exact Nonempty.intro ⟨v, hb⟩


#exit 

/- Topologies. -/ -- And here we really see the problem: (I → 𝕜) →ₗ[𝕜] E doesn't have a topology !

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]

/-- We equip the QGrassmannian with the "coinduced" topology from the natural map
`mk' : {v : (I → 𝕜) →ₗ[𝕜] E // LinearIndependent 𝕜 v} → QGrassmannanian 𝕜 V r`. -/
instance : TopologicalSpace (QGrassmannian 𝕜 E I) :=
TopologicalSpace.coinduced (QGrassmannian.mk' 𝕜) instTopologicalSpaceSubtype 

/- We equip the Grassmannian with the coinduced topology from the equivalence with the QGrassmannian. Note that this is also
an induced topology, see Equiv.induced_symm and Equiv.coinduced_symm.-/

instance : TopologicalSpace (Grassmannian 𝕜 E r) :=
TopologicalSpace.coinduced (Grassmannian.mk' 𝕜) instTopologicalSpaceSubtype 



end

  