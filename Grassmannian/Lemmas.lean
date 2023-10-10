import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis
import Mathlib.Analysis.Calculus.ContDiffDef


lemma Basis.constr_ker {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M' : Type u_7} [Semiring R] 
[AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] (b : Basis ι R M) (S : Type u_10) 
[Semiring S] [Module S M'] [SMulCommClass R S M'] {v : ι → M'} (hv : LinearIndependent R v) :
LinearMap.ker (Basis.constr b S v) = ⊥ := by
  ext u
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor 
  . intro h
    rw [Basis.constr_apply] at h 
    change LinearMap.ker _ = ⊥  at hv 
    rw [←Finsupp.total_apply, ←LinearMap.mem_ker, hv] at h
    simp only [Submodule.mem_bot, AddEquivClass.map_eq_zero_iff] at h  
    exact h 
  . exact fun h => by simp only [h, map_zero]

lemma LinearMap.graph_fst_injective {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M] 
[AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) :
Function.Injective ((LinearMap.fst R M M₂).domRestrict (LinearMap.graph f)) := by
  intro ⟨v, hv⟩ ⟨v', hv'⟩ hvv' 
  simp only [Subtype.mk.injEq]
  simp only [domRestrict_apply, fst_apply] at hvv' 
  rw [Prod.ext_iff, and_iff_right hvv']
  rw [LinearMap.mem_graph_iff] at hv hv'
  rw [hv, hv', hvv']

lemma LinearMap.graph_fst_surjective {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M] 
[AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) :
Function.Surjective ((LinearMap.fst R M M₂).domRestrict (LinearMap.graph f)) := by
  intro v 
  simp only [domRestrict_apply, fst_apply, Subtype.exists, mem_graph_iff, exists_prop, Prod.exists, exists_eq_left,
         exists_eq]

noncomputable def LinearMap.graph_equiv_fst {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M] 
[AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) : LinearMap.graph f ≃ₗ[R] M := 
 LinearEquiv.ofBijective ((LinearMap.fst R M M₂).domRestrict (LinearMap.graph f)) 
 ⟨LinearMap.graph_fst_injective f, LinearMap.graph_fst_surjective f⟩

theorem contDiffOn_open_iff_contDiffAt_finite {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E] 
[NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set E} {f : E → F} {n : ℕ} 
(hs : IsOpen s) :
ContDiffOn 𝕜 n f s ↔ ∀ (x : s), ContDiffAt 𝕜 n f x := by
  constructor 
  . intro h x
    apply ContDiffOn.contDiffAt h 
    exact IsOpen.mem_nhds hs x.2 
  . intro h
    apply contDiffOn_of_locally_contDiffOn
    intro x hxs 
    obtain ⟨U, hU1, hU2, hU3⟩ := ContDiffWithinAt.contDiffOn' (m := n) (le_refl _) (ContDiffAt.contDiffWithinAt (s := ⊤) (h ⟨x, hxs⟩))
    existsi U 
    simp only at hU2  
    simp only [hU1, hU2, true_and]
    simp only [Set.top_eq_univ, Set.mem_univ, Set.insert_eq_of_mem, Set.univ_inter] at hU3 
    apply ContDiffOn.mono hU3 
    simp only [Set.inter_subset_right]

theorem contDiffOn_open_iff_contDiffAt {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E] 
[NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set E} {f : E → F} {n : ℕ∞} 
(hs : IsOpen s) :
ContDiffOn 𝕜 n f s ↔ ∀ (x : s), ContDiffAt 𝕜 n f x := by
  by_cases hn : n = ⊤
  . constructor 
    . intro h x 
      apply ContDiffOn.contDiffAt h 
      exact IsOpen.mem_nhds hs x.2 
    . rw [hn, contDiffOn_top] 
      intro h n 
      rw [contDiffOn_open_iff_contDiffAt_finite hs]
      intro x 
      apply ContDiffAt.of_le (h x)
      simp only [le_top]
  . rw [←ne_eq, WithTop.ne_top_iff_exists] at hn 
    obtain ⟨m, hm⟩ := hn
    rw [←hm]
    exact contDiffOn_open_iff_contDiffAt_finite hs 
