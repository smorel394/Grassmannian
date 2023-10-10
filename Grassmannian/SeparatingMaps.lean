import Mathlib.Tactic
import Grassmannian.Grassmannian 
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Mathlib.Algebra.Module.Projective


open Classical
noncomputable section 

section NoTopology 

variable {𝕜 E F G : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] 
[AddCommGroup F] [Module 𝕜 F] [AddCommGroup G] [Module 𝕜 G] 

variable (F G)

lemma SeparatingMaps_iff_surjective (r : ℕ) (W : Grassmannian 𝕜 E r) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) (f : E →ₗ[𝕜] F) : 
(W.1 ⊓ (LinearMap.ker f) = ⊥) ↔ Function.Surjective (f.comp (Submodule.subtype W)) := by
  letI := W.2.1 
  rw [←LinearMap.injective_iff_surjective_of_finrank_eq_finrank] 
  . rw [←LinearMap.ker_eq_bot]
    constructor 
    . intro h
      rw [Submodule.eq_bot_iff]
      intro u 
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype,
        Function.comp_apply]
      intro hu 
      have hint : u.1 ∈ W.1 ⊓ LinearMap.ker f := by
          simp only [ge_iff_le, Submodule.mem_inf, SetLike.coe_mem, LinearMap.mem_ker, hu, and_self]
      rw [h] at hint 
      simp only [Submodule.mem_bot, ZeroMemClass.coe_eq_zero] at hint  
      exact hint 
    . intro h 
      rw [Submodule.eq_bot_iff]
      intro u
      simp only [ge_iff_le, Submodule.mem_inf, LinearMap.mem_ker, and_imp] 
      intro huW huf
      have hu : ⟨u, huW⟩ ∈ LinearMap.ker (f.comp (Submodule.subtype W.1)) := by
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Submodule.coeSubtype, Function.comp_apply, huf]
      rw [h] at hu 
      simp only [Submodule.mem_bot, Submodule.mk_eq_zero] at hu  
      exact hu
  . rw [W.2.2, hrankF]

lemma SeparatingMaps_iff_bijective (r : ℕ) (W : Grassmannian 𝕜 E r) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) (f : E →ₗ[𝕜] F) : 
(W.1 ⊓ (LinearMap.ker f) = ⊥) ↔ Function.Bijective (f.comp (Submodule.subtype W)) := by
  rw [SeparatingMaps_iff_surjective]
  change _ ↔ _ ∧ _ 
  simp only [iff_and_self]
  intro hsurj
  rw [←SeparatingMaps_iff_surjective] at hsurj 
  rw [←LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro u hu 
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Submodule.coeSubtype, Function.comp_apply] at hu  
  have h : u.1 = 0 := by
    rw [←(Submodule.mem_bot 𝕜), ←hsurj, Submodule.mem_inf]
    exact ⟨u.2, hu⟩
  rw [←(Submodule.coe_zero (R :=𝕜)), SetCoe.ext_iff] at h 
  exact h 
  exact hrankF 
  exact hrankF

lemma SeparatingMaps_iff_isCompl (r : ℕ) (W : Grassmannian 𝕜 E r) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) (f : E →ₗ[𝕜] F) : 
(W.1 ⊓ (LinearMap.ker f) = ⊥) ↔ IsCompl W.1 (LinearMap.ker f) := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  simp only [iff_self_and]
  rw [Submodule.eq_top_iff']
  intro h 
  intro u
  rw [Submodule.mem_sup]
  rw [SeparatingMaps_iff_surjective] at h
  obtain ⟨⟨w, hw⟩, hwu⟩ := h (f u)
  simp only [LinearMap.coe_comp, Submodule.coeSubtype, Function.comp_apply] at hwu 
  set v := u - w 
  have hv : v ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, map_sub, hwu, sub_self]
  existsi w
  rw [and_iff_right hw]
  existsi v 
  rw [and_iff_right hv]
  simp only [add_sub_cancel'_right]
  exact hrankF 

end NoTopology 



section Topology 

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]   
[NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] 
[CompleteSpace 𝕜] 

variable (𝕜 E)


def SeparatingMaps (r : ℕ) : Prop := ∀ (W : Grassmannian 𝕜 E r), ∃ (f : E →L[𝕜] (Fin r → 𝕜)), 
(W.1 ⊓ (LinearMap.ker f) = ⊥)

lemma SeparatingMaps_zero : SeparatingMaps 𝕜 E 0 := by
  intro ⟨W, hWfd, hWrank⟩
  existsi 0 
  letI := hWfd 
  rw [finrank_eq_zero] at hWrank
  simp only [ge_iff_le]
  rw [hWrank]
  simp only [ge_iff_le, bot_le, inf_of_le_left]


variable {𝕜 E}




lemma SeparatingMaps_iff_target_aux (r : ℕ) (W : Grassmannian 𝕜 E r) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) [FiniteDimensional 𝕜 G] 
(hrankG : FiniteDimensional.finrank 𝕜 G = r) : 
(∃ (f : E →L[𝕜] F), (W.1 ⊓ (LinearMap.ker f) = ⊥)) →
(∃ (f : E →L[𝕜] G), (W.1 ⊓ (LinearMap.ker f) = ⊥)) := by 
  have cond : FiniteDimensional.finrank 𝕜 F = FiniteDimensional.finrank 𝕜 G := by
    rw [hrankF, hrankG]
  intro ⟨f, hf⟩
  set e := ContinuousLinearEquiv.ofFinrankEq cond 
  existsi ContinuousLinearMap.comp (ContinuousLinearEquiv.ofFinrankEq cond) f
  erw [LinearEquiv.ker_comp] 
  exact hf 

variable (F G)

lemma SeparatingMaps_iff_target (r : ℕ) (W : Grassmannian 𝕜 E r) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) [FiniteDimensional 𝕜 G] 
(hrankG : FiniteDimensional.finrank 𝕜 G = r) : 
(∃ (f : E →L[𝕜] F), (W.1 ⊓ (LinearMap.ker f) = ⊥)) ↔
(∃ (f : E →L[𝕜] G), (W.1 ⊓ (LinearMap.ker f) = ⊥)) := 
⟨SeparatingMaps_iff_target_aux r W hrankF hrankG, SeparatingMaps_iff_target_aux r W hrankG hrankF⟩

variable {F G}

lemma SeparatingMaps_recursion (r : ℕ) (hsep : SeparatingDual 𝕜 E) :
SeparatingMaps 𝕜 E r → SeparatingMaps 𝕜 E (Nat.succ r) := by
  intro hind W 
  letI := W.2.1 
  set b := FiniteDimensional.finBasisOfFinrankEq 𝕜 W.1 W.2.2
  set W' := Submodule.span 𝕜 (Set.range (((fun i => (b i).1) ∘ (Fin.castLE (Nat.le_succ r))))) 
  have hW'W : W' ≤ W.1 := by
    rw [Submodule.span_le]
    intro v 
    simp only [Set.mem_range, Function.comp_apply, SetLike.mem_coe, forall_exists_index]
    intro i hiv 
    rw [←hiv]
    simp only [SetLike.coe_mem]
  have hW'fd : FiniteDimensional 𝕜 W' := by
    exact Submodule.finiteDimensional_of_le hW'W 
  have hW'rank : FiniteDimensional.finrank 𝕜 W' = r := by
    have hlin : LinearIndependent 𝕜 ((fun i => (b i).1) ∘ (Fin.castLE (Nat.le_succ r))) := by
      apply LinearIndependent.comp 
      . have heq : (fun i => (b i).1) = (Submodule.subtype W.1) ∘ b := by
          ext i 
          simp only [Submodule.coeSubtype, Function.comp_apply]
        rw [heq]
        apply LinearIndependent.map' 
        . apply Basis.linearIndependent 
        . simp only [Submodule.ker_subtype]
      . intro i j heq 
        apply_fun (fun i => i.1) at heq 
        simp only [Fin.coe_castLE] at heq   
        exact Fin.ext heq 
    rw [finrank_span_eq_card hlin]
    simp only [Fintype.card_fin]
  obtain ⟨f, hf⟩ := hind ⟨W', hW'fd, hW'rank⟩ 
  have hnt : LinearMap.ker (f.toLinearMap.comp (Submodule.subtype W)) ≠ ⊥ := by
    by_contra habs 
    rw [LinearMap.ker_eq_bot] at habs 
    have h := LinearMap.finrank_le_finrank_of_injective habs 
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin] at h 
    rw [W.2.2] at h 
    exact Nat.not_succ_le_self r h 
  rw [Submodule.ne_bot_iff] at hnt 
  obtain ⟨⟨u, huW⟩, hfu, hunz⟩ := hnt 
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype,
    Function.comp_apply] at hfu  
  simp only [ne_eq, Submodule.mk_eq_zero] at hunz  
  obtain ⟨g, hgu⟩ := hsep.exists_eq_one hunz
  rw [SeparatingMaps_iff_target (Fin (Nat.succ r) → 𝕜) ((Fin r → 𝕜) × 𝕜) (Nat.succ r) W]
  . existsi ContinuousLinearMap.prod f g 
    erw [SeparatingMaps_iff_surjective]
    intro ⟨a, b⟩
    erw [SeparatingMaps_iff_surjective] at hf
    change Function.Surjective (f.toLinearMap.comp (Submodule.subtype W')) at hf 
    obtain ⟨⟨v, hvW'⟩, hfv⟩ := hf a
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype, Function.comp_apply] at hfv  
    have hvW : v ∈ W.1 := Set.mem_of_mem_of_subset hvW' hW'W  
    existsi ⟨v, hvW⟩ + (b - g v) • ⟨u, huW⟩  
    rw [LinearMap.comp_apply, Submodule.subtype_apply]
    simp only [SetLike.mk_smul_mk, AddSubmonoid.mk_add_mk]
    erw [ContinuousLinearMap.prod_apply]
    apply Prod.ext 
    . simp only [map_add, hfv, map_smul, hfu, smul_zero, add_zero]
    . simp only [map_add, map_smul, hgu, smul_eq_mul, mul_one, add_sub_cancel'_right]
    . simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
    . simp only [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin,
      FiniteDimensional.finrank_self]
  . simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
  . simp only [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin,
    FiniteDimensional.finrank_self]
  

lemma SeparatingMaps.ofSeparatingDual (hsep : SeparatingDual 𝕜 E) : 
∀ (r : ℕ), SeparatingMaps 𝕜 E r := by
  intro r; induction' r with r hrec 
  . exact SeparatingMaps_zero 𝕜 E 
  . exact SeparatingMaps_recursion r hsep hrec 

end Topology


end 

