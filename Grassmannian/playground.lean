import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Data.Real.Basic


#check balancedCoreAux 

open Classical
noncomputable section 

universe u v

variable {𝕜 : Type u} [hnorm : NormedDivisionRing 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F : Type w} [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜 F] {F' : Type x}
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [TopologicalAddGroup F']
  [ContinuousSMul 𝕜 F'] {hnt : ∃ (x : 𝕜), 1 < ‖x‖}

open Set FiniteDimensional TopologicalSpace Filter BigOperators

variable [CompleteSpace 𝕜]

variable (𝕜)

lemma NormedDivisionRing.exists_lt_norm (r : ℝ) : ∃ (x : 𝕜), r < ‖x‖ :=
  let ⟨w, hw⟩ := hnt
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩


lemma  NormedDivisionRing.exists_norm_lt {r : ℝ} (hr : 0 < r) : 
∃ (x : 𝕜), 0 < ‖x‖ ∧ ‖x‖ < r := 
  let ⟨w, hw⟩ := NormedDivisionRing.exists_lt_norm r⁻¹ (hnt := hnt)
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩


instance : SMul 𝕜 (Set E) := @Set.smulSet 𝕜 E _ 
instance : MulAction 𝕜 (Set E) := Set.mulActionSet


variable {𝕜}

theorem balancedCoreAux_subset_var (s : Set E) : balancedCoreAux 𝕜 s ⊆ s := fun x hx => by 
  simpa only [one_smul] using mem_balancedCoreAux_iff.1 hx 1 norm_one.ge 

theorem balancedCoreAux_balanced_var (h0 : (0 : E) ∈ balancedCoreAux 𝕜 s) :
    Balanced 𝕜 (balancedCoreAux 𝕜 s) := by
  rintro a ha x ⟨y, hy, rfl⟩
  obtain rfl | h := eq_or_ne a 0
  · simp_rw [zero_smul, h0]
  rw [mem_balancedCoreAux_iff] at hy ⊢
  intro r hr
  have h'' : 1 ≤ ‖a⁻¹ • r‖ := by
    rw [norm_smul, norm_inv]
    exact one_le_mul_of_one_le_of_one_le (one_le_inv (norm_pos_iff.mpr h) ha) hr
  have h' := hy (a⁻¹ • r) h''
  rwa [smul_assoc, mem_inv_smul_set_iff₀ h] at h'

theorem balancedCoreAux_maximal_var (h : t ⊆ s) (ht : Balanced 𝕜 t) : t ⊆ @balancedCoreAux 𝕜 E _ _ s := by
  refine' fun x hx => mem_balancedCoreAux_iff.2 fun r hr => _
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp <| zero_lt_one.trans_le hr)]
  refine' h (ht.smul_mem _ hx)
  rw [norm_inv]
  exact inv_le_one hr

theorem balancedCore_subset_balancedCoreAux_var : balancedCore 𝕜 s ⊆ @balancedCoreAux 𝕜 E  _ _ s  := 
  balancedCoreAux_maximal_var (balancedCore_subset s) (balancedCore_balanced s)




theorem balancedCore_eq_iInter_var (hs : (0 : E) ∈ s) :
    balancedCore 𝕜 s = ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s := by
  refine' balancedCore_subset_balancedCoreAux_var.antisymm _
  refine' (balancedCoreAux_balanced_var _).subset_balancedCore_of_subset (balancedCoreAux_subset_var s)
  exact balancedCore_subset_balancedCoreAux_var (balancedCore_zero_mem hs)


theorem subset_balancedCore_var {s : Set E} {t : Set E} (ht : 0 ∈ t) (hst : ∀ (a : 𝕜), ‖a‖ ≤ 1 → a • s ⊆ t) :
s ⊆ balancedCore 𝕜 t := by 
  rw [balancedCore_eq_iInter_var ht]
  refine' subset_iInter₂ fun a ha => _
  rw [← smul_inv_smul₀ (norm_pos_iff.mp <| zero_lt_one.trans_le ha) s]
  refine' smul_set_mono (hst _ _)
  rw [norm_inv]
  exact inv_le_one ha


theorem balancedCore_mem_nhds_zero_var (hU : U ∈ nhds (0 : E)) : balancedCore 𝕜 U ∈ nhds (0 : E) := by
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  obtain ⟨r, V, hr, hV, hrVU⟩ : ∃ (r : ℝ) (V : Set E),
      0 < r ∧ V ∈ nhds (0 : E) ∧ ∀ (c : 𝕜) (y : E), ‖c‖ < r → y ∈ V → c • y ∈ U := by
    have h : Filter.Tendsto (fun x : 𝕜 × E => x.fst • x.snd) (nhds (0, 0)) (nhds 0) :=
      continuous_smul.tendsto' (0, 0) _ (smul_zero _)
    simpa only [← Prod.exists', ← Prod.forall', ← and_imp, ← and_assoc, exists_prop] using
      h.basis_left (NormedAddCommGroup.nhds_zero_basis_norm_lt.prod_nhds (nhds _).basis_sets) U hU
  rcases NormedDivisionRing.exists_norm_lt hr (hnt := hnt) with ⟨y, hy₀, hyr⟩
  rw [norm_pos_iff] at hy₀
  have : y • V ∈ nhds (0 : E) := (set_smul_mem_nhds_zero_iff hy₀).mpr hV
  -- It remains to show that `y • V ⊆ balancedCore 𝕜 U`
  refine' Filter.mem_of_superset this (subset_balancedCore_var (mem_of_mem_nhds hU) fun a ha => _)
  rw [smul_smul]
  rintro _ ⟨z, hz, rfl⟩
  refine' hrVU _ _ _ hz
  rw [norm_mul, ← one_mul r]
  exact mul_lt_mul' ha hyr (norm_nonneg y) one_pos

theorem unique_topology_of_t2_var {t : TopologicalSpace 𝕜} (h₁ : @TopologicalAddGroup 𝕜 t _)
    (h₂ : @ContinuousSMul 𝕜 𝕜 _ hnorm.toUniformSpace.toTopologicalSpace t) (h₃ : @T2Space 𝕜 t) :
    t = hnorm.toUniformSpace.toTopologicalSpace := by
  -- Let `𝓣₀` denote the topology on `𝕜` induced by the norm, and `𝓣` be any T2 vector
  -- topology on `𝕜`. To show that `𝓣₀ = 𝓣`, it suffices to show that they have the same
  -- neighborhoods of 0.
  refine' TopologicalAddGroup.ext h₁ inferInstance (le_antisymm _ _)
  · -- To show `𝓣 ≤ 𝓣₀`, we have to show that closed balls are `𝓣`-neighborhoods of 0.
    rw [Metric.nhds_basis_closedBall.ge_iff]
    -- Let `ε > 0`. Since `𝕜` is nontrivially normed, we have `0 < ‖ξ₀‖ < ε` for some `ξ₀ : 𝕜`.
    intro ε hε
    rcases NormedDivisionRing.exists_norm_lt (hnt := hnt) hε with ⟨ξ₀, hξ₀, hξ₀ε⟩
    -- Since `ξ₀ ≠ 0` and `𝓣` is T2, we know that `{ξ₀}ᶜ` is a `𝓣`-neighborhood of 0.
    -- Porting note: added `mem_compl_singleton_iff.mpr`
    have : {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := IsOpen.mem_nhds isOpen_compl_singleton <|
      mem_compl_singleton_iff.mpr <| Ne.symm <| norm_ne_zero_iff.mp hξ₀.ne.symm
    -- Thus, its balanced core `𝓑` is too. Let's show that the closed ball of radius `ε` contains
    -- `𝓑`, which will imply that the closed ball is indeed a `𝓣`-neighborhood of 0.
    have : balancedCore 𝕜 {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := balancedCore_mem_nhds_zero_var this (hnt := hnt)
    refine' mem_of_superset this fun ξ hξ => _
    -- Let `ξ ∈ 𝓑`. We want to show `‖ξ‖ < ε`. If `ξ = 0`, this is trivial.
    by_cases hξ0 : ξ = 0
    · rw [hξ0]
      exact Metric.mem_closedBall_self hε.le
    · rw [mem_closedBall_zero_iff]
      -- Now suppose `ξ ≠ 0`. By contradiction, let's assume `ε < ‖ξ‖`, and show that
      -- `ξ₀ ∈ 𝓑 ⊆ {ξ₀}ᶜ`, which is a contradiction.
      by_contra' h
      suffices (ξ₀ * ξ⁻¹) • ξ ∈ balancedCore 𝕜 {ξ₀}ᶜ by
        rw [smul_eq_mul 𝕜, mul_assoc, inv_mul_cancel hξ0, mul_one] at this
        exact not_mem_compl_iff.mpr (mem_singleton ξ₀) ((balancedCore_subset _) this)
      -- For that, we use that `𝓑` is balanced : since `‖ξ₀‖ < ε < ‖ξ‖`, we have `‖ξ₀ / ξ‖ ≤ 1`,
      -- hence `ξ₀ = (ξ₀ / ξ) • ξ ∈ 𝓑` because `ξ ∈ 𝓑`.
      refine' (balancedCore_balanced _).smul_mem _ hξ
      rw [norm_mul, norm_inv, mul_inv_le_iff (norm_pos_iff.mpr hξ0), mul_one]
      exact (hξ₀ε.trans h).le
  · -- Finally, to show `𝓣₀ ≤ 𝓣`, we simply argue that `id = (fun x ↦ x • 1)` is continuous from
    -- `(𝕜, 𝓣₀)` to `(𝕜, 𝓣)` because `(•) : (𝕜, 𝓣₀) × (𝕜, 𝓣) → (𝕜, 𝓣)` is continuous.
    calc
      @nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0 =
          map id (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) :=
        map_id.symm
      _ = map (fun x => id x • (1 : 𝕜)) (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) := by
        conv_rhs =>
          congr
          ext
          rw [smul_eq_mul, mul_one]
      _ ≤ @nhds 𝕜 t ((0 : 𝕜) • (1 : 𝕜)) :=
        (@Tendsto.smul_const _ _ _ hnorm.toUniformSpace.toTopologicalSpace t _ _ _ _ _
          tendsto_id (1 : 𝕜))
      _ = @nhds 𝕜 t 0 := by rw [zero_smul]


theorem LinearMap.continuous_of_isClosed_ker_var (l : E →ₗ[𝕜] 𝕜)
    (hl : IsClosed (LinearMap.ker l : Set E)) :
    Continuous l := by
  -- `l` is either constant or surjective. If it is constant, the result is trivial.
  by_cases H : finrank 𝕜 (LinearMap.range l) = 0
  · rw [finrank_eq_zero, LinearMap.range_eq_bot] at H
    rw [H]
    exact continuous_zero
  · -- In the case where `l` is surjective, we factor it as `φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜`. Note that
    -- `E ⧸ l.ker` is T2 since `l.ker` is closed.
    have : finrank 𝕜 (LinearMap.range l) = 1 :=
      le_antisymm (finrank_self 𝕜 ▸ l.range.finrank_le) (zero_lt_iff.mpr H)
    have hi : Function.Injective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (le_refl _)
    have hs : Function.Surjective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.range_eq_top, Submodule.range_liftQ]
      exact Submodule.eq_top_of_finrank_eq ((finrank_self 𝕜).symm ▸ this)
    let φ : (E ⧸ LinearMap.ker l) ≃ₗ[𝕜] 𝕜 :=
      LinearEquiv.ofBijective ((LinearMap.ker l).liftQ l (le_refl _)) ⟨hi, hs⟩
    have hlφ : (l : E → 𝕜) = φ ∘ (LinearMap.ker l).mkQ := by ext; rfl
    -- Since the quotient map `E →ₗ[𝕜] (E ⧸ l.ker)` is continuous, the continuity of `l` will follow
    -- form the continuity of `φ`.
    suffices Continuous φ.toEquiv by
      rw [hlφ]
      exact this.comp continuous_quot_mk
    -- The pullback by `φ.symm` of the quotient topology is a T2 topology on `𝕜`, because `φ.symm`
    -- is injective. Since `φ.symm` is linear, it is also a vector space topology.
    -- Hence, we know that it is equal to the topology induced by the norm.
    have : induced φ.toEquiv.symm inferInstance = hnorm.toUniformSpace.toTopologicalSpace := by
      refine'
        unique_topology_of_t2_var (topologicalAddGroup_induced φ.symm.toLinearMap)
          (continuousSMul_induced φ.symm.toLinearMap) _
      -- Porting note: was `rw [t2Space_iff]`
      exact hnt
      refine (@t2Space_iff 𝕜 (induced (↑(LinearEquiv.toEquiv φ).symm) inferInstance)).mpr ?_
      exact fun x y hxy =>
        @separated_by_continuous _ _ (induced _ _) _ _ _ continuous_induced_dom _ _
          (φ.toEquiv.symm.injective.ne hxy)
    -- Finally, the pullback by `φ.symm` is exactly the pushforward by `φ`, so we have to prove
    -- that `φ` is continuous when `𝕜` is endowed with the pushforward by `φ` of the quotient
    -- topology, which is trivial by definition of the pushforward.
    rw [this.symm, Equiv.induced_symm]
    exact continuous_coinduced_rng

    end 