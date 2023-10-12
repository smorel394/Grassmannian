import Mathlib.Tactic 
import Mathlib.Geometry.Manifold.ContMDiff

open Classical
noncomputable section 


variable {𝕜: Type u_1} {E : Type u_2} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
 {H : Type u_3} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type u_4} [TopologicalSpace M] 
 [ChartedSpace H M] {E' : Type u_5} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] 
{α : Type u_8} [TopologicalSpace α] [Nonempty α] {j : α → E'} (h : OpenEmbedding j) 

lemma ContMDiffAT_vs_openEmbedding (f : M → α) (x : M) :
@ContMDiffAt 𝕜 _ E _ _ H _ I M _ _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _ 
(OpenEmbedding.singletonChartedSpace h) n f x ↔ ContMDiffAt I (modelWithCornersSelf 𝕜 E') (E' := E') 
(H' := E') n (j ∘ f) x := by 
  have hj : h.toLocalHomeomorph ∈ @SmoothManifoldWithCorners.maximalAtlas 𝕜 _ E' _ _ E' _
         (modelWithCornersSelf 𝕜 E') α _ (OpenEmbedding.singletonChartedSpace h):= by 
        apply @SmoothManifoldWithCorners.subset_maximalAtlas 𝕜 _ E' _ _ E' _
         (modelWithCornersSelf 𝕜 E') α _ (OpenEmbedding.singletonChartedSpace h)
         (OpenEmbedding.singleton_smoothManifoldWithCorners _ h)            
        change _ ∈ {h.toLocalHomeomorph} 
        simp only [Set.mem_singleton_iff]
  constructor 
  . intro hdiff
    apply @ContMDiffAt.comp 𝕜 _ E _ _ H _ I M _ _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _
      (OpenEmbedding.singletonChartedSpace h) 
    . apply @contMDiffAt_of_mem_maximalAtlas 𝕜 _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _
        (OpenEmbedding.singletonChartedSpace h) (OpenEmbedding.singleton_smoothManifoldWithCorners _ h) 
        h.toLocalHomeomorph (f x) n hj 
      rw [OpenEmbedding.toLocalHomeomorph_source j h]
      apply Set.mem_univ 
    . exact hdiff
  . intro hdiff 
    have heq : f = (h.toLocalHomeomorph).symm ∘ (j ∘ f) := by 
      ext x 
      simp only [Function.comp_apply]
      conv => rhs 
              congr 
              rfl
              rw [←(OpenEmbedding.toLocalHomeomorph_apply j h)]
      rw [(h.toLocalHomeomorph).left_inv]
      rw [OpenEmbedding.toLocalHomeomorph_source j h]
      exact Set.mem_univ _ 
    rw [heq]
    apply @ContMDiffAt.comp 𝕜 _ E _ _ H _ I M _ _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') E' _ _ 
      E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _ (OpenEmbedding.singletonChartedSpace h) 
      (j ∘ f) n (h.toLocalHomeomorph).symm 
    . apply @contMDiffAt_symm_of_mem_maximalAtlas 𝕜 _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _
        (OpenEmbedding.singletonChartedSpace h) (OpenEmbedding.singleton_smoothManifoldWithCorners _ h) 
        h.toLocalHomeomorph n ((j ∘ f) x) hj 
      rw [OpenEmbedding.toLocalHomeomorph_target j h]
      simp only [Function.comp_apply, Set.mem_range, exists_apply_eq_apply]
    . exact hdiff 


lemma ContMDiff_vs_openEmbedding (f : M → α) :
@ContMDiff 𝕜 _ E _ _ H _ I M _ _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _ 
(OpenEmbedding.singletonChartedSpace h) n f ↔ ContMDiff I (modelWithCornersSelf 𝕜 E') (E' := E') 
(H' := E') n (j ∘ f) := by 
  have hj : h.toLocalHomeomorph ∈ @SmoothManifoldWithCorners.maximalAtlas 𝕜 _ E' _ _ E' _
         (modelWithCornersSelf 𝕜 E') α _ (OpenEmbedding.singletonChartedSpace h):= by 
        apply @SmoothManifoldWithCorners.subset_maximalAtlas 𝕜 _ E' _ _ E' _
         (modelWithCornersSelf 𝕜 E') α _ (OpenEmbedding.singletonChartedSpace h)
         (OpenEmbedding.singleton_smoothManifoldWithCorners _ h)            
        change _ ∈ {h.toLocalHomeomorph} 
        simp only [Set.mem_singleton_iff]
  constructor 
  . intro hdiff
    apply @ContMDiff.comp 𝕜 _ E _ _ H _ I M _ _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _
      (OpenEmbedding.singletonChartedSpace h) 
    .  rw [←(@contMDiffOn_univ 𝕜 _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _
         (OpenEmbedding.singletonChartedSpace h))]
       rw [←(OpenEmbedding.toLocalHomeomorph_source j h)]
       exact @contMDiffOn_of_mem_maximalAtlas 𝕜 _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _
         (OpenEmbedding.singletonChartedSpace h) (OpenEmbedding.singleton_smoothManifoldWithCorners _ h) 
         h.toLocalHomeomorph n hj    
    . exact hdiff 
  . intro hdiff 
    have heq : f = (h.toLocalHomeomorph).symm ∘ (j ∘ f) := by 
      ext x 
      simp only [Function.comp_apply]
      conv => rhs 
              congr 
              rfl
              rw [←(OpenEmbedding.toLocalHomeomorph_apply j h)]
      rw [(h.toLocalHomeomorph).left_inv]
      rw [OpenEmbedding.toLocalHomeomorph_source j h]
      exact Set.mem_univ _ 
    rw [heq]
    rw [←(@contMDiffOn_univ 𝕜 _ E _ _ H _ I M _ _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _ 
      (OpenEmbedding.singletonChartedSpace h))]
    apply @ContMDiffOn.comp 𝕜 _ E _ _ H _ I M _ _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') E' _ _ 
      E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _ (OpenEmbedding.singletonChartedSpace h) 
      (j ∘ f) Set.univ n (h.toLocalHomeomorph).target (h.toLocalHomeomorph).symm 
    . exact @contMDiffOn_symm_of_mem_maximalAtlas 𝕜 _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _
         (OpenEmbedding.singletonChartedSpace h) (OpenEmbedding.singleton_smoothManifoldWithCorners _ h) 
         h.toLocalHomeomorph n hj    
    . rw [contMDiffOn_univ]
      exact hdiff
    . rw [OpenEmbedding.toLocalHomeomorph_target j h]
      intro x 
      simp only [Set.mem_univ, Set.mem_preimage, Function.comp_apply, Set.mem_range, exists_apply_eq_apply,
        forall_true_left]


-- This almost exists, see contMDiff_inclusion. Except not quite, because here we have an open embedding into E,
-- not opens of E. 
lemma contMDiffOpenEmbedding : @ContMDiff 𝕜 _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') α _ 
(OpenEmbedding.singletonChartedSpace h) E' _ _ E' _ (modelWithCornersSelf 𝕜 E') E' _ _ n j := by 
  letI : ChartedSpace E' α := OpenEmbedding.singletonChartedSpace h 
  have ha := @ContMDiff_vs_openEmbedding 𝕜 E' _ _ _ E' _ (modelWithCornersSelf 𝕜 E') α _ _ 
    E' _ _ α _ _ j h n (fun (x : α) => (x : α))  
  have heq : j ∘ (fun x => x) = j := by ext x; simp only [Function.comp_apply]
  rw [heq] at ha 
  rw [←ha]
  exact contMDiff_id 
