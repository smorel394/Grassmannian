import Mathlib.Tactic 
import Mathlib.Geometry.Manifold.ContMDiff

open Classical
noncomputable section 


variable {𝕜: Type u_1} {E : Type u_2} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
 {H : Type u_3} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type u_4} [TopologicalSpace M] 
 [ChartedSpace H M] {E' : Type u_5} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] 
{α : Type u_8} [TopologicalSpace α] [Nonempty α] {j : α → E'} (h : OpenEmbedding j) 


lemma truc (f : M → α) :
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

    