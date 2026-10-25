import Submission.Obl.k4_pair_bin_atlas_assembly.FiniteAssembly

namespace Submission.Obl.k4_pair_bin_atlas_assembly

theorem realization_from_assembly : AnalyticKernel → DiscSublevel → SafePaths → Realization := by
  intro hk hd hs
  obtain ⟨Cs, hCs, hprob⟩ := safePaths_probability hs
  obtain ⟨k⟩ := hk.binKernel Cs hCs
  obtain ⟨CD, hCD, hsub⟩ := hd Cs hCs
  let C₂ : ℝ := CD + k.CK + 2 * k.CR + 1
  have hC₂ : 0 < C₂ := by dsimp [C₂]; linarith [k.CK_pos, k.CR_pos]
  apply realization_of_finiteAssembly hC₂ (show (0 : ℝ) < 1 by norm_num)
  exact finiteAssembly k (by dsimp [C₂]; linarith [k.CK_pos, k.CR_pos])
    (by dsimp [C₂]; linarith) hprob hsub

end Submission.Obl.k4_pair_bin_atlas_assembly
