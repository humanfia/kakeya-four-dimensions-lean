-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.FiniteReduction

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric

theorem InUnitSquare.norm_le_two {F : Set Plane} (hF : InUnitSquare F) {x : Plane}
    (hx : x ∈ F) : ‖x‖ ≤ 2 := by
  have h0 := hF x hx 0
  have h1 := hF x hx 1
  have hnorm := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_two] at hnorm
  nlinarith [norm_nonneg x, mul_nonneg h0.1 (sub_nonneg.mpr h0.2),
    mul_nonneg h1.1 (sub_nonneg.mpr h1.2)]

theorem AD.exists_global_cover {δ C : ℝ} {F : Set Plane}
    (h : AD δ C F) (hF : InUnitSquare F) (hδ3 : δ ≤ 3) :
    ∃ (m : ℕ) (c : Fin m → Plane), Covers δ F c ∧ (m : ℝ) ≤ C * (3 / δ) := by
  obtain ⟨m, c, hc, hm⟩ := h 0 δ 3 le_rfl hδ3
  refine ⟨m, c, hc.mono_set ?_, hm⟩
  intro x hx
  refine ⟨hx, ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact (hF.norm_le_two hx).trans_lt (by norm_num)

/-- A large triple set forces each factor to require many balls. The loss is
the square of a common upper bound for the covering numbers of both factors. -/
theorem coverLower_factors_of_triples {δ B N : ℝ} (hB : 0 < B)
    {F G : Set Plane} {Q : Set Triple} (hQ : Q ⊆ F ×ˢ (G ×ˢ G))
    (hN : CoverLower δ Q N)
    (hF : ∃ (m : ℕ) (c : Fin m → Plane), Covers δ F c ∧ (m : ℝ) ≤ B)
    (hG : ∃ (m : ℕ) (c : Fin m → Plane), Covers δ G c ∧ (m : ℝ) ≤ B) :
    CoverLower δ F (N / B ^ 2) ∧ CoverLower δ G (N / B ^ 2) := by
  obtain ⟨nF, cF, hcF, hnF⟩ := hF
  obtain ⟨nG, cG, hcG, hnG⟩ := hG
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  constructor
  · intro m c hc
    apply (div_le_iff₀ hBsq).mpr
    have hb := hN (m * (nG * nG)) _ ((hc.prod (hcG.prod hcG)).mono_set hQ)
    calc N ≤ (m : ℝ) * ((nG : ℝ) * nG) := by exact_mod_cast hb
      _ ≤ (m : ℝ) * (B * B) := by gcongr
      _ = (m : ℝ) * B ^ 2 := by ring
  · intro m c hc
    apply (div_le_iff₀ hBsq).mpr
    have hb := hN (nF * (m * nG)) _ ((hcF.prod (hc.prod hcG)).mono_set hQ)
    calc N ≤ (nF : ℝ) * ((m : ℝ) * nG) := by exact_mod_cast hb
      _ ≤ B * ((m : ℝ) * B) := by gcongr
      _ = (m : ℝ) * B ^ 2 := by ring

theorem factor_coverLower_of_AD {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {F G : Set Plane} (hF : InUnitSquare F) (hG : InUnitSquare G)
    (hAF : AD δ (δ ^ (-η)) F) (hAG : AD δ (δ ^ (-η)) G)
    {Q : Set Triple} (hQ : Q ⊆ F ×ˢ (G ×ˢ G))
    (hN : CoverLower δ Q (δ ^ (η - 3))) :
    CoverLower δ F (δ ^ (η - 3) / (δ ^ (-η) * (3 / δ)) ^ 2) ∧
    CoverLower δ G (δ ^ (η - 3) / (δ ^ (-η) * (3 / δ)) ^ 2) := by
  apply coverLower_factors_of_triples (by positivity) hQ hN
  · exact hAF.exists_global_cover hF (by linarith)
  · exact hAG.exists_global_cover hG (by linarith)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
