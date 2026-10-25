-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.HalfEscape.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Mathlib

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- Approximate invariance under the two contractions generating the unit
interval forces density in that interval. -/
theorem half_invariant_dense {T : Set ℝ} (hTc : IsCompact T) (hT : T.Nonempty)
    {h : ℝ}
    (hinv : ∀ r ∈ T, ∀ b : ℝ, b = 0 ∨ b = 1 →
      ∃ s ∈ T, dist ((r + b) / 2) s ≤ h) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ T, dist x s ≤ 2 * h := by
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (Metric.continuous_infDist_pt T).continuousOn
  have hmax' := isMaxOn_iff.mp hmax
  obtain ⟨b, y, hb, hy, hxy⟩ : ∃ b y : ℝ, (b = 0 ∨ b = 1) ∧
      y ∈ Set.Icc (0 : ℝ) 1 ∧ x₀ = (y + b) / 2 := by
    by_cases hx : x₀ ≤ 1 / 2
    · exact ⟨0, 2 * x₀, Or.inl rfl, ⟨by linarith [hx₀.1], by linarith⟩, by ring⟩
    · exact ⟨1, 2 * x₀ - 1, Or.inr rfl, ⟨by linarith, by linarith [hx₀.2]⟩, by ring⟩
  obtain ⟨r, hr, hyr⟩ := hTc.exists_infDist_eq_dist hT y
  obtain ⟨s, hs, hzs⟩ := hinv r hr b hb
  have hdist : dist x₀ ((r + b) / 2) = dist y r / 2 := by
    rw [hxy, Real.dist_eq, Real.dist_eq, ← sub_div, abs_div]
    norm_num
  have hbound : Metric.infDist x₀ T ≤ Metric.infDist x₀ T / 2 + h := by
    calc Metric.infDist x₀ T ≤ dist x₀ s := Metric.infDist_le_dist_of_mem hs
      _ ≤ dist x₀ ((r + b) / 2) + dist ((r + b) / 2) s := dist_triangle _ _ _
      _ ≤ dist y r / 2 + h := by rw [hdist]; linarith
      _ = Metric.infDist y T / 2 + h := by rw [hyr]
      _ ≤ Metric.infDist x₀ T / 2 + h := by linarith [hmax' y hy]
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hTc.exists_infDist_eq_dist hT x
  refine ⟨s, hs, ?_⟩
  rw [← hxs]
  linarith [hmax' x hx]

theorem exists_half_escape {T : Set ℝ} (hTc : IsCompact T) (hT : T.Nonempty)
    {h : ℝ} (hgap : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ T, 2 * h < dist x s) :
    ∃ r ∈ T, ∃ b : ℝ, (b = 0 ∨ b = 1) ∧ ∀ s ∈ T, h < dist ((r + b) / 2) s := by
  classical
  by_contra hn
  push Not at hn
  have hinv : ∀ r ∈ T, ∀ b : ℝ, b = 0 ∨ b = 1 →
      ∃ s ∈ T, dist ((r + b) / 2) s ≤ h := by
    intro r hr b hb
    exact hn r hr b hb
  obtain ⟨x, hx, hfar⟩ := hgap
  obtain ⟨s, hs, hxs⟩ := half_invariant_dense hTc hT hinv x hx
  exact (not_lt_of_ge hxs) (hfar s hs)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
