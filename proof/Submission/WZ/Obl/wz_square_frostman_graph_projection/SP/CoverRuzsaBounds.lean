-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.CoverRuzsaBounds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RectangularScalarTransfer

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products


open scoped Pointwise

/-- Ruzsa's sum inequality with a real-valued lower bound for the middle
set's occupied grid cells. -/
theorem RealCoverBound.ruzsa_sum_grid {δ M N L : ℝ} {A B C : Finset ℝ}
    (hAB : RealCoverBound δ (A + B) M) (hBC : RealCoverBound δ (B + C) N)
    (hδ : 0 < δ) (hL : 0 < L)
    (hB : L ≤ ((B.image (realGridIndex δ)).card : ℝ)) :
    RealCoverBound δ (A + C) (36 * M * N / L) := by
  have hM := hAB.nonneg
  have hN := hBC.nonneg
  obtain ⟨m, ca, hca, hm⟩ := hAB
  obtain ⟨n, cb, hcb, hn⟩ := hBC
  obtain ⟨k, cc, hc, hk⟩ := real_ruzsa_sum hδ A B C ca cb hca hcb
  refine ⟨k, cc, hc, (le_div_iff₀ hL).mpr ?_⟩
  calc
    (k : ℝ) * L ≤ (k : ℝ) * ((B.image (realGridIndex δ)).card : ℝ) := by gcongr
    _ ≤ 36 * (m : ℝ) * (n : ℝ) := hk
    _ ≤ 36 * M * N := by gcongr

theorem RealCoverBound.ruzsa_sum_separated {δ M N : ℝ} {A B C : Finset ℝ}
    (hAB : RealCoverBound δ (A + B) M) (hBC : RealCoverBound δ (B + C) N)
    (hδ : 0 < δ) (hB : B.Nonempty)
    (hsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y) :
    RealCoverBound δ (A + C) (36 * M * N / (B.card : ℝ)) := by
  apply hAB.ruzsa_sum_grid hBC hδ (by exact_mod_cast Finset.card_pos.mpr hB)
  rw [Finset.card_image_iff.mpr (realGridIndex_injective hδ hsep)]

theorem RealCoverBound.ruzsa_sum_scaled {δ t M N : ℝ} {A B C : Finset ℝ}
    (hAB : RealCoverBound δ (A + realScalarImage t B) M)
    (hBC : RealCoverBound δ (realScalarImage t B + C) N)
    (hδ : 0 < δ) (ht : 0 < t) (ht1 : t ≤ 1) (hB : B.Nonempty)
    (hsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y) :
    RealCoverBound δ (A + C) (144 * M * N / (t * (B.card : ℝ))) := by
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  have hgrid : t * (B.card : ℝ) / 4 ≤
      (((realScalarImage t B).image (realGridIndex δ)).card : ℝ) := by
    have hh := scaled_grid_card_lower hδ ht ht1 B hsep
    dsimp only [realScalarImage]
    linarith
  have hh := hAB.ruzsa_sum_grid hBC hδ (by positivity : 0 < t * (B.card : ℝ) / 4) hgrid
  convert hh using 1 <;> ring

/-- One small rectangular projection controls both self-sum sets. -/
theorem rectangular_projection_self_sums (A B : Finset ℝ) {δ t M : ℝ}
    (hδ : 0 < δ) (ht : 0 < t) (ht1 : t ≤ 1) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y)
    (hcov : RealCoverBound δ (A + realScalarImage t B) M) :
    RealCoverBound δ (A + A) (144 * M ^ 2 / (t * (B.card : ℝ))) ∧
      RealCoverBound δ (B + B) (108 * M ^ 2 / (t * (A.card : ℝ))) := by
  have hcov' : RealCoverBound δ (realScalarImage t B + A) M := by simpa only [add_comm] using hcov
  constructor
  · have hh := hcov.ruzsa_sum_scaled hcov' hδ ht ht1 hB hBsep
    convert hh using 1 <;> ring
  · have hh := hcov'.ruzsa_sum_separated hcov hδ hA hAsep
    have hinv : 1 ≤ 1 / t := (le_div_iff₀ ht).mpr (by simpa using ht1)
    have hh' := hh.scale hδ hinv (show |1 / t| ≤ 1 / t by rw [abs_of_pos (by positivity)])
    change RealCoverBound δ
      (realScalarImage (1 / t) (realScalarImage t B + realScalarImage t B)) _ at hh'
    rw [realScalarImage_add, realScalarImage_mul, show 1 / t * t = 1 by field_simp,
      realScalarImage_one] at hh'
    convert hh' using 1 <;> ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
