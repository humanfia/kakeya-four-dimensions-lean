-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RealPlunnecke.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GridIteratedSums
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

theorem grid_sum_card_le {δ : ℝ} (hδ : 0 < δ) (B : Finset ℝ)
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers δ (↑(B + B) : Set ℝ) cc) :
    (((B.image (realGridIndex δ)) + (B.image (realGridIndex δ))).card : ℝ) ≤ 6 * (m : ℝ) := by
  classical
  have hcov' : Covers δ ((fun p : ℝ × ℝ => p.1 + p.2) '' (↑(B ×ˢ B) : Set (ℝ × ℝ))) cc := by
    rintro x ⟨p, hp, rfl⟩
    exact hcov (Finset.add_mem_add (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2)
  obtain ⟨S, hSc, hS⟩ := grid_sums_of_cover hδ (B ×ˢ B) cc hcov'
  have hsub : B.image (realGridIndex δ) + B.image (realGridIndex δ) ⊆ S := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hS (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)
  have hc : ((B.image (realGridIndex δ) + B.image (realGridIndex δ)).card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans hSc

/-- Plunnecke's inequality for real covers. Its cardinality bound is at the
original grid scale, and the output radius grows linearly with the number
of summands. -/
theorem real_plunnecke_cover {δ : ℝ} (hδ : 0 < δ) (B : Finset ℝ) (hB : B.Nonempty)
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers δ (↑(B + B) : Set ℝ) cc) (k l : ℕ) :
    ∃ (n : ℕ) (centers : Fin n → ℝ),
      Covers (((k + l : ℕ) : ℝ) * δ) (↑(k • B - l • B) : Set ℝ) centers ∧
      (n : ℝ) ≤ (6 * (m : ℝ) / (B.image (realGridIndex δ)).card) ^ (k + l) *
        (B.image (realGridIndex δ)).card := by
  classical
  let G := B.image (realGridIndex δ)
  have hG : G.Nonempty := hB.image _
  have hGc : (0 : ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hG
  have hsum := grid_sum_card_le hδ B cc hcov
  obtain ⟨n, centers, hcover, hn⟩ := cover_of_grid_nsmul_sub_nsmul hδ B k l
  refine ⟨n, centers, hcover, ?_⟩
  rw [hn]
  have hp : ((k • G - l • G).card : ℝ) ≤
      (((G + G).card : ℝ) / (G.card : ℝ)) ^ (k + l) * (G.card : ℝ) := by
    have hh := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hG G k l
    have hh' := (NNRat.cast_le (K := ℝ)).mpr hh
    push_cast at hh'
    exact hh'
  apply hp.trans
  gcongr

/-- A denominator-free form for the nine-term expression used below. -/
theorem real_plunnecke_nine {δ : ℝ} (hδ : 0 < δ) (B : Finset ℝ) (hB : B.Nonempty)
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers δ (↑(B + B) : Set ℝ) cc) :
    ∃ (n : ℕ) (centers : Fin n → ℝ), Covers (9 * δ) (↑((5 : ℕ) • B - (4 : ℕ) • B) : Set ℝ) centers ∧
      (n : ℝ) * ((B.image (realGridIndex δ)).card : ℝ) ^ 8 ≤ (6 * (m : ℝ)) ^ 9 := by
  obtain ⟨n, centers, hcover, hn⟩ := real_plunnecke_cover hδ B hB cc hcov 5 4
  norm_num only at hcover hn
  refine ⟨n, centers, hcover, ?_⟩
  have hG : (0 : ℝ) < (B.image (realGridIndex δ)).card := by
    exact_mod_cast Finset.card_pos.mpr (hB.image _)
  have hh := mul_le_mul_of_nonneg_right hn (by positivity :
    0 ≤ ((B.image (realGridIndex δ)).card : ℝ) ^ 8)
  convert hh using 1
  field_simp

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
