-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ProductTripleCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealPlunnecke
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealCoverAlgebra

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products


open scoped Pointwise

/-- Small product doubling controls the sum of the original set and two
product sets, at three times the original radius. -/
theorem product_triple_cover {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (A : Finset ℝ) (hA1 : (1 : ℝ) ∈ A)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hsmall : RealCoverBound δ (A * A + A * A) (K * (A.card : ℝ))) :
    RealCoverBound (3 * δ) (A + (A * A + A * A)) (216 * K ^ 3 * (A.card : ℝ)) := by
  classical
  obtain ⟨m, cc, hc, hm⟩ := hsmall
  have hAne : A.Nonempty := ⟨1, hA1⟩
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hAne
  obtain ⟨n, centers, hcover, hn⟩ := real_plunnecke_cover hδ (A * A) (hAne.mul hAne) cc hc 3 0
  norm_num only [Nat.add_zero, Nat.cast_ofNat, zero_nsmul, sub_zero] at hcover hn
  have hsub : A ⊆ A * A := by
    intro a ha
    simpa only [one_mul] using Finset.mul_mem_mul hA1 ha
  have hG : (A.card : ℝ) ≤ (((A * A).image (realGridIndex δ)).card : ℝ) := by
    have hh := Finset.card_le_card (Finset.image_subset_image (f := realGridIndex δ) hsub)
    rw [Finset.card_image_iff.mpr (realGridIndex_injective hδ hsep)] at hh
    exact_mod_cast hh
  have hGp : (0 : ℝ) < ((A * A).image (realGridIndex δ)).card := hAp.trans_le hG
  have hlong : A + (A * A + A * A) ⊆ (3 : ℕ) • (A * A) := by
    have hs := Finset.add_subset_add hsub (Finset.Subset.rfl : A * A + A * A ⊆ A * A + A * A)
    have hid : (3 : ℕ) • (A * A) = A * A + (A * A + A * A) := by
      rw [show (3 : ℕ) = 1 + 2 by decide, add_nsmul, one_nsmul, two_nsmul]
    rwa [hid]
  refine ⟨n, centers, hcover.mono_set hlong, ?_⟩
  have hden : (n : ℝ) * (((A * A).image (realGridIndex δ)).card : ℝ) ^ 2 ≤ (6 * (m : ℝ)) ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hn (sq_nonneg (((A * A).image (realGridIndex δ)).card : ℝ))
    convert hh using 1 <;> field_simp
  have hmul : (n : ℝ) * (A.card : ℝ) ^ 2 ≤ (216 * K ^ 3 * (A.card : ℝ)) * (A.card : ℝ) ^ 2 := by
    calc
      (n : ℝ) * (A.card : ℝ) ^ 2 ≤ (n : ℝ) * (((A * A).image (realGridIndex δ)).card : ℝ) ^ 2 := by gcongr
      _ ≤ (6 * (m : ℝ)) ^ 3 := hden
      _ ≤ (6 * (K * (A.card : ℝ))) ^ 3 := by gcongr
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hAp)).mp hmul

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
