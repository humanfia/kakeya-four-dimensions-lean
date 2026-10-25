-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GridIntersectionSum.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealRuzsaSum
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RectangularScalarTransfer

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- A large intersection of occupied grid cells transfers small doubling
to a small mixed sum. -/
theorem grid_intersection_small_sum (X Y : Finset ℝ) {δ d N K : ℝ}
    (hδ : 0 < δ) (hd : 0 < d) (hN : 0 < N) (hK : 0 ≤ K)
    (hX : RealCoverBound δ (X + X) (K * N))
    (hY : RealCoverBound δ (Y + Y) (K * N))
    (hcommon : d * N ≤ ((X.image (realGridIndex δ) ∩ Y.image (realGridIndex δ)).card : ℝ)) :
    RealCoverBound δ (X + Y) ((36 * K ^ 2 / d) * N) := by
  classical
  obtain ⟨m, ca, hca, hm⟩ := hX
  obtain ⟨n, cb, hcb, hn⟩ := hY
  let G := X.image (realGridIndex δ)
  let H := Y.image (realGridIndex δ)
  let D := G ∩ H
  obtain ⟨k, cc, hc, hk⟩ := cover_of_grid_sum hδ X Y
  have hleft : ((G + D).card : ℝ) ≤ 6 * (m : ℝ) := by
    have hsub : G + D ⊆ G + G := Finset.add_subset_add Finset.Subset.rfl Finset.inter_subset_left
    exact (show ((G + D).card : ℝ) ≤ ((G + G).card : ℝ) by
      exact_mod_cast Finset.card_le_card hsub).trans (grid_mixed_sum_card_le hδ X X ca hca)
  have hright : ((D + H).card : ℝ) ≤ 6 * (n : ℝ) := by
    have hsub : D + H ⊆ H + H := Finset.add_subset_add Finset.inter_subset_right Finset.Subset.rfl
    exact (show ((D + H).card : ℝ) ≤ ((H + H).card : ℝ) by
      exact_mod_cast Finset.card_le_card hsub).trans (grid_mixed_sum_card_le hδ Y Y cb hcb)
  have ht : (k : ℝ) * (D.card : ℝ) ≤ ((G + D).card : ℝ) * ((D + H).card : ℝ) := by
    rw [hk]
    exact_mod_cast Finset.ruzsa_triangle_inequality_add_add_add G D H
  have ht' : (k : ℝ) * (D.card : ℝ) ≤ 36 * (m : ℝ) * (n : ℝ) := by
    have hh := mul_le_mul hleft hright (Nat.cast_nonneg _) (by positivity)
    nlinarith
  have hprod : (m : ℝ) * (n : ℝ) ≤ (K * N) * (K * N) :=
    mul_le_mul hm hn (Nat.cast_nonneg _) (by positivity)
  have hlow := mul_le_mul_of_nonneg_left hcommon (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hlast : ((k : ℝ) * d) * N ≤ (36 * K ^ 2 * N) * N := by
    change (k : ℝ) * (d * N) ≤ (k : ℝ) * (D.card : ℝ) at hlow
    nlinarith
  have hcancel := (mul_le_mul_iff_left₀ hN).mp hlast
  refine ⟨k, cc, hc, ?_⟩
  have hh := (le_div_iff₀ hd).mpr hcancel
  convert hh using 1 <;> ring

/-- A popular multiplier produces a small scalar projection after
normalizing by the anchor. -/
theorem common_multiplier_small_projection (A : Finset ℝ) {δ c a₀ a d K : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (ha₀ : c ≤ a₀) (ha₀1 : a₀ ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hd : 0 < d) (hK : 0 ≤ K) (hA : A.Nonempty)
    (hAdd : RealCoverBound δ (A + A) (K * (A.card : ℝ)))
    (hcommon : d * (A.card : ℝ) ≤
      (((realScalarImage a₀ A).image (realGridIndex δ) ∩
        (realScalarImage a A).image (realGridIndex δ)).card : ℝ)) :
    SmallScalarProjection δ A (108 * K ^ 2 / (c * d)) (a / a₀) := by
  classical
  have ha₀p : 0 < a₀ := hc.trans_le ha₀
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hX : RealCoverBound δ (realScalarImage a₀ A + realScalarImage a₀ A) (K * (A.card : ℝ)) := by
    have hh := hAdd.scale_contract hδ.le (by rwa [abs_of_pos ha₀p])
    change RealCoverBound δ (realScalarImage a₀ (A + A)) _ at hh
    rwa [realScalarImage_add] at hh
  have hY : RealCoverBound δ (realScalarImage a A + realScalarImage a A) (K * (A.card : ℝ)) := by
    have hh := hAdd.scale_contract hδ.le (by rwa [abs_of_nonneg ha])
    change RealCoverBound δ (realScalarImage a (A + A)) _ at hh
    rwa [realScalarImage_add] at hh
  have hsum := grid_intersection_small_sum (realScalarImage a₀ A) (realScalarImage a A)
    hδ hd hAp hK hX hY hcommon
  have haInv : 1 ≤ 1 / a₀ := (le_div_iff₀ ha₀p).mpr (by simpa using ha₀1)
  have hh := hsum.scale hδ haInv (show |1 / a₀| ≤ 1 / a₀ by rw [abs_of_pos (by positivity)])
  change RealCoverBound δ (realScalarImage (1 / a₀) (realScalarImage a₀ A + realScalarImage a A)) _ at hh
  rw [realScalarImage_add, realScalarImage_mul, realScalarImage_mul,
    show 1 / a₀ * a₀ = 1 by field_simp, realScalarImage_one,
    show 1 / a₀ * a = a / a₀ by ring] at hh
  apply hh.mono Finset.Subset.rfl
  calc
    3 * (1 / a₀) * (36 * K ^ 2 / d * (A.card : ℝ)) =
        (108 * K ^ 2 / (a₀ * d)) * (A.card : ℝ) := by ring
    _ ≤ (108 * K ^ 2 / (c * d)) * (A.card : ℝ) := by gcongr

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
