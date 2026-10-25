-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GridFrostmanLower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GridQuantization
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.CartesianFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoverCounting

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- The number of occupied grid cells has the usual Frostman lower bound. -/
theorem RealFiniteFrostman.grid_card_lower {δ C σ : ℝ} {A : Finset ℝ}
    (hAF : RealFiniteFrostman δ C σ A) (hδ : 0 < δ) (hA : A.Nonempty) :
    1 ≤ ((A.image (realGridIndex δ)).card : ℝ) * C * δ ^ σ := by
  classical
  let G := A.image (realGridIndex δ)
  let e := Fintype.equivFin G
  let cc (i : Fin (Fintype.card G)) := δ * ((e.symm i).1 : ℝ)
  have hcov : Covers δ (↑A : Set ℝ) cc := by
    intro a ha
    have hag : realGridIndex δ a ∈ G := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    refine Set.mem_iUnion.mpr ⟨e ⟨realGridIndex δ a, hag⟩, ?_⟩
    change dist a (δ * ((e.symm (e ⟨realGridIndex δ a, hag⟩)).1 : ℝ)) ≤ δ
    rw [Equiv.symm_apply_apply, Real.dist_eq, abs_of_nonneg (realGridIndex_error hδ a).1]
    exact (realGridIndex_error hδ a).2.le
  have hcount := WangZahlLot.Obl.wz_separated_projection_dichotomy.card_le_cover_mul_fiber_bound A id
    (show Covers δ (id '' (↑A : Set ℝ)) cc by simpa only [Set.image_id] using hcov)
    (fun i => hAF (cc i) δ le_rfl)
  rw [Fintype.card_coe] at hcount
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  apply (mul_le_mul_iff_left₀ hAp).mp
  convert hcount using 1 <;> ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
