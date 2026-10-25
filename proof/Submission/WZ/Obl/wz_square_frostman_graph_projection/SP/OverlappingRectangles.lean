-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.OverlappingRectangles.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.CoverRuzsaBounds

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- Large overlaps transfer small projection covers to a fixed rectangle
whose two self-sum sets have small covers. -/
theorem overlapping_rectangle_projection (A B X Y : Finset ℝ) {δ t K L M : ℝ}
    (hδ : 0 < δ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hU : (A ∩ X).Nonempty) (hV : (B ∩ Y).Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y)
    (hAA : RealCoverBound δ (A + A) K) (hBB : RealCoverBound δ (B + B) L)
    (hXY : RealCoverBound δ (X + realScalarImage t Y) M) :
    RealCoverBound δ (A + realScalarImage t B)
      (5184 * K * L * M / (t * ((A ∩ X).card : ℝ) * ((B ∩ Y).card : ℝ))) := by
  classical
  let U := A ∩ X
  let V := B ∩ Y
  have hUV : RealCoverBound δ (U + realScalarImage t V) M := hXY.mono (by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.add_mem_add (Finset.mem_inter.mp hx).2
      (Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).2, rfl⟩)) le_rfl
  have hBB' : RealCoverBound δ (realScalarImage t B + realScalarImage t B) L := by
    have hh := hBB.scale_contract hδ.le (show |t| ≤ 1 by rwa [abs_of_pos ht])
    change RealCoverBound δ (realScalarImage t (B + B)) L at hh
    rwa [realScalarImage_add] at hh
  have hVB : RealCoverBound δ (realScalarImage t V + realScalarImage t B) L := hBB'.mono (by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.add_mem_add (Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).1, rfl⟩) hy) le_rfl
  have hUB := hUV.ruzsa_sum_scaled hVB hδ ht ht1 hV
    (fun x hx y hy hne => hBsep x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1 hne)
  have hAU : RealCoverBound δ (A + U) K := hAA.mono (by
    intro z hz
    obtain ⟨a, ha, u, hu, rfl⟩ := Finset.mem_add.mp hz
    exact Finset.add_mem_add ha (Finset.mem_inter.mp hu).1) le_rfl
  have hh := hAU.ruzsa_sum_separated hUB hδ hU
    (fun x hx y hy hne => hAsep x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1 hne)
  convert hh using 1 <;> dsimp only [U, V] <;> ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
