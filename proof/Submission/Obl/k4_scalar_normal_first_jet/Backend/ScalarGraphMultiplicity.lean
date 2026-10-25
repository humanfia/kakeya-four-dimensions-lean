/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGraphMultiplicity.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGraphMultiplicity.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedGraphCovers
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCovers

/-! Explicit multiplicities of the original indexed scalar collision graphs. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set Metric
open WangZahlLot.Obl.wz_slab_local_linearity

theorem grid_list_multiplicity {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (K : Finset ℤ) (t : ℤ → ℝ) (hgrid : ∀ k ∈ K, ⌊t k / p⌋ = k) :
    ∀ k ∈ K, ((K.filter fun k' => |t k - t k'| ≤ C * p).card : ℝ) ≤ 2 * C + 3 := by
  classical
  intro k hk
  have h := CellProofs.card_le_of_subset_Icc_int (a := (k : ℝ) - (C + 1))
    (L := 2 * (C + 1)) (by linarith) (K.filter fun k' => |t k - t k'| ≤ C * p) (by
      intro k' hk'
      obtain ⟨hk'K, hclose⟩ := Finset.mem_filter.mp hk'
      have hi := mesh_index_close hp hclose
      rw [hgrid k hk, hgrid k' hk'K] at hi
      obtain ⟨hlo, hhi⟩ := abs_le.mp hi
      constructor <;> linarith)
  linarith

theorem graph_grid_multiplicity {p : ℝ} (hp : 0 < p) (K : Finset ℤ)
    (t : ℤ → ℝ) (f : ℝ → ℝ) (hgrid : ∀ k ∈ K, ⌊t k / p⌋ = k) :
    ∀ k ∈ K, ((K.filter fun k' =>
      dist (graphPoint f (t k)) (graphPoint f (t k')) ≤ 4 * p).card : ℝ) ≤ 11 := by
  classical
  intro k hk
  have hcap₀ := grid_list_multiplicity (C := 4) hp (by norm_num) K t hgrid k hk
  have hcap : ((K.filter fun k' => |t k - t k'| ≤ 4 * p).card : ℝ) ≤ 11 := by
    linarith only [hcap₀]
  apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans hcap
  intro k' hk'
  obtain ⟨hk'K, hd⟩ := Finset.mem_filter.mp hk'
  have hi := scalarPlane_coordinate_dist_le (graphPoint f (t k)) (graphPoint f (t k')) 0
  change |t k - t k'| ≤ dist (graphPoint f (t k)) (graphPoint f (t k')) at hi
  exact Finset.mem_filter.mpr ⟨hk'K, hi.trans hd⟩

theorem boxedDiagonalPoint_original_dist_le {B : ℝ} (hB : 0 < B)
    (e : ℝ) (he : e ^ 2 = 1) (u v u' v' : ℝ) :
    dist (!₂[u, v] : ScalarPlane) !₂[u', v'] ≤
      4 * B * dist (boxedDiagonalPoint e B u v) (boxedDiagonalPoint e B u' v') := by
  have htwo : 0 < 2 * B := mul_pos (by norm_num) hB
  have hbox : dist (boxedDiagonalPoint e B u v) (boxedDiagonalPoint e B u' v') =
      (2 * B)⁻¹ * dist (diagonalPoint e u v) (diagonalPoint e u' v') := by
    unfold boxedDiagonalPoint
    rw [dist_add_right, dist_smul₀]
    simp only [Real.norm_eq_abs, abs_inv, abs_of_pos htwo]
  have hdiag : dist (diagonalPoint e u v) (diagonalPoint e u' v') =
      (2 * B) * dist (boxedDiagonalPoint e B u v) (boxedDiagonalPoint e B u' v') := by
    rw [hbox, ← mul_assoc, mul_inv_cancel₀ htwo.ne', one_mul]
  calc
    _ ≤ 2 * dist (diagonalPoint e u v) (diagonalPoint e u' v') :=
      diagonalPoint_original_dist_le e he u v u' v'
    _ = _ := by rw [hdiag]; ring

theorem boxed_grid_multiplicity {p B : ℝ} (hp : 0 < p) (hB : 0 < B)
    (e : ℝ) (he : e ^ 2 = 1) (J : Finset ℤ) (v : ℤ → ℝ) (G : ℝ → ℝ)
    (hgrid : ∀ j ∈ J, ⌊v j / p⌋ = j) :
    ∀ j ∈ J, ((J.filter fun j' => dist (boxedDiagonalPoint e B (G (v j)) (v j))
      (boxedDiagonalPoint e B (G (v j')) (v j')) ≤ 2 * p).card : ℝ) ≤ 16 * B + 3 := by
  classical
  intro j hj
  have hcap := grid_list_multiplicity (C := 8 * B) hp (by linarith) J v hgrid j hj
  have hsub : (J.filter fun j' => dist (boxedDiagonalPoint e B (G (v j)) (v j))
      (boxedDiagonalPoint e B (G (v j')) (v j')) ≤ 2 * p) ⊆
      J.filter (fun j' => |v j - v j'| ≤ (8 * B) * p) := by
    intro j' hj'
    obtain ⟨hj'J, hd⟩ := Finset.mem_filter.mp hj'
    have hi := scalarPlane_coordinate_dist_le (!₂[G (v j), v j] : ScalarPlane)
      (!₂[G (v j'), v j'] : ScalarPlane) 1
    change |v j - v j'| ≤ dist (!₂[G (v j), v j] : ScalarPlane) !₂[G (v j'), v j'] at hi
    have hinv := boxedDiagonalPoint_original_dist_le hB e he (G (v j)) (v j) (G (v j')) (v j')
    have hmul := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ 4 * B)
    refine Finset.mem_filter.mpr ⟨hj'J, ?_⟩
    nlinarith only [hi, hinv, hmul]
  have h := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcap
  linarith

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
