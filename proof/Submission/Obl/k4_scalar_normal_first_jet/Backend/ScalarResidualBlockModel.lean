/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarResidualBlockModel.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarResidualBlockModel.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAffineResidualModel
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarShearCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry

/-! Residual slope observations on the actual left-normalized time block. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set

theorem original_left_block_residual_model {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (F : ℝ → ℝ) (l : Λ) (s a slope : ℝ) (bin : ℤ)
    {H p K anchor u : ℝ} (hH : 0 < H) (hHp : H ≤ p) (hp1 : p ≤ 1) (hK : 1 ≤ K)
    (hanchor : anchor ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hbounded : D.Bounded K l) (hcunit : s + H * anchor ∈ Icc (0 : ℝ) 1)
    (hF : |F (s + H * anchor)| ≤ K) (hslope : |slope| ≤ K)
    (hrow₀ : |F (s + H * anchor) - (a + slope * (s + H * anchor))| ≤ K * H * p)
    (hrow : |F (s + H * u) - (a + slope * (s + H * u))| ≤ K * H * p) :
    let c := s + H * anchor
    let k := D.residual F l c - slope * D.y l c
    |(D.scalar F l (s + H * u) - H * bin) / H -
      (((D.scalar F l c - H * bin) / H - anchor * k) + u * k)| ≤ 16 * K ^ 2 * p ∧
    |scalarFirstJet D F (fun _ => slope) l (s + H * u) -
      scalarFirstJet D F (fun _ => slope) l c| ≤ 6 * K ^ 2 * H ∧ |k| ≤ 6 * K ^ 2 := by
  dsimp only
  let c := s + H * anchor
  have huc : |u - anchor| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hanchor.1, hanchor.2]
  have he : c + H * (u - anchor) = s + H * u := by dsimp [c]; ring
  obtain ⟨_, hY, hR, _⟩ := D.bounds_at_unit_time hK hbounded hcunit hF
  have hmodel := original_affine_row_residual_model D F l c (H * bin) a slope
    hH hHp hp1 hK huc hbounded.2.2.1 hbounded.2.2.2.2 hY hslope hrow₀
    (by simpa only [he] using hrow)
  rw [he] at hmodel
  have hproduct : |slope * D.y l c| ≤ 2 * K ^ 2 := by
    rw [abs_mul]
    have hh := mul_le_mul hslope hY (abs_nonneg _) (zero_le_one.trans hK)
    nlinarith
  refine ⟨?_, hmodel.2, ?_⟩
  · dsimp only [c] at hmodel
    convert hmodel.1 using 1 <;> congr 1 <;> ring
  · exact (abs_sub _ _).trans (by linarith)

theorem original_frozen_first_jet_spread {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (F : ℝ → ℝ) (A : Set Λ) (c slope : ℝ)
    {K H p ζ : ℝ} (hK : 1 ≤ K) (hH : 0 < H) (hHp : H ≤ p) (hζH : ζ ≤ H)
    (hF : |F c| ≤ K) (hslope : |slope| ≤ K)
    (hS : ∀ l ∈ A, ∀ l' ∈ A,
      |D.scalar F l c - D.scalar F l' c| ≤ H)
    (hR : ∀ l ∈ A, ∀ l' ∈ A,
      |D.residual F l c - D.residual F l' c| ≤
        K * (|D.x l c - D.x l' c| + |D.y l c - D.y l' c| + ζ))
    {l l' : Λ} (hl : l ∈ A) (hl' : l' ∈ A)
    (hcode : (⌊D.y l c / p⌋ : ℤ) = ⌊D.y l' c / p⌋) :
    |scalarFirstJet D F (fun _ => slope) l c -
      scalarFirstJet D F (fun _ => slope) l' c| ≤ 7 * K ^ 2 * p := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hp : 0 < p := hH.trans_le hHp
  have hzero : |(0 : ℝ)| ≤ K := by simpa using hK0
  have hspread := scalar_frozen_residual_comparison A (fun l => D.x l c)
    (fun l => D.y l c) (fun _ => 0) (fun l => D.residual F l c)
    hK0 hH.le hζH hF hzero
    (by simpa only [zero_mul, sub_zero, ScalarMotion.scalar] using hS)
    (by simpa only [sub_self, abs_zero, add_zero] using hR) l hl l' hl'
  simp only [sub_self, abs_zero, add_zero] at hspread
  have hy := same_mesh_cell_close hp hcode
  have hcoef : 2 * K + K ^ 2 ≤ 3 * K ^ 2 := by nlinarith [hK]
  have hRbound : |D.residual F l c - D.residual F l' c| ≤ 6 * K ^ 2 * p := by
    have hh := mul_le_mul hcoef (show |D.y l c - D.y l' c| + H ≤ 2 * p by linarith)
      (by positivity : 0 ≤ |D.y l c - D.y l' c| + H) (by positivity : 0 ≤ 3 * K ^ 2)
    nlinarith
  have hYbound : |slope * (D.y l c - D.y l' c)| ≤ K ^ 2 * p := by
    rw [abs_mul]
    have hh := mul_le_mul hslope hy (abs_nonneg _) hK0
    have hKK : K * p ≤ K ^ 2 * p := mul_le_mul_of_nonneg_right (by nlinarith : K ≤ K ^ 2) hp.le
    exact hh.trans hKK
  have he : scalarFirstJet D F (fun _ => slope) l c -
      scalarFirstJet D F (fun _ => slope) l' c =
      (D.residual F l c - D.residual F l' c) - slope * (D.y l c - D.y l' c) := by
    dsimp [scalarFirstJet]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
