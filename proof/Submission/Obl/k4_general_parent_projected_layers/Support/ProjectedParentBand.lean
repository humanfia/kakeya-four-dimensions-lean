/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ProjectedParentBand.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedCellCap
import Submission.Obl.k4_general_parent_projected_layers.Support.TerminalSupport
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! A parent contributes a moving projected band of area O(K^2 q^2). -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Set

noncomputable section

theorem major_motion_error {chi z₀ z₁ t : ℝ} (hc : 0 ≤ chi)
    (b : Fin 6 → ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hb : b ∈ majorGroup chi z₀ z₁) :
    |basePoint b t 1 - z₀ - t * z₁| ≤ 2 * chi := by
  have h := (projectedCell_mem_movingBox (sigma := 1) (g := 1) (y₀ := 0) (y₁ := 0)
    (by norm_num) (by norm_num) hc b (projectedCell 1 1 0 0 b t) ht hb rfl).2 0
  change |basePoint b t 1 - (z₀ + t * z₁)| ≤ 2 * chi at h
  simpa only [sub_add_eq_sub_sub] using h

theorem projected_parent_band {K q g chi y₀ y₁ z₀ z₁ t : ℝ}
    (c : Fin 5 → ℝ) (b : Fin 6 → ℝ) (hK : 0 ≤ K) (hg : 0 < g)
    (hc : 0 ≤ chi) (hcq : chi ≤ q * g) (hc₄ : |c 4| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hb : b ∈ majorGroup chi z₀ z₁)
    (hy : |basePoint b t 2 - c 2 - t * c 3 - c 4 * basePoint b t 1| ≤ K * q * g) :
    |(basePoint b t 2 - y₀ - t * y₁) / g -
      ((c 2 + c 4 * z₀ - y₀) / g + t * ((c 3 + c 4 * z₁ - y₁) / g))| ≤ 3 * K * q := by
  have hz := major_motion_error hc b ht hb
  have heq : (basePoint b t 2 - y₀ - t * y₁) / g -
      ((c 2 + c 4 * z₀ - y₀) / g + t * ((c 3 + c 4 * z₁ - y₁) / g)) =
      ((basePoint b t 2 - c 2 - t * c 3 - c 4 * basePoint b t 1) +
        c 4 * (basePoint b t 1 - z₀ - t * z₁)) / g := by ring
  rw [heq, abs_div, abs_of_pos hg, div_le_iff₀ hg]
  calc
    _ ≤ |basePoint b t 2 - c 2 - t * c 3 - c 4 * basePoint b t 1| +
        |c 4| * |basePoint b t 1 - z₀ - t * z₁| := by
      simpa only [abs_mul] using abs_add_le
        (basePoint b t 2 - c 2 - t * c 3 - c 4 * basePoint b t 1)
        (c 4 * (basePoint b t 1 - z₀ - t * z₁))
    _ ≤ K * q * g + K * (2 * chi) := add_le_add hy
      (mul_le_mul hc₄ hz (abs_nonneg _) hK)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcq hK]

theorem projected_parent_band_velocity {K g chi y₁ z₀ z₁ : ℝ}
    (c : Fin 5 → ℝ) (b : Fin 6 → ℝ) (hK : 1 ≤ K) (hg : 0 < g)
    (hcg : chi ≤ g) (hc₄ : |c 4| ≤ K) (hb : b ∈ majorGroup chi z₀ z₁)
    (hrow : |b 4 - c 3 - c 4 * b 3| ≤ K * g) (hcrop : |b 4 - y₁| ≤ g) :
    |(c 3 + c 4 * z₁ - y₁) / g| ≤ 3 * K := by
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  have hmajor : |z₁ - b 3| ≤ chi := by simpa only [abs_sub_comm] using hb.2
  rw [abs_div, abs_of_pos hg, div_le_iff₀ hg]
  calc
    _ = |-(b 4 - c 3 - c 4 * b 3) + c 4 * (z₁ - b 3) + (b 4 - y₁)| := by congr 1; ring
    _ ≤ |-(b 4 - c 3 - c 4 * b 3)| + |c 4 * (z₁ - b 3)| + |b 4 - y₁| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K * g + K * chi + g := by
      simp only [abs_neg, abs_mul]
      exact add_le_add (add_le_add hrow (mul_le_mul hc₄ hmajor (abs_nonneg _) hK0)) hcrop
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcg hK0,
      mul_le_mul_of_nonneg_right hK hg.le]

theorem projected_parent_cell_cover {K q g chi sigma y₀ y₁ z₀ z₁ tmid : ℝ}
    (c : Fin 5 → ℝ) (hK : 1 ≤ K) (hg : 0 < g) (hc : 0 ≤ chi)
    (hcq : chi ≤ q * g) (hc₄ : |c 4| ≤ K) (hs : 0 < sigma) (hsq : sigma ≤ q)
    (hv : |(c 3 + c 4 * z₁ - y₁) / g| ≤ 3 * K) :
    ∃ F : Finset (Fin 2 → ℤ), (F.card : ℝ) * sigma ^ 2 ≤ 7200 * K ^ 2 * q ^ 2 ∧
      ∀ (b : Fin 6 → ℝ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → |t - tmid| ≤ q →
        b ∈ majorGroup chi z₀ z₁ →
        |basePoint b t 2 - c 2 - t * c 3 - c 4 * basePoint b t 1| ≤ K * q * g →
          projectedCell sigma g y₀ y₁ b t ∈ F := by
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  have hq : 0 ≤ q := hs.le.trans hsq
  obtain ⟨F, hF, hcover⟩ := planar_moving_mesh_cover (width := 3 * K * q)
    (L := 3 * K) hs hsq (by positivity)
    (by nlinarith [mul_nonneg (sub_nonneg.mpr hK) hq])
    (mul_le_mul_of_nonneg_left hsq (by positivity)) tmid
    ((c 2 + c 4 * z₀ - y₀) / g) ((c 3 + c 4 * z₁ - y₁) / g) hv
  refine ⟨F, ?_, ?_⟩
  · exact hF.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg hK0 (sq_nonneg q))])
  · intro b t ht htmid hb hy
    have hf := hcover ![t, (basePoint b t 2 - y₀ - t * y₁) / g] htmid
      (projected_parent_band c b hK0 hg hc hcq hc₄ ht hb hy)
    have heq : (fun e : Fin 2 => ⌊(![t, (basePoint b t 2 - y₀ - t * y₁) / g] : Fin 2 → ℝ) e / sigma⌋) =
        projectedCell sigma g y₀ y₁ b t := by
      ext e
      fin_cases e <;> rfl
    rwa [heq] at hf

end

end Submission.Obl.k4_general_parent_projected_layers
