/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ProjectedGroupLists.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.MeshProjection
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Compatible original coefficient bins for one true parent. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Set

noncomputable section

theorem major_intercept_mesh_cover {K q chi tmid center velocity : ℝ}
    (hK : 1 ≤ K) (hq : 0 ≤ q) (hchi : 0 < chi) (hchiq : chi ≤ q)
    (ht : tmid ∈ Icc (0 : ℝ) 1) :
    ∃ F : Finset ℤ, (F.card : ℝ) * chi ≤ 10 * K * q ∧
      ∀ b₀ b₃ : ℝ, |b₀ + tmid * b₃ - center| ≤ K * q → |b₃ - velocity| ≤ chi →
        ⌊b₀ / chi⌋ ∈ F := by
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  obtain ⟨F, hF, hcover⟩ := interval_mesh_cover hchi (by positivity : 0 ≤ 2 * K * q)
    (center - tmid * velocity)
  refine ⟨F, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right hF hchi.le
    have heq : (4 * (2 * K * q) / chi + 2) * chi = 8 * K * q + 2 * chi := by field_simp <;> ring
    rw [heq] at h
    nlinarith [mul_le_mul_of_nonneg_right hK hq]
  · intro b₀ b₃ hb hvel
    apply hcover b₀
    have ht1 : |tmid| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
    calc
      _ = |(b₀ + tmid * b₃ - center) + (-tmid * (b₃ - velocity))| := by congr 1; ring
      _ ≤ |b₀ + tmid * b₃ - center| + |tmid| * |b₃ - velocity| := by
        simpa only [abs_mul, abs_neg] using abs_add_le
          (b₀ + tmid * b₃ - center) (-tmid * (b₃ - velocity))
      _ ≤ K * q + 1 * chi := add_le_add hb (mul_le_mul ht1 hvel (abs_nonneg _) (by norm_num))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hK hq]

theorem transverse_slope_mesh_cover {K g chi c₃ c₄ velocity : ℝ}
    (hK : 1 ≤ K) (hg : 0 < g) (hchig : chi ≤ g) (hc₄ : |c₄| ≤ K) :
    ∃ F : Finset ℤ, (F.card : ℝ) ≤ 10 * K ∧
      ∀ b₃ b₄ : ℝ, |b₃ - velocity| ≤ chi → |b₄ - c₃ - c₄ * b₃| ≤ K * g →
        ⌊b₄ / g⌋ ∈ F := by
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  obtain ⟨F, hF, hcover⟩ := interval_mesh_cover hg (by positivity : 0 ≤ 2 * K * g)
    (c₃ + c₄ * velocity)
  refine ⟨F, ?_, ?_⟩
  · have heq : 4 * (2 * K * g) / g + 2 = 8 * K + 2 := by field_simp <;> ring
    rw [heq] at hF
    linarith
  · intro b₃ b₄ hvel hrow
    apply hcover b₄
    calc
      _ = |(b₄ - c₃ - c₄ * b₃) + c₄ * (b₃ - velocity)| := by congr 1; ring
      _ ≤ |b₄ - c₃ - c₄ * b₃| + |c₄| * |b₃ - velocity| := by
        simpa only [abs_mul] using abs_add_le (b₄ - c₃ - c₄ * b₃) (c₄ * (b₃ - velocity))
      _ ≤ K * g + K * chi := add_le_add hrow (mul_le_mul hc₄ hvel (abs_nonneg _) hK0)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hchig hK0]

theorem transverse_intercept_mesh_cover {K q g chi tmid c₂ c₃ c₄ z₀ z₁ y₁ : ℝ}
    (hK : 1 ≤ K) (hq1 : q ≤ 1) (hg : 0 < g) (hchiqg : chi ≤ q * g)
    (ht : tmid ∈ Icc (0 : ℝ) 1) (hc₄ : |c₄| ≤ K) :
    ∃ F : Finset ℤ, (F.card : ℝ) ≤ 18 * K ∧
      ∀ b₀ b₁ b₃ b₄ : ℝ,
        |b₁ + tmid * b₄ - c₂ - tmid * c₃ - c₄ * (b₀ + tmid * b₃)| ≤ K * q * g →
        |b₀ + tmid * b₃ - (z₀ + tmid * z₁)| ≤ 2 * chi → |b₄ - y₁| ≤ g →
          ⌊b₁ / g⌋ ∈ F := by
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  obtain ⟨F, hF, hcover⟩ := interval_mesh_cover hg (by positivity : 0 ≤ 4 * K * g)
    (c₂ + c₄ * z₀ + tmid * (c₃ + c₄ * z₁ - y₁))
  refine ⟨F, ?_, ?_⟩
  · have heq : 4 * (4 * K * g) / g + 2 = 16 * K + 2 := by field_simp <;> ring
    rw [heq] at hF
    linarith
  · intro b₀ b₁ b₃ b₄ hpos hmajor hcrop
    apply hcover b₁
    have ht1 : |tmid| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
    calc
      _ = |(b₁ + tmid * b₄ - c₂ - tmid * c₃ - c₄ * (b₀ + tmid * b₃)) +
          c₄ * (b₀ + tmid * b₃ - (z₀ + tmid * z₁)) + (-tmid * (b₄ - y₁))| := by congr 1; ring
      _ ≤ |b₁ + tmid * b₄ - c₂ - tmid * c₃ - c₄ * (b₀ + tmid * b₃)| +
          |c₄ * (b₀ + tmid * b₃ - (z₀ + tmid * z₁))| + |-(tmid * (b₄ - y₁))| := by
        simpa only [neg_mul] using (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K * q * g + K * (2 * chi) + g := by
        simp only [abs_mul, abs_neg]
        exact add_le_add (add_le_add hpos (mul_le_mul hc₄ hmajor (abs_nonneg _) hK0))
          (by simpa only [one_mul] using mul_le_mul ht1 hcrop (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left hchiqg hK0,
          mul_le_mul_of_nonneg_right hq1 (mul_nonneg hK0 hg.le),
          mul_le_mul_of_nonneg_right hK hg.le]

end

end Submission.Obl.k4_general_parent_projected_layers
