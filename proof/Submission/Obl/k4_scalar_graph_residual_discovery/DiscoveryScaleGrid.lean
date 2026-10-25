/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file DiscoveryScaleGrid.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.PowerScaleGrid
import Submission.Obl.k4_scalar_graph_residual_discovery.PreparationPieces
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalRows

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

theorem discovery_exponent_grid (J C : ℕ) :
    (Finset.range (C * J + 1)).image (fun i : ℕ => (i : ℝ) / J) =
      insert 0 (positiveScaleGrid J C) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    by_cases hi₀ : i = 0
    · simp only [hi₀, Nat.cast_zero, zero_div, Finset.mem_insert_self]
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨i, Finset.mem_Icc.mpr ⟨by omega, by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi⟩,
          rfl⟩)
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by
        have hh := (Finset.mem_Icc.mp hi).2
        omega), rfl⟩

theorem powerScaleGrid_eq_range (N : ℝ) (J C : ℕ) :
    (powerScaleGrid N J C : Set ℝ) = Set.range (fun i : Fin (C * J + 1) => powerWidth N J i) := by
  classical
  ext x
  change (x ∈ ((insert 0 (positiveScaleGrid J C)).image (fun s : ℝ => N ^ (-s)))) ↔ _
  rw [← discovery_exponent_grid, Finset.image_image]
  constructor
  · intro hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_image.mp hx
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, hx⟩
  · rintro ⟨i, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr i.isLt, hi⟩

/-- The very same finite indexed scales are used for global cuts, raw
residual lists, common choice and the later all-real-scale interpolation. -/
theorem discovery_scale_rounding {N : ℝ} (hN : 1 < N) (J C : ℕ) (hJ : 1 ≤ J) :
    ScalarScaleRounding (N ^ (-(C : ℝ))) (N ^ (1 / (J : ℝ)))
      (Set.range (fun i : Fin (C * J + 1) => powerWidth N J i)) := by
  rw [← powerScaleGrid_eq_range]
  exact powerScaleGrid_rounding hN J C hJ

theorem discovery_scale_bounds {N : ℝ} (hN : 1 ≤ N) {J C : ℕ} (hJ : 1 ≤ J)
    (i : Fin (C * J + 1)) :
    N ^ (-(C : ℝ)) ≤ powerWidth N J i ∧ powerWidth N J i ≤ 1 := by
  have hJ₀ : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hi : (i : ℝ) / J ≤ C := by
    apply (div_le_iff₀ hJ₀).mpr
    exact_mod_cast (by omega : (i : ℕ) ≤ C * J)
  exact ⟨Real.rpow_le_rpow_of_exponent_le hN (by linarith),
    Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr (by positivity))⟩

/-- On a selected scale the preparation rounding costs ONLY the original
mesh buffer H. No `N^(1/J)` factor enters the raw list budget. -/
theorem discovery_prepared_scale {N H a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a)
    {M J C : ℕ} (hM : 1 ≤ M) (hJ : 1 ≤ J)
    (hcost : N ^ (1 / (M : ℝ)) ≤ H) (i : Fin (C * J + 1)) :
    a ≤ upperGridExponent M (a + (i : ℝ) / J) ∧
      upperGridExponent M (a + (i : ℝ) / J) ≤ a + C + 1 / (M : ℝ) ∧
      N ^ (-upperGridExponent M (a + (i : ℝ) / J)) ≤ N ^ (-a) * powerWidth N J i ∧
      N ^ (-a) * powerWidth N J i ≤ H * N ^ (-upperGridExponent M (a + (i : ℝ) / J)) := by
  have hN₀ : 0 < N := by linarith
  have hJ₀ : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hi₀ : 0 ≤ (i : ℝ) / J := by positivity
  have hiC : (i : ℝ) / J ≤ C := by
    apply (div_le_iff₀ hJ₀).mpr
    exact_mod_cast (by omega : (i : ℕ) ≤ C * J)
  have hu := upperGridExponent_bounds hM (add_nonneg ha hi₀)
  have hw := grid_width_comparison hN hM hcost (add_nonneg ha hi₀)
  have hmul : N ^ (-(a + (i : ℝ) / J)) = N ^ (-a) * powerWidth N J i := by
    rw [neg_add, Real.rpow_add hN₀]
    rfl
  refine ⟨by linarith only [hu.1, hi₀], by linarith only [hu.2, hiC], ?_, ?_⟩
  · simpa only [hmul] using hw.1
  · rw [hmul] at hw
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hN₀ _)).mp hw.2

theorem upperGridExponent_mono {M : ℕ} (hM : 1 ≤ M) : Monotone (upperGridExponent M) := by
  have hM₀ : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  intro a b hab
  exact div_le_div_of_nonneg_right (by
    exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right hab hM₀)) hM₀

theorem discovery_prepared_scale_antitone {N a : ℝ} (hN : 1 < N)
    {M J : ℕ} (hM : 1 ≤ M) (hJ : 1 ≤ J) {i j : ℕ}
    (hscale : powerWidth N J i ≤ powerWidth N J j) :
    upperGridExponent M (a + (j : ℝ) / J) ≤ upperGridExponent M (a + (i : ℝ) / J) := by
  have he : -((i : ℝ) / J) ≤ -((j : ℝ) / J) := (Real.rpow_le_rpow_left_iff hN).mp hscale
  exact upperGridExponent_mono hM (by linarith)

end

end Submission.Obl.k4_scalar_graph_residual_discovery
