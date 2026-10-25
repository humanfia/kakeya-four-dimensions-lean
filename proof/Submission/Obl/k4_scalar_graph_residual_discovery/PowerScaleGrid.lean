/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PowerScaleGrid.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarGridCovering
import Submission.Obl.k4_scalar_grid_parameter_preparation.FiniteScaleGrid

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

def powerScaleGrid (N : ℝ) (J C : ℕ) : Finset ℝ :=
  (insert 0 (positiveScaleGrid J C)).image (fun s => N ^ (-s))

theorem powerScaleGrid_card_le (N : ℝ) (J C : ℕ) :
    (powerScaleGrid N J C).card ≤ C * J + 1 :=
  Finset.card_image_le.trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (positiveScaleGrid_card_le J C) 1))

private theorem exponent_grid_neighbors {J C : ℕ} (hJ : 1 ≤ J) {v : ℝ}
    (hv : 0 ≤ v) (hvC : v ≤ C) :
    ∃ lo ∈ insert 0 (positiveScaleGrid J C), ∃ hi ∈ insert 0 (positiveScaleGrid J C),
      0 ≤ lo ∧ lo ≤ v ∧ v ≤ hi ∧ hi ≤ C ∧
        hi - v ≤ 1 / (J : ℝ) ∧ v - lo ≤ 1 / (J : ℝ) := by
  classical
  have hJ₀ : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  by_cases hv₀ : v = 0
  · refine ⟨0, Finset.mem_insert_self _ _, 0, Finset.mem_insert_self _ _, ?_⟩
    subst v
    exact ⟨le_rfl, le_rfl, le_rfl, by positivity,
      by simpa only [sub_self] using (one_div_pos.mpr hJ₀).le,
      by simpa only [sub_self] using (one_div_pos.mpr hJ₀).le⟩
  obtain ⟨s, hs, hvs, hsv⟩ := exists_positiveScaleGrid_point J C (by omega)
    (lt_of_le_of_ne hv (Ne.symm hv₀)) hvC
  obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp hs
  obtain ⟨hj₁, hjC⟩ := Finset.mem_Icc.mp hj
  let lo : ℝ := ((j - 1 : ℕ) : ℝ) / J
  have hlo : lo ∈ insert 0 (positiveScaleGrid J C) := by
    by_cases hj₀ : j - 1 = 0
    · simp only [lo, hj₀, Nat.cast_zero, zero_div, Finset.mem_insert_self]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨j - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  have hs_eq : s = lo + 1 / (J : ℝ) := by
    rw [← hjs]
    dsimp only [lo]
    rw [Nat.cast_sub hj₁, Nat.cast_one]
    ring
  have hsC : s ≤ C := by
    rw [← hjs]
    apply (div_le_iff₀ hJ₀).mpr
    exact_mod_cast hjC
  refine ⟨lo, hlo, s, Finset.mem_insert_of_mem hs, by positivity, ?_, hvs, hsC, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

private theorem exponent_of_scale {N C r : ℝ} (hN : 1 < N)
    (hr : N ^ (-C) ≤ r) (hr₁ : r ≤ 1) :
    0 ≤ -Real.logb N r ∧ -Real.logb N r ≤ C ∧ N ^ (-(-Real.logb N r)) = r := by
  have hN₀ : 0 < N := by linarith
  have hr₀ : 0 < r := (Real.rpow_pos_of_pos hN₀ _).trans_le hr
  have hlo := (Real.le_logb_iff_rpow_le hN hr₀).mpr hr
  have hhi := (Real.logb_le_iff_le_rpow hN hr₀).mpr
    (by simpa only [Real.rpow_zero] using hr₁ : r ≤ N ^ (0 : ℝ))
  refine ⟨by linarith, by linarith, ?_⟩
  rw [neg_neg]
  exact Real.rpow_logb hN₀ hN.ne' hr₀

/-- A finite grid with C*J+1 entries brackets every physical scale down
to N^-C with multiplicative loss N^(1/J). -/
theorem powerScaleGrid_rounding {N : ℝ} (hN : 1 < N) (J C : ℕ) (hJ : 1 ≤ J) :
    ScalarScaleRounding (N ^ (-(C : ℝ))) (N ^ (1 / (J : ℝ))) (powerScaleGrid N J C : Set ℝ) := by
  classical
  have hN₀ : 0 < N := by linarith
  constructor
  · intro r hr hr₁
    obtain ⟨hv, hvC, hpow⟩ := exponent_of_scale hN hr hr₁
    obtain ⟨lo, _, hi, hhig, _, _, hvhi, _, hhiv, _⟩ := exponent_grid_neighbors hJ hv hvC
    refine ⟨N ^ (-hi), Finset.mem_image.mpr ⟨hi, hhig, rfl⟩,
      Real.rpow_pos_of_pos hN₀ _, ?_, ?_⟩
    · rw [← hpow]
      exact Real.rpow_le_rpow_of_exponent_le hN.le (neg_le_neg hvhi)
    · rw [← hpow, ← Real.rpow_add hN₀]
      exact Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
  · intro r hr hr₁
    obtain ⟨hv, hvC, hpow⟩ := exponent_of_scale hN hr hr₁
    obtain ⟨lo, hlog, hi, _, hlo, hlov, _, _, _, hvlo⟩ := exponent_grid_neighbors hJ hv hvC
    refine ⟨N ^ (-lo), Finset.mem_image.mpr ⟨lo, hlog, rfl⟩, ?_, ?_, ?_⟩
    · rw [← hpow]
      exact Real.rpow_le_rpow_of_exponent_le hN.le (neg_le_neg hlov)
    · exact Real.rpow_le_one_of_one_le_of_nonpos hN.le (neg_nonpos.mpr hlo)
    · rw [← hpow, ← Real.rpow_add hN₀]
      exact Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)

end

end Submission.Obl.k4_scalar_graph_residual_discovery
