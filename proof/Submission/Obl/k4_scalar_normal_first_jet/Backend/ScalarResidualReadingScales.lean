/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarResidualReadingScales.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarResidualReadingScales.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarWindowCovers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The fixed residual windows give first-jet covers at every allowed reading. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set

theorem scalar_residual_window_reading_bound {H K B d r : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hd0 : 0 ≤ d) (hd : d < 1)
    (hB : 1 ≤ B) (hKB : 6 * K ^ 2 ≤ B) (hr : H ^ ((1 - d) / 32) ≤ r) :
    (H ^ (1 / 8 : ℝ)) ^ ((1 - d) / 4) + B * H ^ (1 / 8 : ℝ) + 6 * K ^ 2 * H ≤ 3 * B * r := by
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hH _).trans_le hr
  have hwindow : (H ^ (1 / 8 : ℝ)) ^ ((1 - d) / 4) ≤ r := by
    calc
      _ = H ^ ((1 - d) / 32) := by
        rw [← Real.rpow_mul hH.le]
        congr 1
        ring
      _ ≤ H ^ ((1 - d) / 32) :=
        Real.rpow_le_rpow_of_exponent_ge hH hH1 (by linarith)
      _ ≤ _ := hr
  have hp : H ^ (1 / 8 : ℝ) ≤ r :=
    (Real.rpow_le_rpow_of_exponent_ge hH hH1 (by linarith : (1 - d) / 32 ≤ 1 / 8)).trans hr
  have hHr : H ≤ r :=
    (Real.self_le_rpow_of_le_one hH.le hH1 (by linarith : (1 - d) / 32 ≤ 1)).trans hr
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have h₁ := mul_le_mul_of_nonneg_left hp hB0
  have h₂ := mul_le_mul_of_nonneg_left hHr (show 0 ≤ 6 * K ^ 2 by positivity)
  have h₃ := mul_le_mul_of_nonneg_right hKB hrpos.le
  have h₄ := mul_le_mul_of_nonneg_right hB hrpos.le
  nlinarith

theorem scalar_residual_reading_card_bound {K B : ℝ}
    (hB : 1 ≤ B) (hKB : 23 * K ^ 2 ≤ B) :
    (2 * (23 * K ^ 2 + 1) + 3) * (2 * (3 * B) + 3) ≤ 1000 * B ^ 2 := by
  have hfirst : 2 * (23 * K ^ 2 + 1) + 3 ≤ 7 * B := by linarith
  have hsecond : 2 * (3 * B) + 3 ≤ 9 * B := by linarith
  have hh := mul_le_mul hfirst hsecond (by positivity : 0 ≤ 2 * (3 * B) + 3)
    (show 0 ≤ 7 * B by positivity)
  nlinarith [sq_nonneg B]

theorem scalar_first_jet_grid_covers_of_residual_windows {Λ : Type*}
    (A : Set Λ) (group current : Λ → ℤ) (jet : Λ → ℝ) (center : ℤ → ℝ)
    {H K B d r : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hd0 : 0 ≤ d) (hd : d < 1)
    (hB : 1 ≤ B) (hKB : 23 * K ^ 2 ≤ B) (hr : H ^ ((1 - d) / 32) ≤ r)
    (hnear : ∀ l ∈ A, |(group l : ℝ) - current l| ≤ 23 * K ^ 2 + 1)
    (hwindow : ∀ l ∈ A, |jet l - center (group l)| ≤
      (H ^ (1 / 8 : ℝ)) ^ ((1 - d) / 4) + B * H ^ (1 / 8 : ℝ) + 6 * K ^ 2 * H) :
    ∃ J : ℤ → Finset ℤ, (∀ z, ((J z).card : ℝ) ≤ 1000 * B ^ 2) ∧
      ∀ l ∈ A, (⌊jet l / r⌋ : ℤ) ∈ J (current l) := by
  have hKB' : 6 * K ^ 2 ≤ B := by nlinarith [sq_nonneg K]
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hH _).trans_le hr
  have hreading := scalar_residual_window_reading_bound hH hH1 hd0 hd hB hKB' hr
  obtain ⟨J, hJ, hcover⟩ := scalar_reading_cover_of_group_windows A group current jet center
    (by positivity : 0 ≤ 23 * K ^ 2 + 1) (show 0 ≤ 3 * B by positivity) hrpos hnear
    (fun l hl => (hwindow l hl).trans hreading)
  exact ⟨J, fun z => (hJ z).trans (scalar_residual_reading_card_bound hB hKB), hcover⟩

theorem scalar_interval_covers_of_grid_covers {Λ : Type*} (A : Set Λ)
    (current : Λ → ℤ) (jet : Λ → ℝ) (J : ℤ → Finset ℤ) {r C : ℝ} (hr : 0 < r)
    (hcard : ∀ z, ((J z).card : ℝ) ≤ C) (hcover : ∀ l ∈ A, (⌊jet l / r⌋ : ℤ) ∈ J (current l)) :
    ∃ L : ℤ → Finset ℝ, (∀ z, ((L z).card : ℝ) ≤ C) ∧
      ∀ l ∈ A, ∃ v ∈ L (current l), |jet l - v| ≤ r := by
  classical
  let L : ℤ → Finset ℝ := fun z => (J z).image (fun b : ℤ => r * b)
  refine ⟨L, ?_, ?_⟩
  · intro z
    have hh : ((L z).card : ℝ) ≤ ((J z).card : ℝ) := by exact_mod_cast Finset.card_image_le
    exact hh.trans (hcard z)
  · intro l hl
    exact ⟨r * (⌊jet l / r⌋ : ℤ), Finset.mem_image.mpr ⟨_, hcover l hl, rfl⟩,
      (mesh_lower_endpoint hr (k := ⌊jet l / r⌋) rfl).2.le⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
