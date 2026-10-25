-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.GoodCoreLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/GoodCoreLists.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/GoodCoreLists.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/GoodCoreLists.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.GraphCells
import Submission.Obl.k4_adapted_oscillation_tests.Glue

/-!
Good branch centers are kept with the grid labels used to choose them.
A terminal observation resolving that grid has a bounded core menu,
independently of the total number of centers.

The coded-net construction adapts this LOT tree oai_074_kakeya_four_dimensions,
obligation o204, session x0747, commit934f89606d3cf7dbdb9fb039b3f743b22ab540cc,
Submission/Obl/k4_uniform_sampled_isotropic_branches/GoodBaseCenters.lean.
That file has no earlier code attribution. The extension exposes its
actual grid codes instead of discarding them after choosing centers.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set

noncomputable section

/-- Choose one actual good center in each occupied grid cell and retain
its grid code. No regularity or closedness of the good set is needed. -/
theorem original_good_base_centers_with_codes
    (A : Set (EuclideanSpace ℝ (Fin 3)))
    (hA : ∀ z ∈ A, ∀ j, |z j| ≤ 1) {r : ℝ} (hr : 0 < r) :
    ∃ codes : Finset (Fin 3 → ℤ), ∃ center : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3),
      (codes.card : ℝ) ≤ (12 / r + 2) ^ 3 ∧
      (∀ b ∈ codes, center b ∈ A ∧ ∀ j, ⌊center b j / (r / 3)⌋ = b j) ∧
      ∀ z ∈ A, ∃ b ∈ codes, ‖z - center b‖ ≤ r := by
  classical
  let mesh := r / 3
  have hm : 0 < mesh := div_pos hr (by norm_num)
  obtain ⟨B, hB, hcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover
    hm (by norm_num : (0 : ℝ) ≤ 1) 0
  let code : EuclideanSpace ℝ (Fin 3) → Fin 3 → ℤ := fun z j => ⌊z j / mesh⌋
  let All : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => B)
  let codes := All.filter (fun b => ∃ z ∈ A, code z = b)
  let center : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3) := fun b =>
    if h : ∃ z ∈ A, code z = b then h.choose else 0
  have hc (b : Fin 3 → ℤ) (hb : b ∈ codes) : center b ∈ A ∧ code (center b) = b := by
    have hex : ∃ z ∈ A, code z = b := (Finset.mem_filter.mp hb).2
    simpa only [center, dite_eq_left hex] using hex.choose_spec
  refine ⟨codes, center, ?_, ?_, ?_⟩
  · calc
      (codes.card : ℝ) ≤ (All.card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
      _ = (B.card : ℝ) ^ 3 := by simp [All, Fintype.card_piFinset]
      _ ≤ (12 / r + 2) ^ 3 := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 3
        calc
          (B.card : ℝ) ≤ 4 / mesh + 2 := by simpa only [mul_one] using hB
          _ = 12 / r + 2 := by dsimp only [mesh]; field_simp; ring
  · intro b hb
    exact ⟨(hc b hb).1, fun j => congrFun (hc b hb).2 j⟩
  · intro z hz
    have hcode : code z ∈ codes := by
      apply Finset.mem_filter.mpr
      refine ⟨Fintype.mem_piFinset.mpr ?_, z, hz, rfl⟩
      intro j
      exact hcover (z j) (by simpa using hA z hz j)
    refine ⟨code z, hcode, ?_⟩
    have heq := (hc (code z) hcode).2
    have hcoord (j : Fin 3) : |z j - center (code z) j| ≤ mesh := by
      have hh := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun heq j).symm
      rw [← sub_div, abs_div, abs_of_pos hm] at hh
      simpa only [one_mul] using ((div_lt_iff₀ hm).mp hh).le
    have hnorm := Submission.Obl.k4_adapted_oscillation_tests.norm_apply_le_sum_abs
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) (fun j => by simp)
      (z - center (code z))
    change ‖z - center (code z)‖ ≤ ∑ j, |(z - center (code z)) j| at hnorm
    calc
      ‖z - center (code z)‖ ≤ ∑ j, |(z - center (code z)) j| := hnorm
      _ ≤ ∑ _j : Fin 3, mesh := Finset.sum_le_sum (fun j _ => hcoord j)
      _ = r := by simp [mesh]; ring

/-- The coded good net has a format-independent power bound at radius
`K^-e`; its grid metadata are preserved for original-reference menus. -/
theorem original_good_base_centers_with_codes_power
    (e : ℕ) {K : ℝ} (hK : 2 ≤ K)
    (A : Set (EuclideanSpace ℝ (Fin 3)))
    (hA : ∀ z ∈ A, ∀ j, |z j| ≤ 1) :
    ∃ codes : Finset (Fin 3 → ℤ), ∃ center : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3),
      (codes.card : ℝ) ≤ K ^ (3 * e + 12) ∧
      (∀ b ∈ codes, center b ∈ A ∧ ∀ j, ⌊center b j / ((K ^ e)⁻¹ / 3)⌋ = b j) ∧
      ∀ z ∈ A, ∃ b ∈ codes, ‖z - center b‖ ≤ (K ^ e)⁻¹ := by
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hp : 1 ≤ K ^ e := one_le_pow₀ hK1
  obtain ⟨codes, center, hcard, hcenters, hcover⟩ :=
    original_good_base_centers_with_codes A hA (show 0 < (K ^ e)⁻¹ by positivity)
  have hside : 12 / (K ^ e)⁻¹ + 2 ≤ K ^ (e + 4) := by
    calc
      _ = 12 * K ^ e + 2 := by rw [div_inv_eq_mul]
      _ ≤ 14 * K ^ e := by nlinarith
      _ ≤ K ^ 4 * K ^ e := mul_le_mul_of_nonneg_right
        ((by norm_num : (14 : ℝ) ≤ 2 ^ 4).trans (pow_le_pow_left₀ (by norm_num) hK 4))
        (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  refine ⟨codes, center, hcard.trans ?_, hcenters, hcover⟩
  calc
    (12 / (K ^ e)⁻¹ + 2) ^ 3 ≤ (K ^ (e + 4)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hside 3
    _ = K ^ (3 * e + 12) := by rw [← pow_mul]; congr 1; omega

/-- A base observation box resolving the center grid has a uniformly
bounded list of nearby core labels. The count contains no inverse mesh
and no total-center factor. -/
theorem core_labels_over_resolved_base_box
    (center : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3))
    {mesh R : ℝ} (hmesh : 0 < mesh) (hR : 0 ≤ R)
    (z₀ : Fin 3 → ℝ) :
    ∃ menu : Finset (Fin 3 → ℤ), (menu.card : ℝ) ≤ (4 * R + 6) ^ 3 ∧
      ∀ b : Fin 3 → ℤ, (∀ j, ⌊center b j / mesh⌋ = b j) →
        ∀ z : EuclideanSpace ℝ (Fin 3),
          (∀ j, |z j - z₀ j| ≤ mesh) → ‖z - center b‖ ≤ R * mesh → b ∈ menu := by
  classical
  have hwidth : 0 ≤ (R + 1) * mesh := by positivity
  choose B hB hcover using fun j : Fin 3 =>
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hmesh hwidth (z₀ j)
  let menu := Fintype.piFinset B
  refine ⟨menu, ?_, ?_⟩
  · have hside (j : Fin 3) : ((B j).card : ℝ) ≤ 4 * R + 6 := by
      have hh := hB j
      convert hh using 1 <;> field_simp <;> ring
    calc
      (menu.card : ℝ) = ∏ j : Fin 3, ((B j).card : ℝ) := by
        simp only [menu, Fintype.card_piFinset, Nat.cast_prod]
      _ ≤ ∏ _j : Fin 3, (4 * R + 6) :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hside j)
      _ = (4 * R + 6) ^ 3 := by simp
  · intro b hcode z hz hnear
    apply Fintype.mem_piFinset.mpr
    intro j
    have hcoord : |z j - center b j| ≤ R * mesh := by
      have hh := PiLp.norm_apply_le (z - center b) j
      simp only [Real.norm_eq_abs, PiLp.sub_apply] at hh
      exact hh.trans hnear
    have hc : |center b j - z₀ j| ≤ (R + 1) * mesh := by
      apply abs_le.mpr
      constructor <;> linarith [(abs_le.mp (hz j)).1, (abs_le.mp (hz j)).2,
        (abs_le.mp hcoord).1, (abs_le.mp hcoord).2]
    simpa only [hcode j] using hcover j (center b j) hc

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
