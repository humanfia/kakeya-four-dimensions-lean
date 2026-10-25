-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.GoodBaseCenters, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/GoodBaseCenters.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/GoodBaseCenters.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/GoodBaseCenters.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/GoodBaseCenters.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames
import Submission.Lib.K4MovingMeshBoxes.Geometry
import Submission.Lib.K4QuadraticSheets.JetBins

/-! # Finite local branch centers chosen from the original good base set -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set

noncomputable section

/-- A bounded set has a controlled finite net whose centers belong to
that very set. Thus every center retains the original discriminant floor.
Neither closedness nor a separately given list of centers is required. -/
theorem original_good_base_centers
    (A : Set (EuclideanSpace ℝ (Fin 3)))
    (hA : ∀ z ∈ A, ∀ j, |z j| ≤ 1) {r : ℝ} (hr : 0 < r) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 3)),
      (S.card : ℝ) ≤ (12 / r + 2) ^ 3 ∧
      (∀ c ∈ S, c ∈ A) ∧ ∀ z ∈ A, ∃ c ∈ S, ‖z - c‖ ≤ r := by
  classical
  let mesh := r / 3
  have hm : 0 < mesh := div_pos hr (by norm_num)
  obtain ⟨B, hB, hcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover
    hm (by norm_num : (0 : ℝ) ≤ 1) 0
  let code : EuclideanSpace ℝ (Fin 3) → Fin 3 → ℤ := fun z j => ⌊z j / mesh⌋
  let Codes : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => B)
  let Active := Codes.filter (fun b => ∃ z ∈ A, code z = b)
  let center : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3) := fun b =>
    if h : ∃ z ∈ A, code z = b then h.choose else 0
  have hc (b : Fin 3 → ℤ) (hb : b ∈ Active) : center b ∈ A ∧ code (center b) = b := by
    have hex : ∃ z ∈ A, code z = b := (Finset.mem_filter.mp hb).2
    simpa only [center, dite_eq_left hex] using hex.choose_spec
  let S := Active.image center
  refine ⟨S, ?_, ?_, ?_⟩
  · calc
      (S.card : ℝ) ≤ (Active.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ (Codes.card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
      _ = (B.card : ℝ) ^ 3 := by simp [Codes, Fintype.card_piFinset]
      _ ≤ (12 / r + 2) ^ 3 := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 3
        calc
          (B.card : ℝ) ≤ 4 / mesh + 2 := by simpa only [mul_one] using hB
          _ = 12 / r + 2 := by dsimp only [mesh]; field_simp; ring
  · intro c hcS
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hcS
    exact (hc b hb).1
  · intro z hz
    have hcode : code z ∈ Active := by
      apply Finset.mem_filter.mpr
      refine ⟨Fintype.mem_piFinset.mpr ?_, z, hz, rfl⟩
      intro j
      exact hcover (z j) (by simpa using hA z hz j)
    refine ⟨center (code z), Finset.mem_image.mpr ⟨code z, hcode, rfl⟩, ?_⟩
    have heq := (hc (code z) hcode).2
    have hcoord (j : Fin 3) : |z j - center (code z) j| ≤ mesh := by
      exact (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hm
        (congrFun heq j).symm).le
    calc
      ‖z - center (code z)‖ ≤ ∑ j, |(z - center (code z)) j| :=
        Native.euclidean_norm_le_sum_abs _
      _ ≤ ∑ _j : Fin 3, mesh := Finset.sum_le_sum (fun j _ => hcoord j)
      _ = r := by simp [mesh]; ring

/-- The net size is a fixed power of K when the branch radius is K^-e.
The exponent depends only on e, before every native equation and format. -/
theorem original_good_base_centers_power
    (e : ℕ) {K : ℝ} (hK : 2 ≤ K)
    (A : Set (EuclideanSpace ℝ (Fin 3)))
    (hA : ∀ z ∈ A, ∀ j, |z j| ≤ 1) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 3)),
      (S.card : ℝ) ≤ K ^ (3 * e + 12) ∧
      (∀ c ∈ S, c ∈ A) ∧ ∀ z ∈ A, ∃ c ∈ S, ‖z - c‖ ≤ (K ^ e)⁻¹ := by
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hp : 1 ≤ K ^ e := one_le_pow₀ hK1
  obtain ⟨S, hS, hsub, hcover⟩ := original_good_base_centers A hA
    (show 0 < (K ^ e)⁻¹ by positivity)
  have hside : 12 / (K ^ e)⁻¹ + 2 ≤ K ^ (e + 4) := by
    calc
      _ = 12 * K ^ e + 2 := by rw [div_inv_eq_mul]
      _ ≤ 14 * K ^ e := by nlinarith
      _ ≤ K ^ 4 * K ^ e := mul_le_mul_of_nonneg_right
        ((by norm_num : (14 : ℝ) ≤ 2 ^ 4).trans (pow_le_pow_left₀ (by norm_num) hK 4))
        (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  refine ⟨S, hS.trans ?_, hsub, hcover⟩
  calc
    (12 / (K ^ e)⁻¹ + 2) ^ 3 ≤ (K ^ (e + 4)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hside 3
    _ = K ^ (3 * e + 12) := by rw [← pow_mul]; congr 1; omega

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
