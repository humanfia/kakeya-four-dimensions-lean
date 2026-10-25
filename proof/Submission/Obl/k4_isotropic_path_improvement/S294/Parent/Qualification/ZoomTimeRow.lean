-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ZoomTimeRow, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ZoomTimeRow.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ZoomTimeRow.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ZoomTimeRow.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterZoom
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.TimeRowSelection


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

private theorem affine_coordinate_comparison (a b a' b' ρ K t u : ℝ)
    (hρ : 0 ≤ ρ) (ht : |t| ≤ 1) (ha : |a - a'| ≤ ρ)
    (hb : |b - b'| ≤ ρ) (hb' : |b'| ≤ K) :
    |(a + b * t) - (a' + b' * u)| ≤ 2 * ρ + K * |t - u| := by
  rw [show (a + b * t) - (a' + b' * u) =
    (a - a') + (b - b') * t + b' * (t - u) by ring]
  have hlin : |(b - b') * t| ≤ ρ := by
    rw [abs_mul]
    exact (mul_le_mul hb ht (abs_nonneg _) hρ).trans_eq (mul_one _)
  have hgap : |b' * (t - u)| ≤ K * |t - u| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hb' (abs_nonneg _)
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add ha hlin) hgap).trans_eq (by ring))

private theorem quadratic_coordinate_comparison (c c' : Fin 7 → ℝ)
    (ρ K t u : ℝ) (hρ : 0 ≤ ρ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ i, |c i - c' i| ≤ ρ) (h1 : |c' 1| ≤ K) (h2 : |c' 2| ≤ K) :
    |zx c t - zx c' u| ≤ 3 * ρ + 3 * K * |t - u| := by
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have ht2 : |t ^ 2| ≤ 1 := by rw [abs_pow]; nlinarith [abs_nonneg t]
  have hsame : |zx c t - zx c' t| ≤ 3 * ρ := by
    rw [show zx c t - zx c' t = (c 0 - c' 0) + (c 1 - c' 1) * t +
      (c 2 - c' 2) * t ^ 2 by dsimp [zx]; ring]
    have h1 : |(c 1 - c' 1) * t| ≤ ρ := by
      rw [abs_mul]
      exact (mul_le_mul (hcoeff 1) ht' (abs_nonneg _) hρ).trans_eq (mul_one _)
    have h2 : |(c 2 - c' 2) * t ^ 2| ≤ ρ := by
      rw [abs_mul]
      exact (mul_le_mul (hcoeff 2) ht2 (abs_nonneg _) hρ).trans_eq (mul_one _)
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      ((add_le_add (add_le_add (hcoeff 0) h1) h2).trans_eq (by ring))
  have htime : |zx c' t - zx c' u| ≤ 3 * K * |t - u| := by
    rw [show zx c' t - zx c' u = (c' 1 + c' 2 * (t + u)) * (t - u) by dsimp [zx]; ring,
      abs_mul]
    have hsum : |t + u| ≤ 2 := by
      rw [abs_of_nonneg (by linarith [ht.1, hu.1])]
      linarith [ht.2, hu.2]
    have hinner : |c' 1 + c' 2 * (t + u)| ≤ 3 * K := by
      have hK : 0 ≤ K := (abs_nonneg _).trans h2
      have h := mul_le_mul h2 hsum (abs_nonneg _) hK
      rw [← abs_mul] at h
      linarith [abs_add_le (c' 1) (c' 2 * (t + u)), h1]
    exact mul_le_mul_of_nonneg_right hinner (abs_nonneg _)
  exact (abs_sub_le (zx c t) (zx c' t) (zx c' u)).trans (add_le_add hsame htime)

/-- Four central derivative coefficients control positions at different
times. The three central intercepts need no absolute bound. -/
theorem original_parameter_world_position_comparison_of_jets (c c' : Fin 7 → ℝ)
    (ρ K t u : ℝ) (hρ : 0 ≤ ρ) (hK : 1 ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ i, |c i - c' i| ≤ ρ)
    (hjets : |c' 1| ≤ K ∧ |c' 2| ≤ K ∧ |c' 4| ≤ K ∧ |c' 6| ≤ K) :
    ‖zpos c t - zpos c' u‖ ≤ 3 * K * (|t - u| + ρ) := by
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hK0 : 0 ≤ K := by linarith
  have hKρ : ρ ≤ K * ρ := by nlinarith
  have hKg : |t - u| ≤ K * |t - u| := by nlinarith [abs_nonneg (t - u)]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change |t - u| ≤ _
    nlinarith [abs_nonneg (t - u)]
  · change |zx c t - zx c' u| ≤ _
    exact (quadratic_coordinate_comparison c c' ρ K t u hρ ht hu hcoeff hjets.1 hjets.2.1).trans (by
      nlinarith)
  · change |(c 3 + c 4 * t) - (c' 3 + c' 4 * u)| ≤ _
    exact (affine_coordinate_comparison _ _ _ _ ρ K t u hρ ht' (hcoeff 3)
      (hcoeff 4) hjets.2.2.1).trans (by nlinarith [abs_nonneg (t - u)])
  · change |(c 5 + c 6 * t) - (c' 5 + c' 6 * u)| ≤ _
    exact (affine_coordinate_comparison _ _ _ _ ρ K t u hρ ht' (hcoeff 5)
      (hcoeff 6) hjets.2.2.2).trans (by nlinarith [abs_nonneg (t - u)])

/-- Compatibility form with a bound on every central coefficient. -/
theorem original_parameter_world_position_comparison (c c' : Fin 7 → ℝ)
    (ρ K t u : ℝ) (hρ : 0 ≤ ρ) (hK : 1 ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ i, |c i-c' i| ≤ ρ) (hbound : ∀ i, |c' i| ≤ K) :
    ‖zpos c t-zpos c' u‖ ≤ 3*K*(|t-u|+ρ) :=
  original_parameter_world_position_comparison_of_jets c c' ρ K t u hρ hK ht hu hcoeff
    ⟨hbound 1,hbound 2,hbound 4,hbound 6⟩

/-- Produce the time-only row in one actual original parameter block.
Physical field comparison and coefficient geometry give every row
comparison, including the bound between different active trajectories. -/
theorem exists_zoom_time_row_of_jets {Λ : Type*} (E : Set (Λ × ℝ))
    (c : Λ → Fin 7 → ℝ) (row : Λ × ℝ → Fin 2 → ℝ)
    (ρ K B L : ℝ) (hρ : 0 < ρ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hjets : ∀ z ∈ E, |c z.1 1| ≤ K ∧ |c z.1 2| ≤ K ∧
      |c z.1 4| ≤ K ∧ |c z.1 6| ≤ K)
    (hdiam : ∀ z ∈ E, ∀ z' ∈ E, ∀ i, |c z.1 i - c z'.1 i| ≤ ρ)
    (hbound : ∀ z ∈ E, ‖row z‖ ≤ B)
    (hfield : ∀ z ∈ E, ∀ z' ∈ E,
      ‖row z - row z'‖ ≤ L * (‖zpos (c z.1) z.2 - zpos (c z'.1) z'.2‖ + ρ)) :
    ∃ F : ℝ → Fin 2 → ℝ, Measurable F ∧
      (∀ z ∈ E, ‖F z.2‖ ≤ B) ∧
      (∀ z ∈ E, ‖F z.2 - row z‖ ≤ 2 * ((3 * K + 1) * L) * ρ) ∧
      (∀ z ∈ E, ∀ z' ∈ E,
        ‖F z.2 - F z'.2‖ ≤ 3 * ((3 * K + 1) * L) * (|z.2 - z'.2| + ρ)) := by
  have hcmp : ∀ z ∈ E, ∀ z' ∈ E,
      ‖row z - row z'‖ ≤ ((3 * K + 1) * L) * (|z.2 - z'.2| + ρ) := by
    intro z hz z' hz'
    have hpos := original_parameter_world_position_comparison_of_jets (c z.1) (c z'.1)
      ρ K z.2 z'.2 hρ.le hK (htime z hz) (htime z' hz') (hdiam z hz z' hz')
      (hjets z' hz')
    apply (hfield z hz z' hz').trans
    nlinarith [mul_le_mul_of_nonneg_left hpos hL,
      mul_nonneg hL (abs_nonneg (z.2 - z'.2))]
  obtain ⟨F, hm, hb, hf, hc, _⟩ := exists_time_row_of_original_comparison E Prod.snd row
    ρ B ((3 * K + 1) * L) hρ (by positivity) hbound hcmp
  exact ⟨F, hm, hb, hf, hc⟩


/-- Produce the time-only row in one actual original parameter block.
Physical field comparison and coefficient geometry give every row
comparison, including the bound between different active trajectories. -/
theorem exists_zoom_time_row {Λ : Type*} (E : Set (Λ × ℝ))
    (c : Λ → Fin 7 → ℝ) (row : Λ × ℝ → Fin 2 → ℝ)
    (ρ K B L : ℝ) (hρ : 0 < ρ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ z ∈ E, ∀ i, |c z.1 i| ≤ K)
    (hdiam : ∀ z ∈ E, ∀ z' ∈ E, ∀ i, |c z.1 i - c z'.1 i| ≤ ρ)
    (hbound : ∀ z ∈ E, ‖row z‖ ≤ B)
    (hfield : ∀ z ∈ E, ∀ z' ∈ E,
      ‖row z - row z'‖ ≤ L * (‖zpos (c z.1) z.2 - zpos (c z'.1) z'.2‖ + ρ)) :
    ∃ F : ℝ → Fin 2 → ℝ, Measurable F ∧
      (∀ z ∈ E, ‖F z.2‖ ≤ B) ∧
      (∀ z ∈ E, ‖F z.2 - row z‖ ≤ 2 * ((3 * K + 1) * L) * ρ) ∧
      (∀ z ∈ E, ∀ z' ∈ E,
        ‖F z.2 - F z'.2‖ ≤ 3 * ((3 * K + 1) * L) * (|z.2 - z'.2| + ρ)) := by
  exact exists_zoom_time_row_of_jets E c row ρ K B L hρ hK hL htime
    (fun z hz => ⟨hcoeff z hz 1,hcoeff z hz 2,hcoeff z hz 4,hcoeff z hz 6⟩)
    hdiam hbound hfield

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
