/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/CellBallCaps.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.FrameCells
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripAlignment

/-!
Convert the original two-coordinate velocity-grid ceilings to the ball caps
used by strip alignment. A ball of radius at most one grid width meets at most
nine cells; normalization uses the actual old frame and time length.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set
open Submission.Lib.K4XInterface
open Submission.Lib.K4ListedExceptions
open Submission.Obl.k4_native_finite_terminal_atlas_lift
open scoped RealInnerProductSpace

/-- A physical ball of radius at most one velocity-grid width meets nine
canonical cells. This witness feeds the original-law listed-label estimate. -/
theorem velocity_ball_finite_cells {δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ δ) (center : Plane) :
    ∃ C : Finset (Fin 2 → ℤ), C.card = 9 ∧
      ∀ v : Plane, dist v center ≤ r → (fun i => ⌊v i / δ⌋) ∈ C := by
  refine ⟨integerCodeBox 1 (fun i => ⌊center i / δ⌋), by simp [card_integerCodeBox], ?_⟩
  intro v hv
  apply floor_code_mem_integerCodeBox 1 (fun i => v i) (fun i => center i)
    (fun _ => δ) (fun _ => hδ)
  intro i
  have hnorm : ‖v - center‖ ≤ δ := by simpa only [dist_eq_norm] using hv.trans hr
  simpa only [Nat.cast_one, one_mul, PiLp.sub_apply, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (v - center) i).trans hnorm

/-- This is an estimate for any original law, including arbitrary witness
sets: a physical velocity ball costs at most nine original cell ceilings. -/
theorem velocity_ball_grid_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (velocity : Ω → Plane) {δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ δ)
    (B : ENNReal)
    (hcell : ∀ z : Fin 2 → ℤ, μ {p | (fun i => ⌊velocity p i / δ⌋) = z} ≤ B)
    (center : Plane) :
    μ {p | dist (velocity p) center ≤ r} ≤ 9 * B := by
  classical
  obtain ⟨C, hC, hcells⟩ := velocity_ball_finite_cells hδ hr center
  have hcover : {p | dist (velocity p) center ≤ r} ⊆
      ⋃ z : C, {p | (fun i => ⌊velocity p i / δ⌋) = z.val} := by
    intro p hp
    have hcode := hcells (velocity p) hp
    exact mem_iUnion.mpr ⟨⟨_, hcode⟩, rfl⟩
  calc
    _ ≤ μ (⋃ z : C, {p | (fun i => ⌊velocity p i / δ⌋) = z.val}) := measure_mono hcover
    _ ≤ ∑ z : C, μ {p | (fun i => ⌊velocity p i / δ⌋) = z.val} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _z : C, B := Finset.sum_le_sum fun z _ => hcell z.val
    _ = 9 * B := by simp [hC, nsmul_eq_mul]

/-- A normalized old-frame ball is a physical velocity ball with radius
multiplied by at most the actual path slack. -/
theorem normalized_velocity_ball_subset {q κ r : ℝ} {Q : Frame} {u center : Plane}
    (hq : 0 < q) (hQ : Q.det ≠ 0) (hκ : 0 ≤ κ)
    (hsize : frameSize Q ≤ κ * q) (v : Plane)
    (hv : dist (q • Matrix.toEuclideanLin Q⁻¹ (v - u)) center ≤ r) :
    dist v (u + q⁻¹ • Matrix.toEuclideanLin Q center) ≤ κ * r := by
  have heq : v - (u + q⁻¹ • Matrix.toEuclideanLin Q center) =
      q⁻¹ • Matrix.toEuclideanLin Q (q • Matrix.toEuclideanLin Q⁻¹ (v - u) - center) := by
    rw [map_sub, map_smul, toEuclideanLin_inv_cancel Q hQ, smul_sub, smul_smul,
      inv_mul_cancel₀ hq.ne', one_smul]
    abel
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq)]
  have hnorm : ‖q • Matrix.toEuclideanLin Q⁻¹ (v - u) - center‖ ≤ r := by
    simpa only [dist_eq_norm] using hv
  calc
    _ ≤ q⁻¹ * (frameSize Q * ‖q • Matrix.toEuclideanLin Q⁻¹ (v - u) - center‖) :=
      mul_le_mul_of_nonneg_left (euclideanLin_norm_le Q _) (by positivity)
    _ ≤ q⁻¹ * ((κ * q) * r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hsize hnorm (norm_nonneg _) (by positivity))
        (by positivity)
    _ = κ * r := by field_simp

theorem normalized_velocity_ball_grid_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (velocity : Ω → Plane) {δ q κ r : ℝ} {Q : Frame} {u : Plane}
    (hδ : 0 < δ) (hq : 0 < q) (hQ : Q.det ≠ 0) (hκ : 0 ≤ κ)
    (hsize : frameSize Q ≤ κ * q) (hscale : κ * r ≤ δ)
    (B : ENNReal)
    (hcell : ∀ z : Fin 2 → ℤ, μ {p | (fun i => ⌊velocity p i / δ⌋) = z} ≤ B)
    (center : Plane) :
    μ {p | dist (q • Matrix.toEuclideanLin Q⁻¹ (velocity p - u)) center ≤ r} ≤ 9 * B := by
  apply (measure_mono (t := {p | dist (velocity p)
    (u + q⁻¹ • Matrix.toEuclideanLin Q center) ≤ κ * r}) ?_).trans
      (velocity_ball_grid_cap μ velocity hδ hscale B hcell _)
  intro p hp
  exact normalized_velocity_ball_subset hq hQ hκ hsize (velocity p) hp

/-- A misaligned candidate/deep pair meets only nine canonical physical
velocity cells, as an explicit finite witness independent of observations.
Thus it can be charged by `known_label_velocity_charge` under the original
joint density without any conditional reference law. -/
theorem original_strip_overlap_velocity_cells {Ω : Type*}
    (velocity : Ω → Plane) (S : Set Ω)
    {δ q κ r gap V β γ : ℝ} {Q : Frame} {u n m : Plane}
    (hδ : 0 < δ) (hq : 0 < q) (hQ : Q.det ≠ 0) (hκ : 0 ≤ κ)
    (hsize : frameSize Q ≤ κ * q)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hV : 0 ≤ V)
    (hgap : 0 < gap) (hsmall : 4 * r ≤ gap)
    (hsep : gap ≤ ‖n - m‖ + |β - γ|)
    (hsep' : gap ≤ ‖n + m‖ + |β + γ|)
    (hfit : ∀ p ∈ S,
      ‖q • Matrix.toEuclideanLin Q⁻¹ (velocity p - u)‖ ≤ V ∧
      |inner ℝ (q • Matrix.toEuclideanLin Q⁻¹ (velocity p - u)) n - β| ≤ r ∧
      |inner ℝ (q • Matrix.toEuclideanLin Q⁻¹ (velocity p - u)) m - γ| ≤ r)
    (hscale : κ * (32 * (1 + V) * r / gap) ≤ δ) :
    ∃ C : Finset (Fin 2 → ℤ), C.card = 9 ∧
      ∀ p ∈ S, (fun i => ⌊velocity p i / δ⌋) ∈ C := by
  obtain ⟨center, hcenter⟩ := unit_strip_overlap_ball
    (fun p => q • Matrix.toEuclideanLin Q⁻¹ (velocity p - u)) S
    hn hm hV hgap hsmall hsep hsep' hfit
  obtain ⟨C, hC, hcells⟩ := velocity_ball_finite_cells hδ hscale
    (u + q⁻¹ • Matrix.toEuclideanLin Q center)
  exact ⟨C, hC, fun p hp => hcells (velocity p)
    (normalized_velocity_ball_subset hq hQ hκ hsize (velocity p) (hcenter p hp))⟩

/-- The original canonical angular-cell ceiling directly charges a pair of
separated fitted strips, after the actual old-frame change of coordinates. -/
theorem original_strip_overlap_grid_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (velocity : Ω → Plane) (S : Set Ω)
    {δ q κ r gap V β γ : ℝ} {Q : Frame} {u n m : Plane}
    (hδ : 0 < δ) (hq : 0 < q) (hQ : Q.det ≠ 0) (hκ : 0 ≤ κ)
    (hsize : frameSize Q ≤ κ * q)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hV : 0 ≤ V)
    (hgap : 0 < gap) (hsmall : 4 * r ≤ gap)
    (hsep : gap ≤ ‖n - m‖ + |β - γ|)
    (hsep' : gap ≤ ‖n + m‖ + |β + γ|)
    (hfit : ∀ p ∈ S,
      ‖q • Matrix.toEuclideanLin Q⁻¹ (velocity p - u)‖ ≤ V ∧
      |inner ℝ (q • Matrix.toEuclideanLin Q⁻¹ (velocity p - u)) n - β| ≤ r ∧
      |inner ℝ (q • Matrix.toEuclideanLin Q⁻¹ (velocity p - u)) m - γ| ≤ r)
    (hscale : κ * (32 * (1 + V) * r / gap) ≤ δ) (B : ENNReal)
    (hcell : ∀ z : Fin 2 → ℤ, μ {p | (fun i => ⌊velocity p i / δ⌋) = z} ≤ B) :
    μ S ≤ 9 * B := by
  apply unit_strip_overlap_charge μ
    (fun p => q • Matrix.toEuclideanLin Q⁻¹ (velocity p - u)) S
    hn hm hV hgap hsmall hsep hsep' hfit (9 * B)
  exact normalized_velocity_ball_grid_cap μ velocity hδ hq hQ hκ hsize hscale B hcell

end Submission.Obl.k4_finite_positive_mixed_cover_realization
