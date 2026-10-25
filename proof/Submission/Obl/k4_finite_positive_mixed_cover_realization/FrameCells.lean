/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/FrameCells.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripGeometry
import Submission.Lib.K4ListedExceptions.FrameCodes

/-!
Small major frames occupy only a subpower number of velocity cells. Together
with AngularCharge this is the largest-axis fullness preparation: charts with
both spatial axes much smaller than their time block carry negligible mass.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open Submission.Lib.K4XInterface
open Submission.Lib.K4ListedExceptions
open Submission.Obl.k4_native_finite_terminal_atlas_lift

noncomputable section

/-- The original planar velocity radius of a chart is controlled by its
actual frame size divided by its actual time-block length. -/
theorem gchart_velocity_norm_le {Nk κ j r Bv : ℝ} {M D T : ℕ}
    {Ev : Set (Line × ℝ)} {c u : Plane} {Q : Frame}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set (Line × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T j r Bv Ev c u Q R A F ex) {l : Line} (hl : l ∈ A) :
    ‖gv l - u‖ ≤ 2 * κ * ((2 : ℝ) ^ T * frameSize Q) := by
  calc
    _ = ‖Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ (gv l - u))‖ := by
      rw [toEuclideanLin_inv_cancel Q h.1]
    _ ≤ frameSize Q * ‖Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ :=
      euclideanLin_norm_le Q _
    _ ≤ frameSize Q * (2 * κ * (2 : ℝ) ^ T) :=
      mul_le_mul_of_nonneg_left (gchart_velocity h hl) (frameSize_nonneg Q)
    _ = _ := by ring

/-- If the major frame scale is at most a velocity grid width times the
time length, its entire assignment meets at most `49 κ²` velocity cells. -/
theorem gchart_small_frame_velocity_cells {Nk κ j r Bv δ : ℝ} {M D T : ℕ}
    {Ev : Set (Line × ℝ)} {c u : Plane} {Q : Frame}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set (Line × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T j r Bv Ev c u Q R A F ex)
    (hκ : 1 ≤ κ) (hδ : 0 < δ) (hsmall : (2 : ℝ) ^ T * frameSize Q ≤ δ) :
    ∃ C : Finset (Fin 2 → ℤ), (C.card : ℝ) ≤ 49 * κ ^ 2 ∧
      ∀ l ∈ A, (fun i => ⌊(gv l) i / δ⌋) ∈ C := by
  let Cr : ℕ := ⌈2 * κ⌉₊
  let C := integerCodeBox Cr (fun i => ⌊u i / δ⌋)
  have hceil : 2 * κ ≤ (Cr : ℝ) := Nat.le_ceil _
  have hceil' : (Cr : ℝ) < 2 * κ + 1 := Nat.ceil_lt_add_one (by linarith)
  refine ⟨C, ?_, ?_⟩
  · change ((integerCodeBox Cr (fun i => ⌊u i / δ⌋)).card : ℝ) ≤ _
    rw [card_integerCodeBox, Nat.cast_pow]
    have hCr : ((2 * Cr + 1 : ℕ) : ℝ) ≤ 7 * κ := by
      push_cast
      linarith
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hCr 2).trans_eq (by ring)
  · intro l hl
    have hnorm : ‖gv l - u‖ ≤ 2 * κ * δ :=
      (gchart_velocity_norm_le h hl).trans
        (mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ 2 * κ))
    apply floor_code_mem_integerCodeBox Cr (fun i => (gv l) i) (fun i => u i)
      (fun _ => δ) (fun _ => hδ)
    intro i
    have hcoord : |(gv l) i - u i| ≤ 2 * κ * δ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
        (PiLp.norm_apply_le (gv l - u) i).trans hnorm
    exact hcoord.trans (mul_le_mul_of_nonneg_right hceil hδ.le)

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
