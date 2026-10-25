import Submission.Obl.k4_scalar_candidate_original_return.GridCells
import Submission.Lib.K4ContinuousKakeya.Incidence

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open Set MeasureTheory
open Submission.Obl.k4_scalar_candidate_original_return
open Submission.Lib.K4ContinuousKakeya

noncomputable section

def baseLine (v : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, v]

def unitBaseDirection (v : ℝ) : EuclideanSpace ℝ (Fin 2) := ‖baseLine v‖⁻¹ • baseLine v

/-- The affine base lines always have a nonzero time component. -/
theorem baseLine_norm_lower (v : ℝ) : 1 ≤ ‖baseLine v‖ := by
  simpa [baseLine] using abs_apply_le_norm (baseLine v) 0

theorem baseLine_norm_upper (v : ℝ) : ‖baseLine v‖ ≤ 1 + |v| := by
  have hsq : ‖baseLine v‖ ^ 2 = 1 + v ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [baseLine, Fin.sum_univ_two]
  nlinarith [norm_nonneg (baseLine v), abs_nonneg v, sq_abs v]

theorem norm_unitBaseDirection (v : ℝ) : ‖unitBaseDirection v‖ = 1 := by
  have hp : 0 < ‖baseLine v‖ := zero_lt_one.trans_le (baseLine_norm_lower v)
  simp [unitBaseDirection, norm_smul, hp.ne']

theorem measurable_baseLine : Measurable baseLine := by
  unfold baseLine
  fun_prop

theorem measurable_unitBaseDirection : Measurable unitBaseDirection := by
  unfold unitBaseDirection
  exact measurable_baseLine.norm.inv.smul measurable_baseLine

theorem det_unitBaseDirection (v w : ℝ) :
    Matrix.det (Matrix.of (fun i j : Fin 2 => (![unitBaseDirection v, unitBaseDirection w] i) j)) =
      (w - v) / (‖baseLine v‖ * ‖baseLine w‖) := by
  have hv := (zero_lt_one.trans_le (baseLine_norm_lower v)).ne'
  have hw := (zero_lt_one.trans_le (baseLine_norm_lower w)).ne'
  simp [Matrix.det_fin_two, unitBaseDirection, baseLine]
  field_simp

/-- A separated pair of bounded velocities has a quantitatively
nondegenerate pair of unit base directions. -/
theorem unitBaseDirection_det_lower {v w K η : ℝ} (hK : 0 ≤ K)
    (hv : |v| ≤ K) (hw : |w| ≤ K) (hsep : η ≤ |w - v|) :
    η / (K + 1) ^ 2 ≤
      |Matrix.det (Matrix.of (fun i j : Fin 2 => (![unitBaseDirection v, unitBaseDirection w] i) j))| := by
  rw [det_unitBaseDirection, abs_div,
    abs_of_pos (mul_pos (zero_lt_one.trans_le (baseLine_norm_lower v))
      (zero_lt_one.trans_le (baseLine_norm_lower w)))]
  have hden : ‖baseLine v‖ * ‖baseLine w‖ ≤ (K + 1) ^ 2 := by
    have hv' : ‖baseLine v‖ ≤ K + 1 := (baseLine_norm_upper v).trans (by linarith)
    have hw' : ‖baseLine w‖ ≤ K + 1 := (baseLine_norm_upper w).trans (by linarith)
    nlinarith [norm_nonneg (baseLine v), norm_nonneg (baseLine w)]
  calc
    η / (K + 1) ^ 2 ≤ |w - v| / (K + 1) ^ 2 :=
      div_le_div_of_nonneg_right hsep (sq_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _)
      (mul_pos (zero_lt_one.trans_le (baseLine_norm_lower v))
        (zero_lt_one.trans_le (baseLine_norm_lower w))) hden

/-- Euclidean versions of the accepted scalar floor cells. -/
def euclideanBaseCell (ξ : ℝ) (q : Fin 2 → ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  WithLp.ofLp ⁻¹' scalarGridCell ξ q

theorem measurableSet_euclideanBaseCell (ξ : ℝ) (q : Fin 2 → ℤ) :
    MeasurableSet (euclideanBaseCell ξ q) :=
  (scalarGridCell_measurable ξ q).preimage
    (PiLp.volume_preserving_ofLp (Fin 2)).measurable

theorem volume_euclideanBaseCell {ξ : ℝ} (hξ : 0 < ξ) (q : Fin 2 → ℤ) :
    volume (euclideanBaseCell ξ q) = ENNReal.ofReal (ξ ^ 2) := by
  rw [euclideanBaseCell,
    (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      (scalarGridCell_measurable ξ q).nullMeasurableSet,
    scalarGridCell_volume hξ]

theorem euclideanBaseCell_disjoint (ξ : ℝ) :
    Pairwise (fun q q' : Fin 2 → ℤ => Disjoint (euclideanBaseCell ξ q) (euclideanBaseCell ξ q')) := by
  intro q q' hqq'
  exact (scalarGridCell_disjoint ξ hqq').preimage WithLp.ofLp

/-- Rounding a fine state to a coarse base cell costs at most four
coarse mesh widths in Euclidean distance. -/
theorem dist_le_four_mesh_of_assigned_cell {ξ : ℝ} (hξ : 0 < ξ)
    (u center : EuclideanSpace ℝ (Fin 2)) (q : Fin 2 → ℤ)
    (hc : center ∈ euclideanBaseCell ξ q)
    (hclose : ∀ i, |u i - center i| ≤ ξ)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ euclideanBaseCell ξ q) :
    dist x u ≤ 4 * ξ := by
  have hcoord : ∀ i, |x i - u i| ≤ 2 * ξ := by
    intro i
    have hxc := scalarGridCell_distance hξ hx hc i
    have hcu : |center i - u i| ≤ ξ := by simpa [abs_sub_comm] using hclose i
    exact (abs_sub_le (x i) (center i) (u i)).trans (by linarith)
  have hs := EuclideanSpace.real_norm_sq_eq (x - u)
  have h₀ := hcoord 0
  have h₁ := hcoord 1
  simp only [Fin.sum_univ_two, PiLp.sub_apply] at hs
  rw [dist_eq_norm]
  have h₀sq := mul_le_mul h₀ h₀ (abs_nonneg (x 0 - u 0)) (by positivity : 0 ≤ 2 * ξ)
  have h₁sq := mul_le_mul h₁ h₁ (abs_nonneg (x 1 - u 1)) (by positivity : 0 ≤ 2 * ξ)
  nlinarith [sq_abs (x 0 - u 0), sq_abs (x 1 - u 1), norm_nonneg (x - u)]

end
end Submission.Obl.k4_scalar_capped_heavy_potential
