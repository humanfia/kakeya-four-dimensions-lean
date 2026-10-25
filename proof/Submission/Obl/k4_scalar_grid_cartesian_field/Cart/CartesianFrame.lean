-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/CartesianFrame.lean;
-- only the namespace was renamed into o230's.
import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set

/-- Coordinates in the two scalar directions `(1,vr)` and `(1,vc)`
based at `(t0,y0)`. -/
noncomputable def cartesianFrameCoordinates (t0 y0 vr vc t y : ℝ) : Fin 2 → ℝ :=
  ![(vc*(t-t0)-(y-y0))/(vc-vr), ((y-y0)-vr*(t-t0))/(vc-vr)]

theorem cartesianFrame_time_reconstruction (t0 y0 vr vc t y : ℝ) (hsep : vc ≠ vr) :
    t0+cartesianFrameCoordinates t0 y0 vr vc t y 0+
      cartesianFrameCoordinates t0 y0 vr vc t y 1=t := by
  dsimp only [cartesianFrameCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons]
  field_simp [sub_ne_zero.mpr hsep]
  ring

theorem cartesianFrame_space_reconstruction (t0 y0 vr vc t y : ℝ) (hsep : vc ≠ vr) :
    y0+vr*cartesianFrameCoordinates t0 y0 vr vc t y 0+
      vc*cartesianFrameCoordinates t0 y0 vr vc t y 1=y := by
  dsimp only [cartesianFrameCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons]
  field_simp [sub_ne_zero.mpr hsep]
  ring

/-- Polynomial conditioning of the actual two-direction coordinate map. -/
theorem cartesianFrame_coordinate_bound (t0 y0 vr vc t y K R : ℝ)
    (hK : 1 ≤ K) (hR : 0 ≤ R) (hvr : |vr| ≤ K) (hvc : |vc| ≤ K)
    (hsep : 1/K ≤ |vc-vr|) (ht : |t-t0| ≤ R) (hy : |y-y0| ≤ R) :
    ∀ i, |cartesianFrameCoordinates t0 y0 vr vc t y i| ≤ 2*K^2*R := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hden : 0 < |vc-vr| := (one_div_pos.mpr hKpos).trans_le hsep
  have hprod : 1 ≤ |vc-vr| * K := (div_le_iff₀ hKpos).mp hsep
  have haxis (r : ℝ) (hr : |r| ≤ K) :
      |(r*(t-t0)-(y-y0))/(vc-vr)| ≤ 2*K^2*R := by
    rw [abs_div]
    apply (div_le_iff₀ hden).2
    have hnum : |r*(t-t0)-(y-y0)| ≤ 2*K*R := by
      have hmul : |r*(t-t0)| ≤ K*R := by
        rw [abs_mul]
        exact mul_le_mul hr ht (abs_nonneg _) hKpos.le
      have h := (abs_sub (r*(t-t0)) (y-y0)).trans
        (add_le_add hmul hy)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2*K*R)
    nlinarith
  intro i
  fin_cases i
  · exact haxis vc hvc
  · change |((y-y0)-vr*(t-t0))/(vc-vr)| ≤ 2*K^2*R
    rw [abs_div,abs_sub_comm]
    simpa only [abs_div] using haxis vr hvr

/-- The time displacement of a grid center costs only the sum of its
two Cartesian coordinate displacements. -/
theorem cartesianFrame_cell_time_error (t0 y0 vr vc t y xCenter yCenter δ : ℝ)
    (hsep : vc ≠ vr)
    (hclose : |cartesianFrameCoordinates t0 y0 vr vc t y 0-xCenter|+
      |cartesianFrameCoordinates t0 y0 vr vc t y 1-yCenter| ≤ δ) :
    |t-(t0+xCenter+yCenter)| ≤ δ := by
  have ht := cartesianFrame_time_reconstruction t0 y0 vr vc t y hsep
  calc
    _ = |(cartesianFrameCoordinates t0 y0 vr vc t y 0-xCenter)+
        (cartesianFrameCoordinates t0 y0 vr vc t y 1-yCenter)| := by
      congr 1
      linarith
    _ ≤ _ := (abs_add_le _ _).trans hclose

/-- A cell center near an original unit-time source remains in the
fixed signed time box used for the original coefficient bins. -/
theorem cartesianFrame_cell_time_bound (t0 y0 vr vc t y xCenter yCenter δ : ℝ)
    (hsep : vc ≠ vr) (ht : t ∈ Icc (0 : ℝ) 1) (hδ : δ ≤ 1)
    (hclose : |cartesianFrameCoordinates t0 y0 vr vc t y 0-xCenter|+
      |cartesianFrameCoordinates t0 y0 vr vc t y 1-yCenter| ≤ δ) :
    |t0+xCenter+yCenter| ≤ 2 := by
  have hdist := cartesianFrame_cell_time_error t0 y0 vr vc t y xCenter yCenter δ hsep hclose
  have hdist' : |(t0+xCenter+yCenter)-t| ≤ δ := by
    simpa only [abs_sub_comm] using hdist
  have habst : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have htri := abs_add_le ((t0+xCenter+yCenter)-t) t
  rw [sub_add_cancel] at htri
  linarith

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
