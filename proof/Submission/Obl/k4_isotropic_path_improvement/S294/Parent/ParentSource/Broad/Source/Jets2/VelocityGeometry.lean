-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.VelocityGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/VelocityGeometry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/Jets2/VelocityGeometry.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.NativeVelocityGraph

/-! # Physical quadratic trajectories from the seven coefficients

The generic MK4 backend allows a different quadratic polynomial for
every trajectory. Its actual physical curve can therefore be built from
the seven coefficients without using an old chart's unrelated test.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open MeasureTheory Set MvPolynomial
open SourceGeometry Broad.Velocity
noncomputable section

def coefficientTest (c : Fin 7 → ℝ) : MvPolynomial (Fin 4) ℝ :=
  C (c 0)+C (c 1)*X 0+C (c 2)*(X 0)^2

def coefficientPosition (c : Fin 7 → ℝ) : Fin 4 → ℝ := ![0,c 3,c 5,0]

def coefficientVelocity (c : Fin 7 → ℝ) : Fin 4 → ℝ := ![1,c 4,c 6,0]

def coefficientBase (c : Fin 7 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun j : Fin 3 => coefficientVelocity c j.castSucc)

def coefficientPhysical (c : Fin 7 → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![t,zy c t 0,zy c t 1,zx c t]

def coefficientTangent (c : Fin 7 → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  liftedVector (fun j => coefficientVelocity c j.castSucc) (2*c 2*t+c 1)

theorem coefficient_quadratic (c : Fin 7 → ℝ) (t : ℝ) :
    eval (fun j => coefficientPosition c j+t*coefficientVelocity c j) (coefficientTest c) =
      c 2*t^2+c 1*t+c 0 := by
  simp only [coefficientTest,map_add,map_mul,map_pow,eval_C,eval_X,
    coefficientPosition,coefficientVelocity,Matrix.cons_val_zero,zero_add,mul_one]
  ring

theorem coefficient_physical_eq_native (c : Fin 7 → ℝ) (t : ℝ) :
    nativePhysicalCurve (coefficientTest c) (coefficientPosition c) (coefficientVelocity c) t =
      coefficientPhysical c t := by
  rw [nativePhysicalCurve,coefficient_quadratic]
  ext j
  fin_cases j <;> simp [liftedVector,coefficientPhysical,coefficientPosition,
    coefficientVelocity,zx,zy] <;> ring

theorem measurable_coefficientPhysical {Λ : Type*} [MeasurableSpace Λ]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) :
    Measurable (fun z : Λ×ℝ => coefficientPhysical (c z.1) z.2) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j <;> dsimp [coefficientPhysical,zx,zy]
  all_goals fun_prop

theorem measurable_coefficientTangent {Λ : Type*} [MeasurableSpace Λ]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) :
    Measurable (fun z : Λ×ℝ => coefficientTangent (c z.1) z.2) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j <;> dsimp [coefficientTangent,liftedVector,coefficientVelocity]
  all_goals fun_prop

theorem coefficient_value_bound {H : ℝ} (hH : 0 ≤ H) {c : Fin 7 → ℝ}
    (hc : ∀ j, |c j|≤H) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : |zx c t|≤3*H := by
  have ht1 : |t|≤1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have ht2 : |t^2|≤1 := by rw [abs_pow]; nlinarith [abs_nonneg t]
  have hlinear : |c 1*t|≤H := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hc 1) (abs_nonneg t)).trans
      (mul_le_of_le_one_right hH ht1)
  have hquad : |c 2*t^2|≤H := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hc 2) (abs_nonneg _)).trans
      (mul_le_of_le_one_right hH ht2)
  calc
    _ ≤ |c 0+c 1*t|+|c 2*t^2| := abs_add_le _ _
    _ ≤ (|c 0|+|c 1*t|)+|c 2*t^2| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 3*H := by linarith [hc 0]

theorem coefficient_rate_bound {H : ℝ} (hH : 0 ≤ H) {c : Fin 7 → ℝ}
    (hc : ∀ j, |c j|≤H) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : |2*c 2*t+c 1|≤3*H := by
  have ht1 : |t|≤1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  calc
    _ ≤ |2*c 2*t|+|c 1| := abs_add_le _ _
    _ = 2* |c 2| * |t|+|c 1| := by rw [abs_mul,abs_mul]; norm_num
    _ ≤ 2*H*1+H := by gcongr; exact hc 2; exact hc 1
    _ = _ := by ring

theorem coefficient_tangent_bound {H : ℝ} (hH : 1 ≤ H) {c : Fin 7 → ℝ}
    (hc : ∀ j, |c j|≤H) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖coefficientTangent c t‖≤6*H := by
  have hrate := coefficient_rate_bound (zero_le_one.trans hH) hc ht
  have hsum : (∑ j : Fin 4, |coefficientTangent c t j|)≤6*H := by
    rw [Fin.sum_univ_four]
    change |(1:ℝ)| + |c 4| + |c 6| + |2*c 2*t+c 1|≤6*H
    norm_num only [abs_one]
    linarith [hc 4,hc 6]
  exact (Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _).trans hsum


/-- Intercepts are irrelevant to the scalar rate. -/
theorem coefficient_rate_bound_of_jets {H : ℝ} (hH : 0 ≤ H) {c : Fin 7 → ℝ}
    (h1 : |c 1| ≤ H) (h2 : |c 2| ≤ H) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |2*c 2*t+c 1| ≤ 3*H := by
  have ht1 : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  calc
    _ ≤ |2*c 2*t| + |c 1| := abs_add_le _ _
    _ = 2* |c 2| * |t| + |c 1| := by rw [abs_mul,abs_mul]; norm_num
    _ ≤ 2*H*1+H := by gcongr
    _ = _ := by ring

/-- The full tangent uses only the two signal jets and two planar
velocities. Signal and spatial intercepts may be arbitrarily large. -/
theorem coefficient_tangent_bound_of_jets {H : ℝ} (hH : 1 ≤ H) {c : Fin 7 → ℝ}
    (h1 : |c 1| ≤ H) (h2 : |c 2| ≤ H) (h4 : |c 4| ≤ H) (h6 : |c 6| ≤ H)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖coefficientTangent c t‖ ≤ 6*H := by
  have hrate := coefficient_rate_bound_of_jets (zero_le_one.trans hH) h1 h2 ht
  have hsum : (∑ j : Fin 4, |coefficientTangent c t j|) ≤ 6*H := by
    rw [Fin.sum_univ_four]
    change |(1:ℝ)| + |c 4| + |c 6| + |2*c 2*t+c 1| ≤ 6*H
    norm_num only [abs_one]
    linarith
  exact (Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _).trans hsum

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
