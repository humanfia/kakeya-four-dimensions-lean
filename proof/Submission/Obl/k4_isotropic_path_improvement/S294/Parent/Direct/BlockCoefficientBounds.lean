-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Direct.BlockCoefficientBounds, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/Direct/BlockCoefficientBounds.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct.HighCurvature
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ClockParentCoefficients

/-! Local amplitude bounds for the exact original block coefficient table.
Unlike a bound obtained from the full original unit interval, this retains
the small amplitude of the physical residual. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct

open Set MvPolynomial
open Submission.Lib.K4GlobalParentSignal
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

noncomputable section

/-- A quadratic bounded on the actual old block has small coefficients
in the unit old clock, with no inverse clock or inverse thickness cost. -/
theorem oldBlock_local_signal_bounds (P : Po) (hP : P.totalDegree ≤ 2)
    (t0 h : ℝ) (c u : P2) (l : Ln) {M : ℝ}
    (hbound : ∀ t∈Icc (0 : ℝ) 1, |eval (xp l (t0+h*t)) P| ≤ M) :
    |oldBlockCoefficients P t0 h c u l 0| ≤ M ∧
      |oldBlockCoefficients P t0 h c u l 1| ≤ 8*M ∧
      |oldBlockCoefficients P t0 h c u l 2| ≤ 8*M := by
  let v := oldBlockCoefficients P t0 h c u l
  have hb (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
      |v 0+v 1*t+v 2*t^2| ≤ M := by
    change |Jets2.zx v t| ≤ M
    rw [oldBlock_signal hP]
    exact hbound t ht
  have h0 := hb 0 (by norm_num)
  have hhalf := hb (1/2) (by norm_num)
  have h1 := hb 1 (by norm_num)
  norm_num only [mul_zero, pow_two, zero_mul, add_zero, mul_one, one_mul] at h0 h1
  have hh := abs_le.mp hhalf
  have hzero := abs_le.mp h0
  have hone := abs_le.mp h1
  refine ⟨h0,?_,?_⟩
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-- The physical residual's normalized signal table. The base and planar
velocity entries are kept exactly as in the original unsheared block. -/
def amplitudeBlockCoefficients (P : Po) (a t0 h : ℝ) (c u : P2) (l : Ln) : Fin 7 → ℝ :=
  scaleSignal a⁻¹ (oldBlockCoefficients P t0 h c u l)

theorem amplitudeBlock_signal (P : Po) (hP : P.totalDegree ≤ 2)
    (a t0 h : ℝ) (c u : P2) (l : Ln) (t : ℝ) :
    Jets2.zx (amplitudeBlockCoefficients P a t0 h c u l) t =
      a⁻¹*eval (xp l (t0+h*t)) P := by
  rw [amplitudeBlockCoefficients,scaleSignal_zx,oldBlock_signal hP]
  rfl

theorem amplitudeBlock_rate (P : Po) (hP : P.totalDegree ≤ 2)
    (a t0 h : ℝ) (c u : P2) (l : Ln) (t : ℝ) :
    amplitudeBlockCoefficients P a t0 h c u l 1+
      2*amplitudeBlockCoefficients P a t0 h c u l 2*t =
        (h/a)*rate P l (t0+h*t) := by
  have hr := oldBlock_rate hP t0 h c u l t
  change a⁻¹*oldBlockCoefficients P t0 h c u l 1+
    2*(a⁻¹*oldBlockCoefficients P t0 h c u l 2)*t = _
  calc
    _ = a⁻¹*(oldBlockCoefficients P t0 h c u l 1+
        2*oldBlockCoefficients P t0 h c u l 2*t) := by ring
    _ = a⁻¹*(h*rate P l (t0+h*t)) := by rw [hr]
    _ = _ := by ring

/-- Dividing a signal of amplitude `K*a` by `a` costs only `8*K` in
its three scalar coefficients. -/
theorem amplitudeBlock_local_signal_bounds (P : Po) (hP : P.totalDegree ≤ 2)
    (t0 h : ℝ) (c u : P2) (l : Ln) {a K : ℝ} (ha : 0 < a)
    (hbound : ∀ t∈Icc (0 : ℝ) 1, |eval (xp l (t0+h*t)) P| ≤ K*a) :
    |amplitudeBlockCoefficients P a t0 h c u l 0| ≤ K ∧
      |amplitudeBlockCoefficients P a t0 h c u l 1| ≤ 8*K ∧
      |amplitudeBlockCoefficients P a t0 h c u l 2| ≤ 8*K := by
  obtain ⟨h0,h1,h2⟩ := oldBlock_local_signal_bounds P hP t0 h c u l hbound
  have hscaled (x C : ℝ) (hx : |x| ≤ C*a) : |a⁻¹*x| ≤ C := by
    rw [abs_mul,abs_of_pos (inv_pos.mpr ha)]
    calc
      _ ≤ a⁻¹*(C*a) := mul_le_mul_of_nonneg_left hx (inv_pos.mpr ha).le
      _ = C := by field_simp
  refine ⟨hscaled _ K h0,?_,?_⟩
  · exact hscaled _ (8*K) (by simpa only [mul_assoc] using h1)
  · exact hscaled _ (8*K) (by simpa only [mul_assoc] using h2)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct
