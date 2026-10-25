import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.SheetBounds
import Submission.Obl.k4_algebraic_sheet_remez.Rays
import Submission.Obl.k4_algebraic_sheet_remez.Geometry
import Submission.Obl.k4_algebraic_sheet_remez.Numerics
import Submission.Obl.k4_algebraic_sheet_remez.Slices
import Submission.Obl.k4_algebraic_sheet_remez.InterpolationBound

namespace Submission.Obl.k4_algebraic_sheet_remez

open Set Metric MeasureTheory Filter
open scoped Topology
open Submission.Obl.k4_algebraic_real_jet_comparison

/-- The measurable-set comparison for positive-dimensional algebraic sheets. -/
theorem exists_sheet_remez_constant (n D : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (f : EuclideanSpace ℂ (Fin n) → ℂ), HasSheetRelation n D f →
        DifferentiableOn ℂ f (ball 0 4) →
        (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → (f (realEmbedding n x)).im = 0) →
        ∀ (E : Set (EuclideanSpace ℝ (Fin n))) (θ V : ℝ),
          MeasurableSet E → E ⊆ closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 ≤ V →
          ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
            ≤ volume E →
          (∀ x ∈ E, ‖f (realEmbedding n x)‖ ≤ V) →
          ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 →
            ‖f (realEmbedding n x)‖ ≤ C * θ ^ (-C) * V := by
  obtain ⟨B, hB, hnorm⟩ := exists_sheet_norm_constant_two n D
  obtain ⟨c, hc, hc1, hray⟩ := exists_volume_ray_constant n hn
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 4 / 5) (by norm_num : (4 / 5 : ℝ) < 1)
  have hlim : Tendsto (fun q : ℕ => B * (4 / 5 : ℝ) ^ q) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow
  obtain ⟨q, hqsmall, hq⟩ := ((hlim.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and (eventually_ge_atTop 1)).exists
  let A := 2 * (q : ℝ) * (4 * ((q : ℝ) + 1) / c) ^ q
  obtain ⟨C, hC, hcommon⟩ := exists_common_power_constant A q
  refine ⟨C, hC, ?_⟩
  intro f hrel hf hreal E θ V hE hEsub hθ hθ1 hV hmass hval x hx
  have hcont : ContinuousOn (fun y : EuclideanSpace ℝ (Fin n) => ‖f (realEmbedding n y)‖)
      (closedBall 0 (1 / 2)) := by
    apply (hf.continuousOn.comp (realEmbedding n).continuous.continuousOn ?_).norm
    intro y hy
    rw [mem_ball, dist_zero_right, LinearIsometry.norm_map]
    have hy' := mem_closedBall_zero_iff.mp hy
    linarith
  obtain ⟨w, hw, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)).exists_isMaxOn
    (by exact ⟨0, by simp⟩) hcont
  have hw' : ‖w‖ ≤ (1 : ℝ) / 2 := mem_closedBall_zero_iff.mp hw
  let S := ‖f (realEmbedding n w)‖
  have hS : 0 ≤ S := norm_nonneg _
  have hbase : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ (1 : ℝ) / 2 →
      ‖f (realEmbedding n y)‖ ≤ S := by
    intro y hy
    exact hmax (mem_closedBall_zero_iff.mpr hy)
  by_cases hS0 : S = 0
  · exact (hbase x hx).trans (by rw [hS0]; positivity)
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
  have hbound := hnorm f hrel hf S hSpos hbase
  obtain ⟨v, hv, hmassray⟩ := hray E θ hE hEsub hθ hmass w hw'
  let R : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ w + t • v ∈ E}
  have hη : 0 < c * θ := mul_pos hc hθ
  have hη1 : c * θ ≤ 1 := (mul_le_mul hc1 hθ1 hθ.le zero_le_one).trans_eq (by ring)
  have hRne : R.Nonempty := nonempty_of_measure_ne_zero
    (ne_of_gt ((ENNReal.ofReal_pos.mpr hη).trans_le hmassray))
  obtain ⟨T, hT, hRT, hend⟩ := exists_ray_endpoint w v R hRne
    (fun t ht => ht.1) (fun t ht => mem_closedBall_zero_iff.mp (hEsub ht.2))
  let g : ℝ → ℝ := fun t => (f (realEmbedding n w + (t : ℂ) • realEmbedding n v)).re
  have hg : ContDiffOn ℝ q g (Ioo (-2 : ℝ) 2) := contDiffOn_slice hf w v hw' hv.le q
  have hgval : ∀ t ∈ R, |g t| ≤ V := by
    intro t ht
    dsimp only [g]
    rw [← realEmbedding_line]
    exact (Complex.abs_re_le_norm _).trans (hval _ ht.2)
  have hgderiv := slice_derivative_decay hf hbound w v hw' hv.le hT.1 hend q
  have hint := slice_interpolation_bound q hT.1 hT.2 hη hη1 hV (mul_pos hB hSpos).le
    hg R hRT hmassray hgval hgderiv
  have hg0 : |g 0| = S := by
    simp only [g, Complex.ofReal_zero, zero_smul, add_zero]
    exact Complex.abs_re_eq_norm.mpr (hreal w (by linarith))
  rw [hg0] at hint
  have herr : (B * S) * (4 / 5 : ℝ) ^ q ≤ S / 2 := by
    have hh := mul_le_mul_of_nonneg_right hqsmall.le hS
    nlinarith
  have hSbound : S ≤ 2 * (q : ℝ) * (4 * ((q : ℝ) + 1) / (c * θ)) ^ q * V := by
    linarith [hint]
  have hfactor : 2 * (q : ℝ) * (4 * ((q : ℝ) + 1) / (c * θ)) ^ q * V =
      A * (θ ^ q)⁻¹ * V := by
    have hquot : 4 * ((q : ℝ) + 1) / (c * θ) = (4 * ((q : ℝ) + 1) / c) / θ := by
      rw [div_div]
    rw [hquot, div_pow, div_eq_mul_inv]
    dsimp only [A]
    ring
  rw [hfactor] at hSbound
  exact (hbase x hx).trans (hSbound.trans (hcommon θ V hθ hθ1 hV))

end Submission.Obl.k4_algebraic_sheet_remez
