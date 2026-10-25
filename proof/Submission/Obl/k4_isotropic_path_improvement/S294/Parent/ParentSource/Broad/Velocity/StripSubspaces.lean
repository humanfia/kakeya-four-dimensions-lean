-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.StripSubspaces, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/StripSubspaces.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/StripSubspaces.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.PlaneGraph
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CellBreadth

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set SourceGeometry
open scoped ENNReal

noncomputable section

def baseVelocityLift (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![1, a * v 0, a * v 1]

/-- Near any proper base subspace, bounded normalized velocities lie in a
single affine planar strip. The old velocity scale may be arbitrarily large. -/
theorem subspace_near_base_lift_strip {a width : ℝ} (ha : 1 ≤ a)
    (hw : 0 ≤ width) (hw1 : width ≤ 1)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (hV : Module.finrank ℝ V < 3) :
    ∃ n center : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 ∧
      ∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ ≤ 1 →
        Metric.infDist (baseVelocityLift a v) (V : Set _) < width / 8 →
          |inner ℝ n (v - center)| ≤ width := by
  classical
  by_cases hex : ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ ≤ 1 ∧
      Metric.infDist (baseVelocityLift a v) (V : Set _) < width / 8
  · obtain ⟨v₀, hv₀, hnear₀⟩ := hex
    obtain ⟨N, hN, horth⟩ := exists_unit_subspace_normal V hV
    let planar : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![N 1, N 2]
    let m : EuclideanSpace ℝ (Fin 2) := a • planar
    have hidentity (v : EuclideanSpace ℝ (Fin 2)) :
        inner ℝ N (baseVelocityLift a v) = N 0 + inner ℝ m v := by
      simp [baseVelocityLift, m, planar, PiLp.inner_apply,
        Fin.sum_univ_three, Fin.sum_univ_two]
      ring
    have hres (v : EuclideanSpace ℝ (Fin 2)) :
        |N 0 + inner ℝ m v| ≤ Metric.infDist (baseVelocityLift a v) (V : Set _) := by
      rw [← hidentity]
      exact abs_inner_le_plane_distance V N _ hN horth
    have hscale : ‖planar‖ ≤ ‖m‖ := by
      dsimp [m]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans ha)]
      nlinarith [norm_nonneg planar]
    have hN1 : |N 1| ≤ ‖m‖ := by
      exact (show |N 1| ≤ ‖planar‖ by simpa [planar] using PiLp.norm_apply_le planar 0).trans hscale
    have hN2 : |N 2| ≤ ‖m‖ := by
      exact (show |N 2| ≤ ‖planar‖ by simpa [planar] using PiLp.norm_apply_le planar 1).trans hscale
    have hNl1 : 1 ≤ |N 0| + |N 1| + |N 2| := by
      have hh := Submission.Obl.k4_adapted_oscillation_tests.norm_apply_le_sum_abs
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) (fun i => by simp) N
      simpa only [ContinuousLinearMap.id_apply, hN, Fin.sum_univ_three, Real.norm_eq_abs] using hh
    have hinner : |inner ℝ m v₀| ≤ ‖m‖ :=
      (abs_real_inner_le_norm m v₀).trans (by nlinarith [norm_nonneg m])
    have hN0 : |N 0| ≤ width / 8 + ‖m‖ := by
      calc
        |N 0| = |(N 0 + inner ℝ m v₀) - inner ℝ m v₀| := by ring_nf
        _ ≤ |N 0 + inner ℝ m v₀| + |inner ℝ m v₀| := abs_sub _ _
        _ ≤ width / 8 + ‖m‖ := add_le_add ((hres v₀).trans hnear₀.le) hinner
    have hm : (1 : ℝ) / 4 ≤ ‖m‖ := by linarith
    have hmpos : 0 < ‖m‖ := by linarith
    let n : EuclideanSpace ℝ (Fin 2) := ‖m‖⁻¹ • m
    have hn : ‖n‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hmpos)
    let center : EuclideanSpace ℝ (Fin 2) := (-(N 0) / ‖m‖) • n
    refine ⟨n, center, hn, ?_⟩
    intro v hv hnear
    have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
    have hid : inner ℝ n (v - center) = (N 0 + inner ℝ m v) / ‖m‖ := by
      rw [inner_sub_right]
      dsimp only [center]
      rw [real_inner_smul_right, hnn, mul_one]
      simp only [n, real_inner_smul_left]
      ring
    rw [hid, abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]
    have hh := (hres v).trans hnear.le
    nlinarith [mul_le_mul_of_nonneg_left hm hw]
  · refine ⟨WithLp.toLp 2 ![1, 0], 0, ?_, ?_⟩
    · norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    · intro v hv hnear
      exact False.elim (hex ⟨v, hv, hnear⟩)

/-- Planar strip ceilings imply proper-subspace breadth for the actual
three base velocities, using the same incidence law and denominator. -/
theorem base_breadth_of_planar_strip_caps {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v : X → EuclideanSpace ℝ (Fin 2))
    {a width fraction : ℝ} (ha : 1 ≤ a) (hw : 0 ≤ width) (hw1 : width ≤ 1)
    (hfraction : 0 ≤ fraction) (hbound : ∀ᵐ x ∂μ, ‖v x‖ ≤ 1)
    (hstrip : ∀ n center : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 →
      μ {x | |inner ℝ n (v x - center)| ≤ width} ≤ ENNReal.ofReal fraction * μ univ) :
    ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), Module.finrank ℝ V < 3 →
      (1 - fraction) * μ.real univ ≤
        μ.real {x | width / 8 ≤ Metric.infDist (baseVelocityLift a (v x)) (V : Set _)} := by
  intro V hV
  obtain ⟨n, center, hn, hnear⟩ := subspace_near_base_lift_strip ha hw hw1 V hV
  let outside := {x | width / 8 ≤ Metric.infDist (baseVelocityLift a (v x)) (V : Set _)}
  let strip := {x | |inner ℝ n (v x - center)| ≤ width}
  have hcover : (univ : Set X) ≤ᵐ[μ] outside ∪ strip := by
    filter_upwards [hbound] with x hx _
    by_cases hout : x ∈ outside
    · exact Or.inl hout
    · exact Or.inr (hnear (v x) hx (lt_of_not_ge hout))
  have hmass : μ univ ≤ μ outside + μ strip :=
    (measure_mono_ae hcover).trans (measure_union_le _ _)
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩) hmass
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hreal
  have hstripReal : μ.real strip ≤ fraction * μ.real univ := by
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)) (hstrip n center hn)
    simpa only [strip, measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hfraction] using hh
  change (1 - fraction) * (μ univ).toReal ≤ (μ outside).toReal
  change (μ strip).toReal ≤ fraction * (μ univ).toReal at hstripReal
  nlinarith

theorem cell_base_breadth_of_planar_strip_caps {X I : Type*} [MeasurableSpace X]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : Measure X) [IsFiniteMeasure μ] (code : X → I) (hcode : Measurable code)
    (v : X → EuclideanSpace ℝ (Fin 2)) {a width fraction : ℝ}
    (ha : 1 ≤ a) (hw : 0 ≤ width) (hw1 : width ≤ 1) (hfraction : 0 ≤ fraction)
    (hbound : ∀ᵐ x ∂μ, ‖v x‖ ≤ 1)
    (hstrip : ∀ label (n center : EuclideanSpace ℝ (Fin 2)), ‖n‖ = 1 →
      μ {x | code x = label ∧ |inner ℝ n (v x - center)| ≤ width} ≤
        ENNReal.ofReal fraction * μ (code ⁻¹' {label})) :
    ∀ label (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V < 3 →
      (1 - fraction) * (μ.restrict (code ⁻¹' {label})).real univ ≤
        (μ.restrict (code ⁻¹' {label})).real
          {x | width / 8 ≤ Metric.infDist (baseVelocityLift a (v x)) (V : Set _)} := by
  intro label
  apply base_breadth_of_planar_strip_caps (μ.restrict (code ⁻¹' {label})) v
    ha hw hw1 hfraction ((ae_mono Measure.restrict_le_self) hbound)
  intro n center hn
  have hh := hstrip label n center hn
  rw [Measure.restrict_apply' (hcode (measurableSet_singleton label)),
    Measure.restrict_apply_univ]
  convert hh using 2
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, and_comm]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
