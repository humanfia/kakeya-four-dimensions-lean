/-
Adapted from this LOT tree, obligation o093, session x0535, commit 05931f40,
Submission/Obl/k4_scalar_critical_path_terminal/PacketGraphBounds.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.RawCeiling

/-! A current observation ceiling and a current packet mass floor give a
global quadratic predictor bound. The geometric and Remez estimates are
the gate-accepted scalar packet estimates. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PacketGraphs

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

noncomputable section

/-- The accepted thin-packet estimate also applies to a law specified by
an observation ceiling, without choosing its density in advance. -/
theorem packet_mass_le_sublevel {μ : Measure (Coeff × ℝ)} {a : ℝ} (ha : 0 < a)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcap : μ.map (obsL a) ≤ C • (volume.prod (Measure.count : Measure ℤ)))
    {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) {A : Set Coeff} {s q c₀ c₁ w Λ A₀ : ℝ}
    (hΛ : 0 ≤ Λ)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc s (s + q),
      |spatial l t - (c₀ + c₁ * t)| ≤ w ∧ |hidden l t - f t (spatial l t)| ≤ Λ * a)
    (hval : ∀ l ∈ A, ∀ t ∈ Icc s (s + q), |f t (spatial l t)| ≤ A₀) :
    μ (A ×ˢ Icc s (s + q)) ≤ C * (ENNReal.ofReal (2 * Λ + 3) *
      volume {p : ℝ × ℝ | p.1 ∈ Icc s (s + q) ∧
        |p.2 - (c₀ + c₁ * p.1)| ≤ w ∧ |f p.1 p.2| ≤ A₀}) := by
  obtain ⟨hg, hmap, hbound⟩ :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw.exists_density_le hC hcap
  let g := (μ.map (obsL a)).rnDeriv (volume.prod (Measure.count : Measure ℤ))
  have hbad : MeasurableSet {z | C < g z} := measurableSet_lt measurable_const hg
  have hzero : (volume.prod (Measure.count : Measure ℤ)) {z | C < g z} = 0 := by
    simpa only [ae_iff, not_le] using hbound
  have hnull : μ {z | C < g (obsL a z)} = 0 := by
    have h := hcap {z | C < g z}
    rw [Measure.map_apply (measurable_obsL a) hbad, Measure.smul_apply,
      hzero, smul_zero] at h
    exact le_antisymm h bot_le
  calc
    _ = μ ((A ×ˢ Icc s (s + q)) \ {z | C < g (obsL a z)}) :=
      (measure_sdiff_null hnull).symm
    _ ≤ _ := thin_packet_diff_le hg ha hmap hf hΛ hconf hval C

/-- The floor is imposed on the current law. Hence the predictor estimate
remains valid after the simultaneous packet-floor restoration. -/
theorem packet_graph_bound {μ : Measure (Coeff × ℝ)} {a : ℝ} (ha : 0 < a)
    {C : ℝ≥0∞} (hC₀ : C ≠ 0) (hC : C ≠ ∞)
    (hcap : μ.map (obsL a) ≤ C • (volume.prod (Measure.count : Measure ℤ)))
    {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) {A : Set Coeff} {s q c₀ c₁ w Λ A₀ lam : ℝ}
    (hq : 0 < q) (hw : 0 < w) (hΛ : 0 ≤ Λ) (hlam : 0 < lam)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc s (s + q),
      |spatial l t - (c₀ + c₁ * t)| ≤ w ∧ |hidden l t - f t (spatial l t)| ≤ Λ * a)
    (hval : ∀ l ∈ A, ∀ t ∈ Icc s (s + q), |f t (spatial l t)| ≤ A₀)
    (hfloor : (C * ENNReal.ofReal (2 * Λ + 3)) *
      ENNReal.ofReal (lam * (q * (2 * w))) ≤ μ (A ×ˢ Icc s (s + q)))
    (t : ℝ) (ht : t ∈ Icc s (s + q)) (y : ℝ) :
    |f t y| ≤ 186624 * A₀ * (3 + |y - (c₀ + c₁ * t)| / w) ^ 2 / lam ^ 4 := by
  have hmass := packet_mass_le_sublevel ha hC hcap hf hΛ hconf hval
  have hprod : C * ENNReal.ofReal (2 * Λ + 3) ≠ 0 :=
    mul_ne_zero hC₀ (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hprodTop : C * ENNReal.ofReal (2 * Λ + 3) ≠ ∞ :=
    ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  have h := mul_le_mul'
    (show (C * ENNReal.ofReal (2 * Λ + 3))⁻¹ ≤
      (C * ENNReal.ofReal (2 * Λ + 3))⁻¹ from le_rfl) (hfloor.trans hmass)
  simp only [← mul_assoc, ENNReal.inv_mul_cancel hprod hprodTop, one_mul] at h
  apply quad_remez_parallelogram hf hq hw hlam ?_ t ht y
  simpa only [mul_assoc] using h

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PacketGraphs
