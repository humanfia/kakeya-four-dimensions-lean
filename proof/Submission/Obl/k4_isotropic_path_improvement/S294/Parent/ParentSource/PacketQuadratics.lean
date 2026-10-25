-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketQuadratics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketQuadratics.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketQuadratics.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketQuadratics.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketGeometry
import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry

/-! # Canonical measurable native quadratic coefficients -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

def normalizedPacketCurve {W : ℕ} (Nk : ℝ) (p : Native.PathData W) (b : Fin p.C)
    (l : Line) (t : ℝ) : ℝ :=
  MvPolynomial.eval (xp (normalizedPacketLine p b l) t) (normalizedPacketTest Nk p b)

/-- Use the accepted three-sample coefficients, ordered as constant,
linear and quadratic terms. They are actual functions of the original line. -/
def normalizedPacketCoefficients {W : ℕ} (Nk : ℝ) (p : Native.PathData W)
    (b : Fin p.C) (l : Line) : EuclideanSpace ℝ (Fin 3) :=
  k4_horizon_chart_assembly.quadraticCoefficients (normalizedPacketCurve Nk p b l)

theorem measurable_normalizedPacketCurve {W : ℕ} (Nk : ℝ) (p : Native.PathData W)
    (b : Fin p.C) : Measurable (fun q : Line × ℝ => normalizedPacketCurve Nk p b q.1 q.2) := by
  have hL : Measurable (fun q : Line × ℝ => normalizedPacketLine p b q.1) :=
    (measurable_normalizedPacketLine p b).comp measurable_fst
  have hc (j : Fin 6) : Measurable (fun q : Line × ℝ =>
      (normalizedPacketLine p b q.1).2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp hL)
  have hpoint : Measurable (fun q : Line × ℝ => xp (normalizedPacketLine p b q.1) q.2) := by
    unfold xp
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i
    · exact measurable_snd
    · exact (hc 0).add (measurable_snd.mul (hc 3))
    · exact (hc 1).add (measurable_snd.mul (hc 4))
    · exact (hc 2).add (measurable_snd.mul (hc 5))
  exact (MvPolynomial.continuous_eval (normalizedPacketTest Nk p b)).measurable.comp hpoint

theorem measurable_normalizedPacketCoefficients {W : ℕ} (Nk : ℝ) (p : Native.PathData W)
    (b : Fin p.C) : Measurable (normalizedPacketCoefficients Nk p b) := by
  have heval (t : ℝ) : Measurable (fun l : Line => normalizedPacketCurve Nk p b l t) := by
    have hm : Measurable (fun l : Line => (l, t)) := measurable_id.prodMk measurable_const
    exact (measurable_normalizedPacketCurve Nk p b).comp (f := fun l : Line => (l, t)) hm
  have h₀ := heval 0
  have hhalf := heval (1 / 2)
  have h₁ := heval 1
  unfold normalizedPacketCoefficients k4_horizon_chart_assembly.quadraticCoefficients
  apply (PiLp.volume_preserving_toLp (Fin 3)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact h₀
  · exact (h₁.neg.add (hhalf.const_mul 4)).sub (h₀.const_mul 3)
  · exact ((h₁.const_mul 2).sub (hhalf.const_mul 4)).add (h₀.const_mul 2)

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem normalizedPacketCurve_quadratic (b : Fin p.C) (l : Line) :
    k4_eligibility_sign_description.Quadratic (normalizedPacketCurve Nk p b l) :=
  k4_horizon_chart_assembly.native_quadratic (normalizedPacketTest Nk p b)
    (normalizedPacketTest_degree hp b) (normalizedPacketLine p b l)

/-- The actual normalized native test has its canonical quadratic
trajectory identity on the original line parameter. -/
theorem normalizedPacket_quadratic_identity (b : Fin p.C) (l : Line) (t : ℝ) :
    MvPolynomial.eval
      (fun j => normalizedPacketPosition p b l j + t * normalizedPacketVelocity p b l j)
      (normalizedPacketTest Nk p b) =
        normalizedPacketCoefficients Nk p b l 2 * t ^ 2 +
          normalizedPacketCoefficients Nk p b l 1 * t + normalizedPacketCoefficients Nk p b l 0 := by
  have h := k4_horizon_chart_assembly.quadraticCoefficients_eval
    (normalizedPacketCurve_quadratic hp b l) t
  calc
    _ = normalizedPacketCurve Nk p b l t := by rw [← normalizedPacketMotion]; rfl
    _ = normalizedPacketCoefficients Nk p b l 0 +
        t * normalizedPacketCoefficients Nk p b l 1 +
        t ^ 2 * normalizedPacketCoefficients Nk p b l 2 := h.symm
    _ = _ := by ring

/-- Coefficient size depends on the actual native value bound, independently
of the format or the original trajectory coefficients. -/
theorem normalizedPacketCoefficients_bound (b : Fin p.C) (l : Line) (hl : l ∈ p.A b) :
    ‖normalizedPacketCoefficients Nk p b l‖ ≤ 17 * p.κ :=
  k4_horizon_chart_assembly.quadraticCoefficients_norm_le
    (fun t ht => (normalizedPacket_native_bounds hp b l hl t ht).2.1)

theorem normalizedPacketSignalVelocity_bound (b : Fin p.C) (l : Line) (hl : l ∈ p.A b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |2 * normalizedPacketCoefficients Nk p b l 2 * t +
      normalizedPacketCoefficients Nk p b l 1| ≤ 51 * p.κ := by
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hcoeff (j : Fin 3) : |normalizedPacketCoefficients Nk p b l j| ≤ 17 * p.κ :=
    (PiLp.norm_apply_le _ _).trans (normalizedPacketCoefficients_bound hp b l hl)
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  calc
    _ ≤ |2 * normalizedPacketCoefficients Nk p b l 2 * t| +
        |normalizedPacketCoefficients Nk p b l 1| := abs_add_le _ _
    _ = 2 * |normalizedPacketCoefficients Nk p b l 2| * |t| +
        |normalizedPacketCoefficients Nk p b l 1| := by norm_num [abs_mul]
    _ ≤ 2 * (17 * p.κ) * 1 + 17 * p.κ := by
      gcongr <;> exact hcoeff _
    _ = _ := by ring

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
