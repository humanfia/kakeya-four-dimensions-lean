/-
Adapted from this LOT tree, obligation o134, session x0438, commit 2e990309978b,
Submission/Obl/k4_scalar_guarded_tangent_obstruction/ExactLaw.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.Accessors
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.IncidenceTransport

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

open MeasureTheory Set

def originalPureException (p : RawData) (k : ℕ) (g : Fin (p.1 k)) (τ : ℝ) :
    Set Incidence := {z | p.density k g p.L
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-p.L)) z) <
        ENNReal.ofReal (p.N k ^ (-p.profile p.L - τ)) ∨
    ENNReal.ofReal (p.N k ^ (-p.profile p.L + τ)) < p.density k g p.L
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-p.L)) z)}

def originalAngularException (p : RawData) (k : ℕ) (g : Fin (p.1 k)) (a τ : ℝ) :
    Set Incidence := {z | ENNReal.ofReal (p.N k ^ (-p.profile p.L - p.S * a + τ)) <
      p.angularDensity k g a (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsG
        (p.N k ^ (-p.L)) (p.N k ^ (-a)) z)}

def originalDensityException (p : RawData) (k : ℕ) (g : Fin (p.1 k)) (a τ : ℝ) :
    Set Incidence := {z | p.density k g p.L
      ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / p.N k ^ (-p.L)⌋ : ℤ)) <
        ENNReal.ofReal (p.N k ^ (-p.profile p.L - τ)) ∨
    ENNReal.ofReal (p.N k ^ (-p.profile p.L - p.S * a + τ)) <
      p.angularDensity k g a
        (((![z.2, y z.1 z.2] : Fin 2 → ℝ),
          (⌊x z.1 z.2 / p.N k ^ (-p.L)⌋ : ℤ)),
            (⌊z.1.2 1 / p.N k ^ (-a)⌋ : ℤ))}

theorem Exact.prior_probability {p : RawData} (hp : Exact p) (k : ℕ) (g : Fin (p.1 k)) :
    IsProbabilityMeasure (p.prior k g) :=
  ((hp.2.1 k).2.2.2.1 g).1

theorem Exact.selected_finite {p : RawData} (hp : Exact p) (k : ℕ) (g : Fin (p.1 k)) :
    IsFiniteMeasure (mu p k g) := by
  let : IsProbabilityMeasure (p.prior k g) := hp.prior_probability k g
  exact Submission.Obl.k4_dyadic_crop_affine_laws.Framework.finite_selected_incidence
    (p.prior k g) (p.support k g) (((hp.2.1 k).2.2.2.1 g).2.2.2.2.1)

theorem Exact.pure_density {p : RawData} (hp : Exact p) (k : ℕ) (g : Fin (p.1 k))
    {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ p.L) :
    Measurable (p.density k g r) ∧ (mu p k g).map
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-r))) =
        (volume.prod Measure.count).withDensity (p.density k g r) := by
  exact hp.2.2.1 k g r hr hrL

theorem Exact.joint_density {p : RawData} (hp : Exact p) (k : ℕ) (g : Fin (p.1 k))
    {u : ℝ} (hu : 0 < u) (huU : u ≤ p.U) :
    Measurable (p.angularDensity k g u) ∧ (mu p k g).map
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsG
        (p.N k ^ (-p.L)) (p.N k ^ (-u))) =
        ((volume.prod Measure.count).prod Measure.count).withDensity
          (p.angularDensity k g u) := by
  exact hp.2.2.2.1 k g u hu huU

/-- Original pure and angular power windows yield a relative angular cap
without replacing the original pure density by a restricted one. -/
theorem angular_ratio_of_power_window {N a σ τ : ℝ} (hN : 0 < N) {f F : ENNReal}
    (hlo : ENNReal.ofReal (N ^ (-a - τ)) ≤ f)
    (hhi : F ≤ ENNReal.ofReal (N ^ (-a - σ + τ))) :
    F ≤ ENNReal.ofReal (N ^ (-σ + 2 * τ)) * f := by
  calc
    F ≤ ENNReal.ofReal (N ^ (-a - σ + τ)) := hhi
    _ = ENNReal.ofReal (N ^ (-σ + 2 * τ)) * ENNReal.ofReal (N ^ (-a - τ)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
      congr 2
      ring
    _ ≤ ENNReal.ofReal (N ^ (-σ + 2 * τ)) * f := by gcongr

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
