/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/NarrowWidthTails.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NarrowWidths
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueAmbientCharts
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.Asymptotic

/-! Along any strict sequence of true terminal atlases with vanishing
loss, packets narrower than any fixed power of their time length have
power-small ORIGINAL weighted rectangle mass. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NarrowWidths

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open Submission.Obl.k4_scalar_normalized_exact_refinement

/-- Terminal angular typicality controls the narrow labels of the SAME
chosen true atlas on the same strict source sample sequence. -/
theorem narrowMass_powerSmall {p : Code} (hp : Exact p)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (B : ℕ) (h : ℝ)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) (hε0 : ∀ k, 0 ≤ ε k)
    (Q : ∀ k, ChartW p B (L p) (L p) (h + ε k) (ε k) true (φ k))
    {u : ℝ} (hu : 0 < u) (huU : u ≤ U p) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      narrowMass (Q k) (N p (φ k) ^ (-u)) ≤ ENNReal.ofReal (N p (φ k) ^ (-c)) := by
  have hS : 0 < S p := Analysis.RawScalar.S_pos (specExact_of_exact hp).1
  let τ : ℝ := S p * u / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let gap : ℝ := S p * u - τ
  have hgap : 0 < gap := by dsimp [gap, τ]; nlinarith [mul_pos hS hu]
  have hN1 (k : ℕ) : 1 ≤ N p (φ k) := by linarith [hp.1.1 (φ k)]
  have hN0 (k : ℕ) : 0 < N p (φ k) := by linarith [hN1 k]
  have hNt : Tendsto (fun k => N p (φ k)) atTop atTop := hp.1.2.1.comp hφ.tendsto_atTop
  have hεsmall : ∀ᶠ k in atTop, ε k ≤ gap / 6 :=
    hε.eventually (ge_mem_nhds (by positivity))
  have hlarge : ∀ᶠ k in atTop, (80 : ℝ) ≤ N p (φ k) ^ (gap / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < gap / 2)).comp hNt).eventually_ge_atTop 80
  obtain ⟨c, hc, htail⟩ := hp.2.2.2.2.2.2.2 u τ hu huU hτ
  refine ⟨c / 2, by positivity, ?_⟩
  apply Analysis.powerSmall_of_factor hNt hN1
    (ε := fun _ => 0) tendsto_const_nhds 2 (by norm_num) hc
  filter_upwards [hεsmall, hlarge, hφ.tendsto_atTop.eventually htail] with k hεk h80 hk
  have h80' : (80 : ℝ) ≤ N p (φ k) ^ (gap - 3 * ε k) :=
    h80.trans (Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith))
  have hsmall : 16 * (N p (φ k) ^ ε k) ^ 2 * (2 * N p (φ k) ^ ε k + 3) *
      N p (φ k) ^ (-f p (L p) - S p * u + τ) ≤ N p (φ k) ^ (-f p (L p)) := by
    have hcond := cond_P1 (fL := f p (L p)) (hN1 k) (hε0 k) h80'
    have heq : -f p (L p) - gap = -f p (L p) - S p * u + τ := by dsimp [gap]; ring
    rwa [heq] at hcond
  have hbound := weighted_narrow_mass_le (Q k) (hN0 k)
    (Real.rpow_pos_of_pos (hN0 k) _) (Real.rpow_nonneg (hN0 k).le _)
    (fun g => G p (φ k) g u)
    (fun g => (hp.2.2.2.1 (φ k) g u hu huU).1)
    (fun g => (hp.2.2.2.1 (φ k) g u hu huU).2) hsmall
  have hfinal := hbound.trans (mul_le_mul' le_rfl hk)
  simpa only [narrowMass, Real.rpow_zero, ENNReal.ofReal_one, one_mul] using hfinal

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NarrowWidths
