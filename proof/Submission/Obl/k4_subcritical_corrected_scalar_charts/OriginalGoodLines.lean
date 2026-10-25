/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/OriginalGoodLines.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeResolution
import Submission.Obl.k4_scalar_grid_parameter_preparation.IncidenceFacts

/-! Original good-line cuts use only original incidence null sets. The
supercritical Valid wrapper in accepted o226 OriginalGood is unavailable here;
the same elementary coordinate bounds are derived from our actual NativeLevel. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

def goodOriginalLines {α : Type*} (b : α → Fin 6 → ℝ) (H χ : ℝ) : Set α :=
  {l | (∀ e, |b l e| ≤ H) ∧ |b l 4 + b l 0| ≤ χ}

theorem measurableSet_goodOriginalLines {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (H χ : ℝ) :
    MeasurableSet (goodOriginalLines b H χ) := by
  have hcoeff : MeasurableSet {l | ∀ e, |b l e| ≤ H} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun e => measurableSet_le ((measurable_pi_apply e).comp hb).abs measurable_const
  exact hcoeff.inter (measurableSet_le
    ((((measurable_pi_apply 4).comp hb).add ((measurable_pi_apply 0).comp hb)).abs) measurable_const)

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original fitted atlas carries bounded complete trajectories and the
horizontal contact law, before any endpoint or scalar conditioning. -/
theorem NativeLevel.original_good_ae (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) :
    ∀ᵐ p ∂cfg.μ k,
      (∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k) ∧
        |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) := by
  by_cases hn : cfg.n k s = 0
  · filter_upwards [a.assignments.covers] with p hp
    obtain ⟨i, _⟩ := hp
    exact False.elim (by have hi := i.isLt; omega)
  let i : Fin (cfg.n k s) := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hP := a.assignments.native_hidden i
  obtain ⟨hb, hν, hπ, hdom, hρ, hsupp, hmass, hdegree, hparams, hfit⟩ := h.basic k
  have hbase := Submission.Obl.k4_scalar_grid_parameter_preparation.ae_original_incidence
    (cfg.ν k) (cfg.μ k) (cfg.K k) hdom hparams
  filter_upwards [hbase, hfit, a.assignments.horizontal_equation i] with p hp hfit hc
  have hx (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |cfg.b k p.1 2 + t * cfg.b k p.1 5| ≤ cfg.K k := by
    have hh := (hfit.1 t ht).1
    rw [hP, MvPolynomial.eval_X] at hh
    exact hh
  have h0 := hx 0 (by constructor <;> norm_num)
  have h1 := hx 1 (by constructor <;> norm_num)
  simp only [zero_mul, add_zero, one_mul] at h0 h1
  have h5 : |cfg.b k p.1 5| ≤ 2 * cfg.K k := by
    have hh := abs_sub (cfg.b k p.1 2 + cfg.b k p.1 5) (cfg.b k p.1 2)
    rw [show cfg.b k p.1 2 + cfg.b k p.1 5 - cfg.b k p.1 2 = cfg.b k p.1 5 by ring] at hh
    linarith
  refine ⟨?_, hc⟩
  intro e
  have hK := h.subpower.1 k
  fin_cases e <;> dsimp <;>
    linarith [abs_nonneg (cfg.b k p.1 0), abs_nonneg (cfg.b k p.1 1),
      abs_nonneg (cfg.b k p.1 3), abs_nonneg (cfg.b k p.1 4)]

/-- The conull good-line set has exactly the arbitrary loss and weakened
velocity defect used by the projected charts. -/
theorem Prepared.eventually_good_original_lines (h : cfg.Prepared) {s M ε : ℝ}
    (hM : M ≤ cfg.e₀) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ a : cfg.NativeLevel k s,
      ∀ᵐ p ∂cfg.μ k, p.1 ∈ goodOriginalLines (cfg.b k) (cfg.N k ^ ε) (cfg.N k ^ (-M)) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hcoef := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    1 (show (0 : ℝ) < ε from hε) (show (0 : ℝ) ≤ 2 by norm_num)
  filter_upwards [hcoef] with k hk
  intro a
  have hc : 2 * cfg.K k ≤ cfg.N k ^ ε := by
    simpa only [pow_one, Real.rpow_zero, mul_one] using hk.le
  have hdef : cfg.N k ^ (-cfg.e₀) ≤ cfg.N k ^ (-M) :=
    Real.rpow_le_rpow_of_exponent_le (hN1 k) (neg_le_neg hM)
  filter_upwards [a.original_good_ae h] with p hp
  exact ⟨fun e => (hp.1 e).trans hc, hp.2.trans hdef⟩

end Data

/-- A static original-incidence-conull line cut preserves every original
residual chart floor, on its entire time domain. -/
theorem original_good_line_cut_mass {α : Type*} [MeasurableSpace α]
    (μ ρ : Measure (α × ℝ)) (hρ : ρ ≤ μ) (G A : Set α) (J : Set ℝ)
    (hG : ∀ᵐ p ∂μ, p.1 ∈ G) : ρ ((A ∩ G) ×ˢ J) = ρ (A ×ˢ J) := by
  apply measure_congr
  filter_upwards [ae_mono hρ hG] with p hp
  simp only [mem_prod, mem_inter_iff, hp, and_true]

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
