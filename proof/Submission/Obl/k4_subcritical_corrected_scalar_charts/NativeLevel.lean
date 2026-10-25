/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeLevel.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeTable

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- A genuine original native level, with its full witness floor and actual
bounded affine entries stored before any endpoint or scalar restriction. -/
structure NativeLevel (k : ℕ) (s : ℝ) where
  assignments : cfg.AssignmentLevel k s
  fitted_measurable : ∀ i, MeasurableSet (cfg.B k s i)
  witness_floor : ∀ i,
    ENNReal.ofReal (cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 3) ≤
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))
  L : Fin (cfg.n k s) → Fin 4 → ℝ
  slope : ∀ i, ∀ e : Fin 3, |L i e.succ| ≤ 36 * cfg.K k ^ 4
  defining_polynomial : ∀ i, cfg.F k s i = X (3 : Fin 4) -
    (C (L i 0) + C (L i 1) * X (0 : Fin 4) + C (L i 2) * X (1 : Fin 4) +
      C (L i 3) * X (2 : Fin 4))
  fit : ∀ i, ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
    |cfg.b k l 2 + t * cfg.b k l 5 - (L i 0 + L i 1 * t +
      L i 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
      L i 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * cfg.N k ^ (-s)

variable {cfg}

theorem Prepared.eventually_native_level (h : cfg.Prepared) {s : ℝ}
    (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, Nonempty (cfg.NativeLevel k s) := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by
    have hh : 0 < s⁻¹ := inv_pos.mpr hs
    dsimp [R]
    linarith
  have hRs : R⁻¹ ≤ s := by
    have hRpos : 0 < R := by linarith
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    exact (inv_le_comm₀ hRpos hs).mpr hle
  filter_upwards [h.eventually_assignment_level hs hsU,
    h.eventually_native_mass hs hsU, h.atlas R hR] with k ha hμ hatlas
  have hB : ∀ i, MeasurableSet (cfg.B k s i) := fun i =>
    ((hatlas s hRs hsU).2.2.1 i).2.1
  obtain ⟨L, hL, hfit⟩ := h.native_affine_table ha hs.le hμ
  exact ⟨{
    assignments := ha
    fitted_measurable := hB
    witness_floor := h.native_witness_lower ha hμ
    L := L
    slope := hL
    defining_polynomial := fun i => (hfit i).1
    fit := fun i => (hfit i).2
  }⟩

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
