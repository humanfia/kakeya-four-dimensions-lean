/- Adapted from this LOT tree, obligation o249, session x0876, commit b00105b82d24db6d8501c6401ba2acd5156b7922,
   Submission/Obl/k4_horizontal_endpoint_three_projections/Model.lean;
   its accepted o212 data type and original source attributions are retained. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.Model

/-! Named interfaces for the subcritical endpoint-to-projection step. The underlying
prepared data and its basic, cap, atlas and nesting predicates are imported from
the accepted o212 model; only the rate assumption and output are different. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open MeasureTheory Set Filter

abbrev Data (α : Type) [MeasurableSpace α] :=
  Submission.Obl.k4_critical_intercept_concentration.Data α

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- The common subcritical prepared model, imported from accepted o263. -/
abbrev Prepared : Prop :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared cfg

/-- Affine dependence on the two static parameters, with affine time coefficients. -/
def predictor (h : Fin 6 → ℝ) (t p q : ℝ) : ℝ :=
  h 0 + h 1 * t + (h 2 + h 3 * t) * p + (h 4 + h 5 * t) * q

/-- The exact full-time endpoint output supplied by the engine. -/
def EndpointWith (E sMax R : ℝ) : Prop :=
  0 < sMax ∧ 2 * sMax < cfg.U ∧ 100 * sMax < E ∧ 1 < R ∧
    ∀ (m : ℕ) (sH : Fin m → ℝ), (∀ r, 0 < sH r ∧ sH r < sMax) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
    ∃ ρH : Measure (α × ℝ), ρH ≤ cfg.ρ k ∧
      ENNReal.ofReal (cfg.N k ^ (-ε)) ≤ ρH univ ∧
      ∃ (nH : Fin m → ℕ) (AH : (r : Fin m) → Fin (nH r) → Set α)
        (qH : (r : Fin m) → Fin (nH r) → Fin 3 → ℤ)
        (hH : (r : Fin m) → Fin (nH r) → Fin 6 → ℝ),
      ∀ r, (fun (χ D a : ℝ) =>
        (∀ i, MeasurableSet (AH r i)) ∧
        (∀ i i', i ≠ i' → Disjoint (AH r i) (AH r i')) ∧
        (∀ i, (∀ l ∈ AH r i, ⌊cfg.b k l 3 / χ⌋ = qH r i 0 ∧
            ⌊cfg.b k l 0 / D⌋ = qH r i 1 ∧ ⌊cfg.b k l 1 / D⌋ = qH r i 2) ∧
          (∀ e, |hH r i e| ≤ cfg.N k ^ R) ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            ∀ p ∈ Icc ((qH r i 1 : ℝ) * D) (((qH r i 1 : ℝ) + 1) * D),
            ∀ q ∈ Icc ((qH r i 2 : ℝ) * D) (((qH r i 2 : ℝ) + 1) * D),
            |predictor (hH r i) t p q| ≤ cfg.N k ^ ε) ∧
          (∀ l ∈ AH r i, ∀ t ∈ Icc (0 : ℝ) 1,
            |(cfg.x k l t) 3 - predictor (hH r i) t (cfg.b k l 0) (cfg.b k l 1)| ≤
              cfg.N k ^ ε * a) ∧
          ENNReal.ofReal (D ^ 2 * a ^ cfg.d / cfg.N k ^ ε) *
            cfg.π k (Ico ((qH r i 0 : ℝ) * χ) (((qH r i 0 : ℝ) + 1) * χ)) ≤
            ρH (AH r i ×ˢ Icc (0 : ℝ) 1)) ∧
        ρH {p | ∃ i, p.1 ∈ AH r i}ᶜ = 0)
        (cfg.N k ^ (-E)) (cfg.N k ^ (-2 * cfg.κ * sH r))
        (cfg.N k ^ (-sH r))

end Data

end Submission.Obl.k4_subcritical_endpoint_native_pairing
