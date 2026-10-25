/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/PairedInterface.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ChartInterface

/-! The comparison cut retains the original endpoint families and their full
domains. Only incidence coverage is restricted. In particular, no sliced native
or endpoint mass is used as a reference weight. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set Filter

noncomputable section

namespace Data

open Submission.Obl.k4_critical_intercept_concentration.Data (I)

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- The native affine graph written in static horizontal parameters at the
original velocity-bin representative. The horizontal atlas makes `F` affine
with hidden coefficient one. -/
def nativeParameter (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (v t p q : ℝ) : ℝ :=
  -MvPolynomial.eval ![t, p + t * v, q - t * p, 0] (cfg.F k s i)

/-- Simultaneous comparison at the coarse and auxiliary endpoint depths. The
full-time floors refer to `cfg.ρ`, before the comparison law is restricted. -/
def PairedAt (k : ℕ) (M RE s₀ ε : ℝ) : Prop :=
  let depth : Fin 2 → ℝ := ![s₀, 3 * s₀ / 2]
  let χ := cfg.N k ^ (-M)
  ∃ (σ : Measure (α × ℝ)) (nH : Fin 2 → ℕ)
    (AH : (r : Fin 2) → Fin (nH r) → Set α)
    (qH : (r : Fin 2) → Fin (nH r) → Fin 3 → ℤ)
    (hH : (r : Fin 2) → Fin (nH r) → Fin 6 → ℝ)
    (paired : (r : Fin 2) → Fin (nH r) → Fin (cfg.n k (depth r)) → Prop),
    σ ≤ cfg.ρ k ∧ ENNReal.ofReal (cfg.N k ^ (-ε)) ≤ σ univ ∧
    (∀ r, (fun D a : ℝ =>
      (∀ h, MeasurableSet (AH r h)) ∧
      (∀ h h', h ≠ h' → Disjoint (AH r h) (AH r h')) ∧
      (∀ h,
        (∀ l ∈ AH r h, ⌊cfg.b k l 3 / χ⌋ = qH r h 0 ∧
          ⌊cfg.b k l 0 / D⌋ = qH r h 1 ∧ ⌊cfg.b k l 1 / D⌋ = qH r h 2) ∧
        (∀ e, |hH r h e| ≤ cfg.N k ^ RE) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          ∀ p ∈ Icc ((qH r h 1 : ℝ) * D) (((qH r h 1 : ℝ) + 1) * D),
          ∀ q ∈ Icc ((qH r h 2 : ℝ) * D) (((qH r h 2 : ℝ) + 1) * D),
          |predictor (hH r h) t p q| ≤ cfg.N k ^ ε) ∧
        (∀ l ∈ AH r h, ∀ t ∈ Icc (0 : ℝ) 1,
          |(cfg.x k l t) 3 - predictor (hH r h) t (cfg.b k l 0) (cfg.b k l 1)| ≤
            cfg.N k ^ ε * a) ∧
        ENNReal.ofReal (D ^ 2 * a ^ cfg.d / cfg.N k ^ ε) *
          cfg.π k (Ico ((qH r h 0 : ℝ) * χ) (((qH r h 0 : ℝ) + 1) * χ)) ≤
          cfg.ρ k (AH r h ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ h i, paired r h i →
        ∀ t ∈ I (cfg.T k (depth r)) (cfg.j k (depth r) i),
        ∀ p ∈ Icc ((qH r h 1 : ℝ) * D) (((qH r h 1 : ℝ) + 1) * D),
        ∀ q ∈ Icc ((qH r h 2 : ℝ) * D) (((qH r h 2 : ℝ) + 1) * D),
          |cfg.nativeParameter k (depth r) i ((qH r h 0 : ℝ) * χ) t p q -
            predictor (hH r h) t p q| ≤ cfg.N k ^ ε * a) ∧
      (∀ h (j₀ : Fin (2 ^ cfg.T k (depth r))),
        (Set.ncard {i : Fin (cfg.n k (depth r)) |
          paired r h i ∧ cfg.j k (depth r) i = j₀} : ℝ) ≤ cfg.N k ^ ε))
      (cfg.N k ^ (-2 * cfg.κ * depth r)) (cfg.N k ^ (-depth r))) ∧
    (∀ᵐ p ∂σ, ∀ r : Fin 2, ∃ h i,
      p.1 ∈ AH r h ∧ p.1 ∈ cfg.B k (depth r) i ∧
      p.2 ∈ I (cfg.T k (depth r)) (cfg.j k (depth r) i) ∧ paired r h i)

/-- The comparison conclusion at every positive loss. -/
def PairedReady (M RE s₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.PairedAt k M RE s₀ ε

end Data

/-- The original prepared atlas instantiates full-time paired matching. -/
def PairedComparison : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Prepared →
    ∀ M sMax RE s₀ : ℝ, 0 < M → M < cfg.e₀ →
    (Data.withDefect cfg M).EndpointWith sMax RE →
    0 < s₀ → 3 * s₀ / 2 < sMax → 100 * s₀ < M →
    cfg.PairedReady M RE s₀

/-- The second cut: directional correction and original-witness scalar support. -/
def CorrectedCharts : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Prepared →
    ∀ M RE s₀ : ℝ, 0 < M → M < cfg.e₀ →
    0 < s₀ → 3 * s₀ / 2 < cfg.U → 100 * s₀ < M →
    cfg.PairedReady M RE s₀ →
    ∀ depth : Fin 3 → ℝ, cfg.DepthMargins s₀ depth →
    cfg.ChartsReady M s₀ depth

/-- The third cut: conditional Scalar, reconstruction, slicing and common floors.
The one coefficient exponent is chosen before all final losses. -/
def ScalarReturn : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Prepared →
    ∀ M s₀ s u v : ℝ, 0 < M → M < cfg.e₀ → 0 < s₀ → 100 * s₀ < M →
    s₀ < s → 0 < u → 0 < v → v < u → s + u < 3 * s₀ / 2 →
    s + u < cfg.U → cfg.DepthMargins s₀ ![s, s + u, s + v] →
    cfg.ChartsReady M s₀ ![s, s + u, s + v] →
    ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, cfg.ProjectedAt k s₀ s u v M R ε

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
