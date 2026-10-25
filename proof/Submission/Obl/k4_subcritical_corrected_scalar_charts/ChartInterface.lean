/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/ChartInterface.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.Defect
import Submission.Obl.k4_subcritical_corrected_scalar_charts.FiberGeometry

/-! The interface between the subcritical chart preparation (coarse endpoint
charts, their baseline and time correction, and the terminal support counts of
the corrected scalar signal; paper Proposition 9.6, first part) and the scalar
projection with its return to physical coordinates (the rest of the proof).

A chart carries one combined baseline `g`, an endpoint predictor in the original
static parameters `(p,q) = (b 0, b 1)`; it is the coarse endpoint predictor plus
`A0` times the time correction, rewritten in unscaled parameters. The scalar
coordinate is `R(t) = q̃ - 2 t p̃` in chart-scaled parameters and the signal is
`(x3 - g(t,p,q)) / A0`. -/

noncomputable section

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set Filter

/-- Chart-scaled first static parameter `p̃ = (b0 - P D) / D`. -/
def chartP (D : ℝ) (P : ℤ) (b : Fin 6 → ℝ) : ℝ := (b 0 - (P : ℝ) * D) / D

/-- Chart-scaled second static parameter `q̃ = (b1 - Q D) / D`. -/
def chartQ (D : ℝ) (Q : ℤ) (b : Fin 6 → ℝ) : ℝ := (b 1 - (Q : ℝ) * D) / D

/-- The scalar chart coordinate `R(t) = q̃ - 2 t p̃`. -/
def chartR (D : ℝ) (P Q : ℤ) (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  chartQ D Q b - 2 * t * chartP D P b

/-- The corrected scalar signal `(x3 - g(t, b0, b1)) / A`. -/
def chartSignal (A : ℝ) (g : Fin 6 → ℝ) (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  (b 2 + t * b 5 - parameterPredictor g t (b 0) (b 1)) / A

/-- The scalar cell of a trajectory at time `t`. -/
def chartCell (D σ : ℝ) (P Q : ℤ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 2 → ℤ :=
  ![⌊t / σ⌋, ⌊chartR D P Q b t / σ⌋]

/-- A finite family of coarse charts at one index: chart sets, their labels
`(velocity bin at χ, first parameter bin at D, second parameter bin at D)` and
their combined baselines. -/
structure ChartFamily (α : Type) where
  n : ℕ
  G : Fin n → Set α
  q : Fin n → Fin 3 → ℤ
  g : Fin n → Fin 6 → ℝ

namespace ChartFamily

variable {α : Type} [MeasurableSpace α]

/-- The prepared chart family at index `k`, with every loss bounded by `N^ξ`.
The parameters are `χ = N^(-M)`, `D = N^(-2κ s₀)`, `A = N^(-s₀)`,
`σ = N^(-20 s₀)` and the three terminal widths `w h = N^(-(depth h - s₀))`.
`ρ'` is the dense residual on which the terminal support counts hold. -/
structure Prepared (C : ChartFamily α) (cfg : Data α) (k : ℕ)
    (χ D A σ ξ : ℝ) (w : Fin 3 → ℝ) (ρ' : Measure (α × ℝ)) : Prop where
  le_rho : ρ' ≤ cfg.ρ k
  mass : ENNReal.ofReal (cfg.N k ^ (-ξ)) ≤ ρ' univ
  cover : ∀ᵐ p ∂ρ', ∃ c, p.1 ∈ C.G c
  measurable : ∀ c, MeasurableSet (C.G c)
  disjoint : ∀ c c', c ≠ c' → Disjoint (C.G c) (C.G c')
  labels : ∀ c, ∀ l ∈ C.G c,
    ⌊cfg.b k l 3 / χ⌋ = C.q c 0 ∧ ⌊cfg.b k l 0 / D⌋ = C.q c 1 ∧
      ⌊cfg.b k l 1 / D⌋ = C.q c 2 ∧ (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ξ) ∧
      |cfg.b k l 4 + cfg.b k l 0| ≤ χ
  box : ∀ c, ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ p ∈ Icc ((C.q c 1 : ℝ) * D) (((C.q c 1 : ℝ) + 1) * D),
    ∀ q ∈ Icc ((C.q c 2 : ℝ) * D) (((C.q c 2 : ℝ) + 1) * D),
      |parameterPredictor (C.g c) t p q| ≤ cfg.N k ^ ξ
  fit : ∀ c, ∀ l ∈ C.G c, ∀ t ∈ Icc (0 : ℝ) 1,
    |chartSignal A (C.g c) (cfg.b k l) t| ≤ cfg.N k ^ ξ
  floor : ∀ c,
    ENNReal.ofReal (D ^ 2 * A ^ cfg.d / cfg.N k ^ ξ) *
      cfg.π k (Ico ((C.q c 0 : ℝ) * χ) (((C.q c 0 : ℝ) + 1) * χ)) ≤
      cfg.ρ k (C.G c ×ˢ Icc (0 : ℝ) 1)
  support : ∀ c (h : Fin 3), ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
    (F.card : ℝ) * σ ^ 2 ≤ cfg.N k ^ ξ * (w h) ^ (-cfg.d) ∧
    ∀ᵐ p ∂ρ', p.1 ∈ C.G c →
      (chartCell D σ (C.q c 1) (C.q c 2) (cfg.b k p.1) p.2,
        ⌊chartSignal A (C.g c) (cfg.b k p.1) p.2 / w h⌋) ∈ F

end ChartFamily

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- Prepared charts at every loss, for the grid exponent `M`, the coarse depth
`s₀` and the three terminal depths. -/
def ChartsReady (M s₀ : ℝ) (depth : Fin 3 → ℝ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, ∃ (C : ChartFamily α) (ρ' : Measure (α × ℝ)),
    C.Prepared cfg k (cfg.N k ^ (-M)) (cfg.N k ^ (-(2 * cfg.κ * s₀)))
      (cfg.N k ^ (-s₀)) (cfg.N k ^ (-(20 * s₀))) ξ
      (fun h => cfg.N k ^ (-(depth h - s₀))) ρ'

/-- The endpoint output with its returned `sMax` and coefficient exponent made
explicit, so that later choices may depend on them. -/
def EndpointWith (sMax R : ℝ) : Prop :=
  0 < sMax ∧ 2 * sMax < cfg.U ∧ 100 * sMax < cfg.e₀ ∧ 1 < R ∧
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
        (cfg.N k ^ (-cfg.e₀)) (cfg.N k ^ (-2 * cfg.κ * sH r))
        (cfg.N k ^ (-sH r))

theorem endpoint_iff_exists_with : cfg.Endpoint ↔ ∃ sMax R : ℝ, cfg.EndpointWith sMax R :=
  Iff.rfl

/-- The depth margins used by the directional collapse: every terminal depth lies
strictly above `s₀` and below `s₀ (1 + min κ (1 - 2κ) / 16)`. -/
def DepthMargins (s₀ : ℝ) (depth : Fin 3 → ℝ) : Prop :=
  ∀ h, s₀ < depth h ∧ depth h - s₀ ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16

end Data

/-- What the chart preparation must supply: for the endpoint output at the
weakened defect exponent `M`, every admissible coarse depth and terminal depths
with the directional margins give prepared charts. -/
def ChartPreparation : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Prepared →
    ∀ M sMax RE s₀ : ℝ, 0 < M → M < cfg.e₀ →
    (Data.withDefect cfg M).EndpointWith sMax RE →
    0 < s₀ → 3 * s₀ / 2 < sMax → 100 * s₀ < M →
    ∀ depth : Fin 3 → ℝ, cfg.DepthMargins s₀ depth →
    cfg.ChartsReady M s₀ depth

end Submission.Obl.k4_subcritical_corrected_scalar_charts

end
