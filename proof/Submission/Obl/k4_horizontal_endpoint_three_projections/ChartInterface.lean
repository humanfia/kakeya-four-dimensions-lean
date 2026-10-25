/- Adapted from o249 session x0878, branch x0878, commit 6a2b032b,
   ChartInterface.lean. The chart structure has been expanded into existentials
   and conjunctions so the split interfaces freeze over Mathlib only. -/
import Submission.Obl.k4_horizontal_endpoint_three_projections.Defect

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

namespace Submission.Obl.k4_horizontal_endpoint_three_projections

open MeasureTheory Set Filter

abbrev parameterPredictor := Data.predictor

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

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- An explicit chart family and common incidence law. The floors are in the
original residual, and terminal support is only required on the retained law. -/
def ChartsAt (k : ℕ) (M s₀ ξ : ℝ) (depth : Fin 3 → ℝ) : Prop :=
  let χ := cfg.N k ^ (-M)
  let D := cfg.N k ^ (-(2 * cfg.κ * s₀))
  let A₀ := cfg.N k ^ (-s₀)
  let σ := cfg.N k ^ (-(20 * s₀))
  let w : Fin 3 → ℝ := fun h => cfg.N k ^ (-(depth h - s₀))
  ∃ (nC : ℕ) (G : Fin nC → Set α) (qC : Fin nC → Fin 3 → ℤ)
    (g : Fin nC → Fin 6 → ℝ) (ρ' : Measure (α × ℝ)),
    ρ' ≤ cfg.ρ k ∧ ENNReal.ofReal (cfg.N k ^ (-ξ)) ≤ ρ' univ ∧
    (∀ᵐ p ∂ρ', ∃ c, p.1 ∈ G c) ∧
    (∀ c, MeasurableSet (G c)) ∧
    (∀ c c', c ≠ c' → Disjoint (G c) (G c')) ∧
    (∀ c, ∀ l ∈ G c,
      ⌊cfg.b k l 3 / χ⌋ = qC c 0 ∧ ⌊cfg.b k l 0 / D⌋ = qC c 1 ∧
      ⌊cfg.b k l 1 / D⌋ = qC c 2 ∧ (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ξ) ∧
      |cfg.b k l 4 + cfg.b k l 0| ≤ χ) ∧
    (∀ c, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ p ∈ Icc ((qC c 1 : ℝ) * D) (((qC c 1 : ℝ) + 1) * D),
      ∀ q ∈ Icc ((qC c 2 : ℝ) * D) (((qC c 2 : ℝ) + 1) * D),
        |parameterPredictor (g c) t p q| ≤ cfg.N k ^ ξ) ∧
    (∀ c, ∀ l ∈ G c, ∀ t ∈ Icc (0 : ℝ) 1,
      |chartSignal A₀ (g c) (cfg.b k l) t| ≤ cfg.N k ^ ξ) ∧
    (∀ c,
      ENNReal.ofReal (D ^ 2 * A₀ ^ cfg.d / cfg.N k ^ ξ) *
        cfg.π k (Ico ((qC c 0 : ℝ) * χ) (((qC c 0 : ℝ) + 1) * χ)) ≤
        cfg.ρ k (G c ×ˢ Icc (0 : ℝ) 1)) ∧
    (∀ c (h : Fin 3), ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) * σ ^ 2 ≤ cfg.N k ^ ξ * (w h) ^ (-cfg.d) ∧
      ∀ᵐ p ∂ρ', p.1 ∈ G c →
        (chartCell D σ (qC c 1) (qC c 2) (cfg.b k p.1) p.2,
          ⌊chartSignal A₀ (g c) (cfg.b k p.1) p.2 / w h⌋) ∈ F)

/-- Corrected scalar charts at every positive loss. -/
def ChartsReady (M s₀ : ℝ) (depth : Fin 3 → ℝ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, cfg.ChartsAt k M s₀ ξ depth

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

end Submission.Obl.k4_horizontal_endpoint_three_projections

end
