/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/Model.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_critical_intercept_concentration.PreparedModel

/-! Named interfaces for the subcritical endpoint-to-projection step. The underlying
prepared data and its basic, cap, atlas and nesting predicates are imported from
the accepted o212 model; only the rate assumption and output are different. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set Filter

abbrev Data (α : Type) [MeasurableSpace α] :=
  Submission.Obl.k4_critical_intercept_concentration.Data α

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

structure Prepared : Prop where
  scale : ∀ k, 2 ≤ cfg.N k
  scale_limit : Tendsto cfg.N atTop atTop
  subpower : (∀ k, 1 ≤ cfg.K k) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ ε
  dimension_nonneg : 0 ≤ cfg.d
  dimension_lt_one : cfg.d < 1
  rate_pos : 0 < cfg.κ
  rate_le_one : cfg.κ ≤ 1
  transverse_pos : 0 < cfg.ℓ
  palette_pos : 0 < cfg.S
  palette_le_one : cfg.S ≤ 1
  depth_pos : 0 < cfg.U
  defect_pos : 0 < cfg.e₀
  subcritical_rate : 2 * cfg.κ < 1
  horizontal_rate : cfg.ℓ = cfg.κ
  basic : cfg.Basic
  caps : cfg.Caps
  atlas : cfg.Atlas
  nested : cfg.Nested

/-- Affine dependence on the two static parameters, with affine time coefficients. -/
def predictor (h : Fin 6 → ℝ) (t p q : ℝ) : ℝ :=
  h 0 + h 1 * t + (h 2 + h 3 * t) * p + (h 4 + h 5 * t) * q

/-- The exact full-time endpoint output supplied by the engine. -/
def Endpoint : Prop :=
  ∃ sMax R : ℝ, 0 < sMax ∧ 2 * sMax < cfg.U ∧ 100 * sMax < cfg.e₀ ∧ 1 < R ∧
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

/-- One output sample, with the original residual floors and common physical width. -/
def ProjectedAt (k : ℕ) (s₀ s u v M R ε : ℝ) : Prop :=
  (fun (χ D : ℝ) (depth : Fin 3 → ℝ) =>
    ∃ (ρstar : Measure (α × ℝ)) (np : Fin 3 → ℕ)
      (Cp : (h : Fin 3) → Fin (np h) → Set α)
      (qp : (h : Fin 3) → Fin (np h) → Fin 3 → ℤ)
      (Gp : (h : Fin 3) → Fin (np h) → MvPolynomial (Fin 2) ℝ),
      ρstar ≤ cfg.ρ k ∧ ENNReal.ofReal (cfg.N k ^ (-ε)) ≤ ρstar univ ∧
      (∀ᵐ p ∂ρstar, ∀ h : Fin 3, ∃ i, p.1 ∈ Cp h i) ∧
      (∀ h i, MeasurableSet (Cp h i)) ∧
      (∀ h i i', i ≠ i' → Disjoint (Cp h i) (Cp h i')) ∧
      (∀ h i, (∀ l ∈ Cp h i, ⌊cfg.b k l 3 / χ⌋ = qp h i 0 ∧
          ⌊cfg.b k l 0 / χ⌋ = qp h i 1 ∧ ⌊cfg.b k l 1 / D⌋ = qp h i 2 ∧
          (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε)) ∧
        |(qp h i 0 : ℝ) * χ| + |(qp h i 1 : ℝ) * χ| + |(qp h i 2 : ℝ) * D| ≤ cfg.N k ^ ε ∧
        (Gp h i).totalDegree ≤ 2 ∧ (∀ e, |(Gp h i).coeff e| ≤ cfg.N k ^ R) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
          |MvPolynomial.eval ![t, (qp h i 2 : ℝ) * D - t * ((qp h i 1 : ℝ) * χ) + D * w]
            (Gp h i)| ≤ cfg.N k ^ ε) ∧
        (∀ l ∈ Cp h i, ∀ t ∈ Icc (0 : ℝ) 1,
          |(cfg.x k l t) 2 - (qp h i 2 : ℝ) * D + t * ((qp h i 1 : ℝ) * χ)| ≤ cfg.N k ^ ε * D ∧
          |(cfg.x k l t) 3 - MvPolynomial.eval ![t, (cfg.x k l t) 2] (Gp h i)| ≤
            cfg.N k ^ ε * cfg.N k ^ (-depth h)) ∧
        ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) *
          cfg.π k (Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ)) ≤
          cfg.ρ k (Cp h i ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ h, (∑ i : Fin (np h), ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) *
        cfg.π k (Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ))) ≤
        ENNReal.ofReal (cfg.N k ^ ε)))
    (cfg.N k ^ (-M)) (cfg.N k ^ (-2 * cfg.κ * s₀)) ![s, s + u, s + v]

/-- The depth and grid choices, made before the arbitrary output loss. -/
def Projected : Prop :=
  ∀ buffer : ℝ, 100 < buffer → ∃ s₀ s u v R : ℝ,
    0 < s₀ ∧ buffer * s₀ < cfg.U ∧ buffer * s₀ < cfg.e₀ ∧ s₀ < s ∧
    0 < u ∧ 0 < v ∧ v < u ∧ v < (1 - cfg.d) * u / 4 ∧
    s + u < cfg.U ∧ s + u < 3 * s₀ / 2 ∧
    (10 / (1 - cfg.d) + 3) * u < 2 * cfg.κ * (s - s₀) ∧
    (10 / (1 - cfg.d) + 3) * u < cfg.κ * s ∧ 1 < R ∧
    ∃ M : ℝ, buffer * s₀ < M ∧ buffer * M < cfg.U ∧ buffer * M < cfg.e₀ ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.ProjectedAt k s₀ s u v M R ε

end Data

/-- The hypothesis is universal over prepared parents, as in the frozen engine. -/
def EndpointEngine : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Prepared → cfg.Endpoint

def ProjectionEngine : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Prepared → cfg.Projected

end Submission.Obl.k4_subcritical_corrected_scalar_charts
