import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inputs

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Filter

noncomputable section

abbrev Data := Submission.Obl.k4_critical_conditional_row_preparation.Data

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

structure Valid : Prop where
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
  horizontal_rate : cfg.ℓ = cfg.κ
  basic : cfg.Basic
  caps : cfg.Caps
  atlas : cfg.Atlas
  nested : cfg.Nested

/-- One compared three-layer datum at its original physical scales. -/
def ProjectedAt (k : ℕ) (s₀ s u v R M ε : ℝ) : Prop :=
  (fun (χ D : ℝ) (depth : Fin 3 → ℝ) => ∃ (ρstar : MeasureTheory.Measure (α × ℝ)) (np : Fin 3 → ℕ) (Cp : (h : Fin 3) → Fin (np h) → Set α) (qp : (h : Fin 3) → Fin (np h) → Fin 3 → ℤ) (Gp : (h : Fin 3) → Fin (np h) → MvPolynomial (Fin 2) ℝ), ρstar ≤ cfg.ρ k ∧ ENNReal.ofReal (cfg.N k ^ (-ε)) ≤ ρstar Set.univ ∧ (∀ᵐ p ∂ρstar, ∀ h : Fin 3, ∃ i, p.1 ∈ Cp h i) ∧ (∀ h i, MeasurableSet (Cp h i)) ∧ (∀ h i i', i ≠ i' → Disjoint (Cp h i) (Cp h i')) ∧ (∀ h i, (∀ l ∈ Cp h i, ⌊cfg.b k l 3 / χ⌋ = qp h i 0 ∧ ⌊cfg.b k l 0 / χ⌋ = qp h i 1 ∧ ⌊cfg.b k l 1 / D⌋ = qp h i 2 ∧ (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε)) ∧ |(qp h i 0 : ℝ) * χ| + |(qp h i 1 : ℝ) * χ| + |(qp h i 2 : ℝ) * D| ≤ cfg.N k ^ ε ∧ (Gp h i).totalDegree ≤ 2 ∧ (∀ e, |(Gp h i).coeff e| ≤ cfg.N k ^ R) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, (qp h i 2 : ℝ) * D - t * ((qp h i 1 : ℝ) * χ) + D * w] (Gp h i)| ≤ cfg.N k ^ ε) ∧ (∀ l ∈ Cp h i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(cfg.x k l t) 2 - (qp h i 2 : ℝ) * D + t * ((qp h i 1 : ℝ) * χ)| ≤ cfg.N k ^ ε * D ∧ |(cfg.x k l t) 3 - MvPolynomial.eval ![t, (cfg.x k l t) 2] (Gp h i)| ≤ cfg.N k ^ ε * cfg.N k ^ (-depth h)) ∧ ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) * cfg.π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ)) ≤ cfg.ρ k (Cp h i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ (∀ h, (∑ i : Fin (np h), ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) * cfg.π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (cfg.N k ^ ε)) ∧ (∀ᵐ p ∂ρstar, ∀ h : Fin 3, h ≠ 0 → ∀ (i₀ : Fin (np 0)) (ih : Fin (np h)), p.1 ∈ Cp 0 i₀ → p.1 ∈ Cp h ih → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval (![t, (qp 0 i₀ 2 : ℝ) * D - t * ((qp 0 i₀ 1 : ℝ) * χ) + D * w] : Fin 2 → ℝ) (Gp h ih - Gp 0 i₀)| ≤ cfg.N k ^ (ε + (10 / (1 - cfg.d)) * u) * cfg.N k ^ (-s))) (cfg.N k ^ (-M)) (cfg.N k ^ (-2 * cfg.κ * s₀)) ![s, s + u, s + v]

/-- The buffered compared layers, retaining every original reference weight. -/
def Projected : Prop :=
  ∀ buffer : ℝ, 100 < buffer → ∃ s₀ s u v R : ℝ, 0 < s₀ ∧ buffer * s₀ < cfg.U ∧ buffer * s₀ < cfg.e₀ ∧ s₀ < s ∧ 0 < u ∧ 0 < v ∧ v < u ∧ v < (1 - cfg.d) * u / 4 ∧ s + u < cfg.U ∧ s + u < 3 * s₀ / 2 ∧ (10 / (1 - cfg.d) + 3) * u < 2 * cfg.κ * (s - s₀) ∧ (10 / (1 - cfg.d) + 3) * u < cfg.κ * s ∧ 1 < R ∧ ∃ M : ℝ, buffer * s₀ < M ∧ buffer * M < cfg.U ∧ buffer * M < cfg.e₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, cfg.ProjectedAt k s₀ s u v R M ε

/-- The exact normalized geometric and finite-support conclusion at one resolution. -/
def ExtractionAt (k : ℕ) (θ s v m J : ℝ) : Prop :=
  ∃ (i : Fin (cfg.n k s)) (lam : Measure (α × ℝ)) (Bs : Set α)
    (L C : Fin 4 → ℝ),
  let t₀ := (cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s
  let q := ((2 : ℝ) ^ cfg.T k s)⁻¹
  let g := cfg.N k ^ (-cfg.κ * s)
  let a := cfg.N k ^ (-s)
  let zt := fun t : ℝ => (t - t₀) / q
  let zZ := fun l t => (cfg.b k l 0 + t * cfg.b k l 3 - cfg.c k s i 0 - t * cfg.c k s i 1) / q
  let tr := fun l t => (cfg.b k l 1 + t * cfg.b k l 4 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.b k l 0 + t * cfg.b k l 3)) / (q * g)
  let resid := fun l t => (cfg.b k l 2 + t * cfg.b k l 5 - (L 0 + L 1 * t + L 2 * (cfg.b k l 0 + t * cfg.b k l 3) + L 3 * (cfg.b k l 1 + t * cfg.b k l 4))) / a
  MeasurableSet Bs ∧ Bs ⊆ cfg.B k s i ∧ lam ≤ cfg.ρ k ∧
  (∀ᵐ p ∂lam, p.1 ∈ Bs ∧ p.2 ∈ Icc t₀ (t₀ + q)) ∧
  ENNReal.ofReal (cfg.N k ^ (-θ)) * (ENNReal.ofReal q * cfg.ν k (cfg.A k s i)) ≤ lam univ ∧
  (∀ e, |L e| ≤ cfg.N k ^ J) ∧ (∀ e, |C e| ≤ cfg.N k ^ θ) ∧
  (∀ l ∈ Bs, ∀ t ∈ Icc t₀ (t₀ + q), |zZ l t| ≤ cfg.N k ^ θ ∧ |tr l t| ≤ cfg.N k ^ θ ∧ |resid l t| ≤ cfg.N k ^ θ) ∧
  ∃ Fs : Finset ((Fin 2 → ℤ) × ℤ),
    (Fs.card : ℝ) * (cfg.N k ^ (-m)) ^ 2 ≤ cfg.N k ^ θ * (cfg.N k ^ (-v)) ^ (-cfg.d) ∧
    ∀ᵐ p ∂lam,
      ((![⌊zt p.2 / (cfg.N k ^ (-m))⌋, ⌊zZ p.1 p.2 / (cfg.N k ^ (-m))⌋] : Fin 2 → ℤ),
        ⌊(resid p.1 p.2 - ((C 0 + C 1 * zt p.2 + C 2 * zZ p.1 p.2) * tr p.1 p.2 + C 3 * (tr p.1 p.2) ^ 2)) / (cfg.N k ^ (-v))⌋) ∈ Fs

def Extraction : Prop :=
  ∃ s v m U' J : ℝ, 0 < s ∧ 0 < v ∧ v < m ∧ cfg.κ * s ≤ m ∧
    0 < U' ∧ U' < m ∧ s + v ≤ cfg.U ∧ 17 ≤ J ∧
    ∀ θ : ℝ, 0 < θ → ∀ᶠ k in atTop, cfg.ExtractionAt k θ s v m J

end Data

/-- Native preparation uses the local field only after the compared-layer datum. -/
def NativePreparation : Prop :=
  CommonField → Row → Match → ∀ (α : Type) [MeasurableSpace α] (cfg : Data α),
    cfg.Valid → cfg.Projected → cfg.Extraction

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
