import Submission.Obl.k4_horizontal_supercritical_three_projections.Model
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Interface
import Submission.Lib.K4FullTimeLayers.Geometry

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory Filter
open scoped ENNReal BigOperators

noncomputable section

abbrev Model := Submission.Obl.k4_horizontal_supercritical_three_projections.HorizontalModel
abbrev Scalar := Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarMeshProjection
abbrev predictor := Submission.Lib.K4FullTimeLayers.parameterPredictor

def chartP (D : ℝ) (P : ℤ) (b : Fin 6 → ℝ) : ℝ := (b 0 - (P : ℝ) * D) / D

def chartQ (D : ℝ) (Q : ℤ) (b : Fin 6 → ℝ) : ℝ := (b 1 - (Q : ℝ) * D) / D

def chartR (D : ℝ) (P Q : ℤ) (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  chartQ D Q b - 2 * t * chartP D P b

def chartSignal (a : ℝ) (g b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  (b 2 + t * b 5 - predictor g t (b 0) (b 1)) / a

def chartCell (D σ : ℝ) (P Q : ℤ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 2 → ℤ :=
  ![⌊t / σ⌋, ⌊chartR D P Q b t / σ⌋]

/-- The corrected chart certificate, with all floors measured in the original law. -/
structure Charts {α : Type} [MeasurableSpace α]
    (b : α → Fin 6 → ℝ) (ρ : Measure (α × ℝ)) (π : Measure ℝ)
    (χ D a σ d H mass : ℝ) (w : Fin 3 → ℝ) where
  n : ℕ
  G : Fin n → Set α
  q : Fin n → Fin 3 → ℤ
  g : Fin n → Fin 6 → ℝ
  law : Measure (α × ℝ)
  le : law ≤ ρ
  mass_le : ENNReal.ofReal mass ≤ law univ
  cover : ∀ᵐ p ∂law, ∃ c, p.1 ∈ G c
  measurable : ∀ c, MeasurableSet (G c)
  disjoint : ∀ c c', c ≠ c' → Disjoint (G c) (G c')
  bins : ∀ c, ∀ l ∈ G c,
    ⌊b l 3 / χ⌋ = q c 0 ∧ ⌊b l 0 / D⌋ = q c 1 ∧ ⌊b l 1 / D⌋ = q c 2 ∧
      (∀ e, |b l e| ≤ H) ∧ |b l 4 + b l 0| ≤ χ
  norm : ∀ c, ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ p ∈ Icc ((q c 1 : ℝ) * D) (((q c 1 : ℝ) + 1) * D),
    ∀ q' ∈ Icc ((q c 2 : ℝ) * D) (((q c 2 : ℝ) + 1) * D),
      |predictor (g c) t p q'| ≤ H
  signal : ∀ c, ∀ l ∈ G c, ∀ t ∈ Icc (0 : ℝ) 1,
    |chartSignal a (g c) (b l) t| ≤ H
  floor : ∀ c, ENNReal.ofReal (D ^ 2 * a ^ d / H) *
    π (Ico ((q c 0 : ℝ) * χ) (((q c 0 : ℝ) + 1) * χ)) ≤ ρ (G c ×ˢ Icc (0 : ℝ) 1)
  support : ∀ c (h : Fin 3), ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
    (F.card : ℝ) * σ ^ 2 ≤ H * (w h) ^ (-d) ∧
    ∀ᵐ p ∂law, p.1 ∈ G c →
      (chartCell D σ (q c 1) (q c 2) (b p.1) p.2,
        ⌊chartSignal a (g c) (b p.1) p.2 / w h⌋) ∈ F

variable {α : Type} [MeasurableSpace α]

def ChartsAt (m : Model α) (k : ℕ) (M s₀ ξ : ℝ) (depth : Fin 3 → ℝ) : Prop :=
  Nonempty (Charts (m.b k) (m.ρ k) (m.π k)
    (m.N k ^ (-M)) (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-s₀))
    (m.N k ^ (-(20 * s₀))) m.d (m.N k ^ ξ) (m.N k ^ (-ξ))
    (fun h => m.N k ^ (-(depth h - s₀))))

def ChartsReady (m : Model α) (M s₀ : ℝ) (depth : Fin 3 → ℝ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, ChartsAt m k M s₀ ξ depth

def DepthMargins (κ s₀ : ℝ) (depth : Fin 3 → ℝ) : Prop :=
  ∀ h, s₀ < depth h ∧ depth h - s₀ ≤ s₀ * min κ (1 - 2 * κ) / 16

/-- The exact simultaneous physical output, at an arbitrary three depths. -/
def ProjectedAt (m : Model α) (k : ℕ) (M s₀ R ε : ℝ) (depth : Fin 3 → ℝ) : Prop :=
  let χ := m.N k ^ (-M)
  let D := m.N k ^ (-2 * m.κ * s₀)
  ∃ (ρstar : Measure (α × ℝ)) (np : Fin 3 → ℕ)
    (Cp : (h : Fin 3) → Fin (np h) → Set α)
    (qp : (h : Fin 3) → Fin (np h) → Fin 3 → ℤ)
    (Gp : (h : Fin 3) → Fin (np h) → MvPolynomial (Fin 2) ℝ),
    ρstar ≤ m.ρ k ∧ ENNReal.ofReal (m.N k ^ (-ε)) ≤ ρstar univ ∧
    (∀ᵐ p ∂ρstar, ∀ h : Fin 3, ∃ i, p.1 ∈ Cp h i) ∧
    (∀ h i, MeasurableSet (Cp h i)) ∧
    (∀ h i i', i ≠ i' → Disjoint (Cp h i) (Cp h i')) ∧
    (∀ h i,
      (∀ l ∈ Cp h i, ⌊m.b k l 3 / χ⌋ = qp h i 0 ∧
        ⌊m.b k l 0 / χ⌋ = qp h i 1 ∧ ⌊m.b k l 1 / D⌋ = qp h i 2 ∧
        (∀ e, |m.b k l e| ≤ m.N k ^ ε)) ∧
      |(qp h i 0 : ℝ) * χ| + |(qp h i 1 : ℝ) * χ| +
        |(qp h i 2 : ℝ) * D| ≤ m.N k ^ ε ∧
      (Gp h i).totalDegree ≤ 2 ∧ (∀ e, |(Gp h i).coeff e| ≤ m.N k ^ R) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
        |MvPolynomial.eval ![t, (qp h i 2 : ℝ) * D - t * ((qp h i 1 : ℝ) * χ) + D * w]
          (Gp h i)| ≤ m.N k ^ ε) ∧
      (∀ l ∈ Cp h i, ∀ t ∈ Icc (0 : ℝ) 1,
        |(m.x k l t) 2 - (qp h i 2 : ℝ) * D + t * ((qp h i 1 : ℝ) * χ)| ≤
          m.N k ^ ε * D ∧
        |(m.x k l t) 3 - MvPolynomial.eval ![t, (m.x k l t) 2] (Gp h i)| ≤
          m.N k ^ ε * m.N k ^ (-depth h)) ∧
      ENNReal.ofReal (χ * D * (m.N k ^ (-depth h)) ^ m.d / m.N k ^ ε) *
        m.π k (Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ)) ≤
        m.ρ k (Cp h i ×ˢ Icc (0 : ℝ) 1)) ∧
    (∀ h, (∑ i : Fin (np h),
      ENNReal.ofReal (χ * D * (m.N k ^ (-depth h)) ^ m.d) *
        m.π k (Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ))) ≤
          ENNReal.ofReal (m.N k ^ ε))

end
end Submission.Obl.k4_subcritical_chart_projection
