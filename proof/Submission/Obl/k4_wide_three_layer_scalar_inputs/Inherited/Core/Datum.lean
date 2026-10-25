/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit ecf664378ad8398f225a4f7cddbe679a98231d2a, file Submission/Obl/k4_horizontal_wide_interval_return/Core/Datum.lean.
Namespace/imports renamed; only the datum record retained. Earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.Basics

/-!
# The three-layer datum of o250, unpacked

`LayerDatum cfg k ε R χ D depth` records the projected layers at one index `k` exactly as the
frozen premise states them (field `piece` is the frozen conjunction verbatim), and
`projected_unpack` extracts the buffered depths and an eventual family of such data.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

open MeasureTheory Set Filter

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The three-layer datum at one index. -/
structure LayerDatum (cfg : Data α) (k : ℕ) (ε R χ D : ℝ) (depth : Fin 3 → ℝ) where
  ρs : Measure (α × ℝ)
  np : Fin 3 → ℕ
  C : (h : Fin 3) → Fin (np h) → Set α
  qp : (h : Fin 3) → Fin (np h) → Fin 3 → ℤ
  G : (h : Fin 3) → Fin (np h) → MvPolynomial (Fin 2) ℝ
  le_rho : ρs ≤ cfg.ρ k
  mass : ENNReal.ofReal (cfg.N k ^ (-ε)) ≤ ρs univ
  cover : ∀ᵐ p ∂ρs, ∀ h : Fin 3, ∃ i, p.1 ∈ C h i
  meas : ∀ h i, MeasurableSet (C h i)
  disj : ∀ h i i', i ≠ i' → Disjoint (C h i) (C h i')
  piece : ∀ h i, (∀ l ∈ C h i, ⌊cfg.b k l 3 / χ⌋ = qp h i 0 ∧ ⌊cfg.b k l 0 / χ⌋ = qp h i 1 ∧ ⌊cfg.b k l 1 / D⌋ = qp h i 2 ∧ (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε)) ∧ |(qp h i 0 : ℝ) * χ| + |(qp h i 1 : ℝ) * χ| + |(qp h i 2 : ℝ) * D| ≤ cfg.N k ^ ε ∧ (G h i).totalDegree ≤ 2 ∧ (∀ e, |(G h i).coeff e| ≤ cfg.N k ^ R) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, (qp h i 2 : ℝ) * D - t * ((qp h i 1 : ℝ) * χ) + D * w] (G h i)| ≤ cfg.N k ^ ε) ∧ (∀ l ∈ C h i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(cfg.x k l t) 2 - (qp h i 2 : ℝ) * D + t * ((qp h i 1 : ℝ) * χ)| ≤ cfg.N k ^ ε * D ∧ |(cfg.x k l t) 3 - MvPolynomial.eval ![t, (cfg.x k l t) 2] (G h i)| ≤ cfg.N k ^ ε * cfg.N k ^ (-depth h)) ∧ ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) * cfg.π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ)) ≤ cfg.ρ k (C h i ×ˢ Set.Icc (0 : ℝ) 1)
  sum : (∀ h, (∑ i : Fin (np h), ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) * cfg.π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (cfg.N k ^ ε))

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core
