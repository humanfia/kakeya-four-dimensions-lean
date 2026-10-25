/- Inlined and adapted from LOT tree g-oai-074, obligation o250, session x0879,
commit 65c4e2637434d106fc91d7e4dede209e05034e55, files Submission/Obl/k4_horizontal_wide_interval_return/Core/Datum.lean and Core/Comparison.lean.
Only the datum and its reference-sum proof are adapted; the supplied comparison
is recorded as the existing frozen o274 premise. Earlier provenance: none. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Model

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Filter

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The three-layer datum at one index. -/
structure ComparedLayers (cfg : Data α) (k : ℕ) (ε R χ D : ℝ) (depth : Fin 3 → ℝ) (s u : ℝ) where
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

  agree : ∀ᵐ p ∂ρs, ∀ h : Fin 3, h ≠ 0 →
    ∀ (i₀ : Fin (np 0)) (ih : Fin (np h)), p.1 ∈ C 0 i₀ → p.1 ∈ C h ih →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
        |MvPolynomial.eval ![t, (qp 0 i₀ 2 : ℝ) * D - t * ((qp 0 i₀ 1 : ℝ) * χ) + D * w]
          (G h ih - G 0 i₀)| ≤ cfg.N k ^ (ε + (10 / (1 - cfg.d)) * u) * cfg.N k ^ (-s)

/-- Unpack precisely the strengthened frozen premise; no new assignments,
references or measures are introduced. -/
theorem Data.ProjectedAt.comparedLayers {cfg : Data α} {k : ℕ} {s₀ s u v R M ε : ℝ}
    (h : cfg.ProjectedAt k s₀ s u v R M ε) :
    Nonempty (ComparedLayers cfg k ε R (cfg.N k ^ (-M)) (cfg.N k ^ (-2 * cfg.κ * s₀))
      ![s, s + u, s + v] s u) := by
  obtain ⟨ρs, np, C, qp, G, hle, hmass, hcover, hmeas, hdisj, hpiece, hsum, hagree⟩ := h
  exact ⟨⟨ρs, np, C, qp, G, hle, hmass, hcover, hmeas, hdisj, hpiece, hsum, hagree⟩⟩

namespace ComparedLayers

variable {cfg : Data α} {k : ℕ} {ε R χ D s u : ℝ} {depth : Fin 3 → ℝ}
    (L : ComparedLayers cfg k ε R χ D depth s u)

/-- The unchanged full-strip reference of a projected piece. -/
def reference (h : Fin 3) (i : Fin (L.np h)) : ℝ :=
  χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d *
    (cfg.π k (Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ))).toReal

theorem reference_nonneg (hN : 0 < cfg.N k) (hχ : 0 ≤ χ) (hD : 0 ≤ D)
    (h : Fin 3) (i : Fin (L.np h)) : 0 ≤ L.reference h i := by
  unfold reference
  positivity

theorem sum_reference_le [IsFiniteMeasure (cfg.π k)]
    (hN : 0 < cfg.N k) (hχ : 0 ≤ χ) (hD : 0 ≤ D) (h : Fin 3) :
    ∑ i, L.reference h i ≤ cfg.N k ^ ε := by
  have hc : 0 ≤ χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d := by positivity
  have hfin : ∀ i, ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) *
      cfg.π k (Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ)) ≠ ⊤ :=
    fun i => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have heq : ∑ i, L.reference h i =
      (∑ i, ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) *
        cfg.π k (Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ))).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => hfin i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
    rfl
  rw [heq]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (L.sum h)).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

end ComparedLayers

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
