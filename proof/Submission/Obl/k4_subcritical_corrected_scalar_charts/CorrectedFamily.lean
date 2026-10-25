/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/CorrectedFamily.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.CorrectedBaseline

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory

noncomputable section

namespace ChartFamily

variable {α : Type} [MeasurableSpace α]

/-- The full original chart properties, before restricting the incidence law
to the selected correction times. In particular the floor is still for `cfg.ρ`. -/
structure SeedPrepared (C : ChartFamily α) (cfg : Data α) (k : ℕ)
    (χ D A ξ E : ℝ) : Prop where
  measurable : ∀ c, MeasurableSet (C.G c)
  disjoint : ∀ c c', c ≠ c' → Disjoint (C.G c) (C.G c')
  labels : ∀ c, ∀ l ∈ C.G c,
    ⌊cfg.b k l 3 / χ⌋ = C.q c 0 ∧ ⌊cfg.b k l 0 / D⌋ = C.q c 1 ∧
      ⌊cfg.b k l 1 / D⌋ = C.q c 2 ∧ (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ξ) ∧
      |cfg.b k l 4 + cfg.b k l 0| ≤ χ
  box : ∀ c, ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ p ∈ Icc ((C.q c 1 : ℝ) * D) (((C.q c 1 : ℝ) + 1) * D),
    ∀ q ∈ Icc ((C.q c 2 : ℝ) * D) (((C.q c 2 : ℝ) + 1) * D),
      |parameterPredictor (C.g c) t p q| ≤ E
  fit : ∀ c, ∀ l ∈ C.G c, ∀ t ∈ Icc (0 : ℝ) 1,
    |chartSignal A (C.g c) (cfg.b k l) t| ≤ E
  floor : ∀ c,
    ENNReal.ofReal (D ^ 2 * A ^ cfg.d / cfg.N k ^ ξ) *
      cfg.π k (Ico ((C.q c 0 : ℝ) * χ) (((C.q c 0 : ℝ) + 1) * χ)) ≤
      cfg.ρ k (C.G c ×ˢ Icc (0 : ℝ) 1)

/-- Preserve the original full chart domains and labels when adding the common
quadratic time primitive. -/
def withCorrections (C : ChartFamily α) (β : Fin C.n → Fin 3 → ℝ) (A D : ℝ) :
    ChartFamily α where
  n := C.n
  G := C.G
  q := C.q
  g c := correctedBaseline (C.g c) (β c) A D
    ((C.q c 1 : ℝ) * D) ((C.q c 2 : ℝ) * D)

/-- Assemble the chart interface after retaining good times. The original
full-chart floors are passed through unchanged. -/
theorem SeedPrepared.corrected_prepared {C : ChartFamily α} {cfg : Data α} {k : ℕ}
    {χ D A σ ξ E B : ℝ} {w : Fin 3 → ℝ} {ρ' : Measure (α × ℝ)}
    (seed : C.SeedPrepared cfg k χ D A ξ E)
    (β : Fin C.n → Fin 3 → ℝ) (hβ : ∀ c e, |β c e| ≤ B)
    (hA : 0 < A) (hA1 : A ≤ 1) (hD : 0 < D)
    (hbudget : E + 3 * B ≤ cfg.N k ^ ξ)
    (hle : ρ' ≤ cfg.ρ k) (hmass : ENNReal.ofReal (cfg.N k ^ (-ξ)) ≤ ρ' univ)
    (hcover : ∀ᵐ p ∂ρ', ∃ c, p.1 ∈ C.G c)
    (hsupport : ∀ c (h : Fin 3), ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) * σ ^ 2 ≤ cfg.N k ^ ξ * (w h) ^ (-cfg.d) ∧
      ∀ᵐ p ∂ρ', p.1 ∈ C.G c →
        (chartCell D σ (C.q c 1) (C.q c 2) (cfg.b k p.1) p.2,
          ⌊chartSignal A ((C.withCorrections β A D).g c) (cfg.b k p.1) p.2 / w h⌋) ∈ F) :
    (C.withCorrections β A D).Prepared cfg k χ D A σ ξ w ρ' := by
  refine ⟨hle, hmass, hcover, seed.measurable, seed.disjoint, seed.labels,
    ?_, ?_, seed.floor, hsupport⟩
  · intro c t ht p hp q hq
    have hB : 0 ≤ B := (abs_nonneg _).trans (hβ c 0)
    have hbox : ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ p ∈ Icc ((C.q c 1 : ℝ) * D) ((C.q c 1 : ℝ) * D + D),
        ∀ q ∈ Icc ((C.q c 2 : ℝ) * D) ((C.q c 2 : ℝ) * D + D),
          |parameterPredictor (C.g c) t p q| ≤ E := by
      simpa only [add_mul, one_mul] using seed.box c
    have hp' : p ∈ Icc ((C.q c 1 : ℝ) * D) ((C.q c 1 : ℝ) * D + D) := by
      simpa only [withCorrections, add_mul, one_mul] using hp
    have hq' : q ∈ Icc ((C.q c 2 : ℝ) * D) ((C.q c 2 : ℝ) * D + D) := by
      simpa only [withCorrections, add_mul, one_mul] using hq
    exact (correctedBaseline_box_bound hA.le hD (hβ c) hbox ht hp' hq').trans
      (by nlinarith)
  · intro c l hl t ht
    exact (correctedBaseline_fit_bound hA.ne' hD (hβ c) ht
      (seed.labels c l hl).2.1 (seed.labels c l hl).2.2.1
      (seed.fit c l hl t ht)).trans hbudget

end ChartFamily

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
