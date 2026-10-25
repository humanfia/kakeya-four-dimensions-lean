import Submission.Obl.k4_finite_row_graph_assembly.FiniteGraph

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/ExpandedFinite.lean.
import Submission.Obl.k4_finite_row_graph_assembly.Unpack

namespace Submission.Obl.k4_finite_row_graph_assembly

/-- The complete finite stage with all hypotheses expanded to Mathlib types. -/
theorem expanded_finite_construction :
    ∀ h E K R s L : ℝ, 0 < h → h ≤ 1 → 1 ≤ K → 2 ≤ R → K ≤ R → 0 ≤ s →
    K ≤ L → R ^ 3 ≤ L → K + K ^ 2 + 1 ≤ L →
    K * (2048 * K ^ 11 * (6 * R ^ 2 + 2) ^ 4) ≤ L →
    K * (10 + 6 * R ^ 3) ^ 2 ≤ L →
    (6 * R ^ 2 + 2) ^ 2 * K * (2048 * K ^ 11 * (6 * R ^ 2 + 2) ^ 4) ≤ L →
    512 * K ^ 10 * (R ^ 6) ^ s ≤ L → 8 * K ^ 5 ≤ L → 2 + K ≤ L →
    ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α)
      (μ : MeasureTheory.Measure (α × ℝ)) (z T : α × ℝ → Fin 2 → ℝ)
      (P : Finset (Fin 4 → ℤ)) (D : Finset ℤ) (u : ℤ → ℝ)
      (mass : (Fin 4 → ℤ) → ℤ → ℝ) (C : (Fin 4 → ℤ) → Set (α × ℝ)),
    (∀ p d, 0 ≤ mass p d) → ((P.card : ℝ) ≤ K / h ^ 2) →
    (∀ p ∈ P, ∀ d ∈ D, mass p d ≤ K * h ^ 2 / D.card) →
    (1 / K ≤ ∑ p ∈ P, ∑ d ∈ D, mass p d) →
    (∀ d ∈ D, |u d| ≤ K) → (∀ p ∈ P, ∀ j, |h * (p j : ℝ)| ≤ K) →
    (∀ q : ℤ × ℤ, ((P.filter (fun p => (p 0, p 1) = q)).card : ℝ) ≤ K) →
    (∀ d ∈ D, (((P.filter (fun p => 0 < mass p d)).image
      (fun p => (⌊(p 1 : ℝ) - u d * (p 0 : ℝ)⌋,
        ⌊(p 2 : ℝ) + u d * (p 3 : ℝ)⌋))).card : ℝ) ≤ K / h) →
    (∀ x r : ℝ, h ≤ r → r ≤ 1 →
      ((D.filter (fun d => u d ∈ Set.Icc x (x + r))).card : ℝ) ≤ K * r ^ s * D.card) →
    (∀ d₀ ∈ D, ((D.filter (fun d => |u d - u d₀| < 1 / R)).card : ℝ) ≤
      D.card / (16 * K ^ 3)) →
    (∀ p, MeasurableSet (C p)) →
    Pairwise (fun p q => Disjoint (C p) (C q)) →
    (∀ p ∈ P, ENNReal.ofReal (∑ d ∈ D, mass p d) ≤ μ (C p)) →
    (∀ p ∈ P, ∀ x ∈ C p, |z x 0| ≤ 1 ∧ |z x 1| ≤ K ∧ ∀ j, |T x j| ≤ K) →
    (∀ p ∈ P, ∀ x ∈ C p, ∀ j : Fin 2,
      |z x j - h * ((![p 0, p 1] : Fin 2 → ℤ) j : ℝ)| ≤ h) →
    (∀ p ∈ P, ∀ x ∈ C p, ∀ j : Fin 2,
      |(h / E) * T x j - h * ((![p 2, p 3] : Fin 2 → ℤ) j : ℝ)| ≤ h) →
    (μ ≤ ENNReal.ofReal K • (ν.prod MeasureTheory.volume)) →
    ∃ (m : ℕ) (w κ : Fin m → ℝ) (A B : Finset (ℝ × ℝ)) (G : Fin m → Finset ((ℝ × ℝ) × (ℝ × ℝ))) (u₁ u₂ : ℝ) (W : ((ℝ × ℝ) × (ℝ × ℝ)) → Set (α × ℝ)), (∀ x ∈ A, ∃ a b : ℤ, x = (h * a, h * b)) ∧ (∀ y ∈ B, ∃ a b : ℤ, y = (h * a, h * b)) ∧ (∀ x ∈ A, |x.1| ≤ L ∧ |x.2| ≤ L) ∧ (∀ y ∈ B, |y.1| ≤ L ∧ |y.2| ≤ L) ∧ (1 / (L * h) ≤ (A.card : ℝ)) ∧ ((A.card : ℝ) ≤ L / h) ∧ (1 / (L * h) ≤ (B.card : ℝ)) ∧ ((B.card : ℝ) ≤ L / h) ∧ (∀ i : Fin m, 0 ≤ w i) ∧ ((∑ i : Fin m, w i) = 1) ∧ (∀ i : Fin m, 1 / L ≤ |κ i| ∧ |κ i| ≤ L) ∧ (∀ x r : ℝ, h ≤ r → r ≤ 1 → (∑ i : Fin m, if κ i ∈ Set.Icc x (x + r) then w i else 0) ≤ L * r ^ (s)) ∧ (∀ i : Fin m, G i ⊆ A ×ˢ B) ∧ (∀ i : Fin m, 1 / (L * h ^ 2) ≤ ((G i).card : ℝ)) ∧ (∀ i : Fin m, (((G i).image (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => (⌊(p.1.1 + κ i * p.2.1) / h⌋, ⌊(p.1.2 + κ i * p.2.2) / h⌋))).card : ℝ) ≤ L / h) ∧ (∀ (i : Fin m) (x y : ℝ), (((G i).filter (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => p.1.1 ∈ Set.Ico x (x + h) ∧ p.2.1 ∈ Set.Ico y (y + h))).card : ℝ) ≤ L * h ^ 2 * ((G i).card : ℝ)) ∧ (|u₁| ≤ L) ∧ (|u₂| ≤ L) ∧ (1 / L ≤ |u₂ - u₁|) ∧ (μ ≤ ENNReal.ofReal L • (ν.prod MeasureTheory.volume)) ∧ (∀ e, MeasurableSet (W e)) ∧ (Pairwise (fun e f => Disjoint (W e) (W f))) ∧ (∀ (i : Fin m) e, e ∈ G i → ENNReal.ofReal (h ^ 2 / L) ≤ μ (W e)) ∧ (∀ (i : Fin m) e, e ∈ G i → ∀ p ∈ W e, |z p 0| ≤ 1 ∧ |z p 1| ≤ L ∧ (∀ j, |T p j| ≤ L)) ∧ (∀ (i : Fin m) e, e ∈ G i → ∀ p ∈ W e, |z p 1 - u₁ * z p 0 - e.1.1| ≤ L * h ∧ |(h / E) * (T p 0 + u₁ * T p 1) - e.1.2| ≤ L * h ∧ |z p 1 - u₂ * z p 0 - e.2.1| ≤ L * h ∧ |(h / E) * (T p 0 + u₂ * T p 1) - e.2.2| ≤ L * h) := by
  intro h E K R s L hh hh1 hK hR hKR hs hL₁ hL₂ hL₃ hL₄ hL₅ hL₆ hL₇ hL₈ hL₉
    α inst ν μ z T P D u mass C hmass0 hP hmassU hmassT hu hcenter hfiber hcover
    hcap hnear hmeas hdisj hmass hbound hpos hrow hdom
  let f : FiniteIncidenceData h K R s :=
    ⟨P, D, u, mass, hmass0, hP, hmassU, hmassT, hu, hcenter, hfiber, hcover, hcap, hnear⟩
  let cw : CellWitnessData μ z T h E K R s f :=
    ⟨C, hmeas, hdisj, hmass, hbound, hpos, hrow⟩
  have hLoss : LossBounds K R s L :=
    ⟨hL₁, hL₂, hL₃, hL₄, hL₅, hL₆, hL₇, hL₈, hL₉⟩
  exact unpack_witness (finite_graph_construction ν μ z T hh hh1 hK hR hKR hs hLoss f cw hdom)

end Submission.Obl.k4_finite_row_graph_assembly
