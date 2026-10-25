import Submission.Obl.k4_row_cell_regularization.Palette

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace Submission.Obl.k4_row_cell_regularization

variable {α : Type} [MeasurableSpace α]
variable {ν : Measure α} {μ : Measure (α × ℝ)} {b v H : α → ℝ}
    {T : α × ℝ → Fin 2 → ℝ} {π : Measure ℝ} {E : ℝ}
    {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)} {h L S : ℝ}

/-- Once the directions and numerical loss are chosen, all original cells and witnesses
fit the exact finite interface. -/
theorem IncHyp.assemble (hyp : IncHyp ν μ b v H T π E F h L S)
    (K R : ℝ) (D : Finset ℤ) (hD : D ⊆ incBins h L)
    (hLK : L + 1 ≤ K) (hpoints : 8 * L ^ 2 ≤ K) (hproj : 2 ^ 18 * L ^ 6 ≤ K)
    (hmU : ∀ p ∈ incPoints h E L F, ∀ d ∈ D,
      originalMass μ h E L b v H T F p d ≤ K * h ^ 2 / (D.card : ℝ))
    (hmT : 1 / K ≤ ∑ p ∈ incPoints h E L F,
      ∑ d ∈ D, originalMass μ h E L b v H T F p d)
    (hcap : ∀ x r : ℝ, h ≤ r → r ≤ 1 →
      ((D.filter (fun d => binVel h d ∈ Icc x (x + r))).card : ℝ) ≤
        K * r ^ (S / 4) * (D.card : ℝ))
    (hnear : ∀ d₀ ∈ D,
      ((D.filter (fun d => |binVel h d - binVel h d₀| < 1 / R)).card : ℝ) ≤
        (D.card : ℝ) / (16 * K ^ 3)) :
    ∃ (P : Finset Point) (u : ℤ → ℝ) (c : Point → ℤ → ℝ) (C : Point → Set (α × ℝ)),
      (μ ≤ ENNReal.ofReal K • (ν.prod volume)) ∧
      (∀ p d, 0 ≤ c p d) ∧ ((P.card : ℝ) ≤ K / h ^ 2) ∧
      (∀ p ∈ P, ∀ d ∈ D, c p d ≤ K * h ^ 2 / (D.card : ℝ)) ∧
      (1 / K ≤ ∑ p ∈ P, ∑ d ∈ D, c p d) ∧
      (∀ d ∈ D, |u d| ≤ K) ∧
      (∀ p ∈ P, ∀ j : Fin 4, |h * (p j : ℝ)| ≤ K) ∧
      (∀ q : ℤ × ℤ, ((P.filter (fun p => (p 0, p 1) = q)).card : ℝ) ≤ K) ∧
      (∀ d ∈ D, (((P.filter (fun p => 0 < c p d)).image
        (fun p => (⌊(p 1 : ℝ) - u d * (p 0 : ℝ)⌋,
          ⌊(p 2 : ℝ) + u d * (p 3 : ℝ)⌋))).card : ℝ) ≤ K / h) ∧
      (∀ x r : ℝ, h ≤ r → r ≤ 1 →
        ((D.filter (fun d => u d ∈ Icc x (x + r))).card : ℝ) ≤
          K * r ^ (S / 4) * (D.card : ℝ)) ∧
      (∀ d₀ ∈ D, ((D.filter (fun d => |u d - u d₀| < 1 / R)).card : ℝ) ≤
        (D.card : ℝ) / (16 * K ^ 3)) ∧
      (∀ p, MeasurableSet (C p)) ∧
      Pairwise (fun p q => Disjoint (C p) (C q)) ∧
      (∀ p ∈ P, ENNReal.ofReal (∑ d ∈ D, c p d) ≤ μ (C p)) ∧
      (∀ p ∈ P, ∀ x ∈ C p,
        |trajPos b v x 0| ≤ 1 ∧ |trajPos b v x 1| ≤ K ∧ ∀ j, |T x j| ≤ K) ∧
      (∀ p ∈ P, ∀ x ∈ C p, ∀ j : Fin 2,
        |trajPos b v x j - h * ((![p 0, p 1] : Fin 2 → ℤ) j : ℝ)| ≤ h) ∧
      (∀ p ∈ P, ∀ x ∈ C p, ∀ j : Fin 2,
        |(h / E) * T x j - h * ((![p 2, p 3] : Fin 2 → ℤ) j : ℝ)| ≤ h) := by
  have hL : L ≤ K := by linarith
  refine ⟨incPoints h E L F, binVel h, originalMass μ h E L b v H T F,
    originalCell h E L b v H T F, ?_, originalMass_nonneg, ?_, hmU, hmT,
    ?_, ?_, ?_, ?_, hcap, hnear, hyp.measurable_originalCell,
    originalCell_disjoint, (fun p _ => hyp.originalCell_mass p D), ?_,
    (fun p _ x hx j => hyp.originalCell_position hx j),
    (fun p _ x hx j => hyp.originalCell_row hx j)⟩
  · apply hyp.domination.trans
    intro A
    change ENNReal.ofReal L * (ν.prod volume) A ≤ ENNReal.ofReal K * (ν.prod volume) A
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hL) zero_le
  · exact (incPoints_card hyp.h_pos hyp.h_lt_one.le hyp.one_le_L hyp.bins_card).trans
      (div_le_div_of_nonneg_right hpoints (sq_nonneg h))
  · intro d hd
    exact (incBins_velocity_bound hyp.h_pos hyp.h_lt_one.le (hD hd)).trans hLK
  · intro p hp j
    exact (incPoints_center hyp.h_pos hyp.h_lt_one.le hyp.h_le_E
      (by linarith [hyp.one_le_L]) hp j).trans hLK
  · intro q
    exact (hyp.position_fiber_card q).trans hL
  · intro d _
    exact (hyp.originalMass_projection_card d).trans
      (div_le_div_of_nonneg_right hproj hyp.h_pos.le)
  · intro p _ x hx
    obtain ⟨ht, hz, hT⟩ := hyp.originalCell_bounds hx
    exact ⟨ht, hz.trans hL, fun j => (hT j).trans hL⟩

end Submission.Obl.k4_row_cell_regularization
