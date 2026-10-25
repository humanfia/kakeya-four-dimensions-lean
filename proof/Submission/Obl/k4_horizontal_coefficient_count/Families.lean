import Submission.Obl.k4_horizontal_coefficient_count.Common

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

def predictor (h : Fin 6 → ℝ) (t p q : ℝ) : ℝ :=
  h 0 + h 1 * t + (h 2 + h 3 * t) * p + (h 4 + h 5 * t) * q

/-- Geometric witnesses of one finite, disjoint full-time predictor family.
The floor and the current measure are deliberately separate. -/
structure PredictorFamily {α : Type*} [MeasurableSpace α]
    (b : α → Fin 6 → ℝ) (χ D a C M : ℝ) where
  n : ℕ
  A : Fin n → Set α
  q : Fin n → Fin 3 → ℤ
  h : Fin n → Fin 6 → ℝ
  measurable : ∀ i, MeasurableSet (A i)
  disjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  bins : ∀ i l, l ∈ A i →
    ⌊b l 3 / χ⌋ = q i 0 ∧ ⌊b l 0 / D⌋ = q i 1 ∧ ⌊b l 1 / D⌋ = q i 2
  coefficients : ∀ i e, |h i e| ≤ C
  norm : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
    ∀ p ∈ Icc ((q i 1 : ℝ) * D) (((q i 1 : ℝ) + 1) * D),
    ∀ q' ∈ Icc ((q i 2 : ℝ) * D) (((q i 2 : ℝ) + 1) * D),
      |predictor (h i) t p q'| ≤ M
  fit : ∀ i l, l ∈ A i → ∀ t ∈ Icc (0 : ℝ) 1,
    |b l 2 + t * b l 5 - predictor (h i) t (b l 0) (b l 1)| ≤ M * a

namespace PredictorFamily

variable {α : Type*} [MeasurableSpace α] {b : α → Fin 6 → ℝ}
  {χ D a C M : ℝ} (f : PredictorFamily b χ D a C M)

def cell (i : Fin f.n) : Set (α × ℝ) := f.A i ×ˢ Icc (0 : ℝ) 1

def weight (π : Measure ℝ) (d Z : ℝ) (i : Fin f.n) : ENNReal :=
  ENNReal.ofReal (D ^ 2 * a ^ d / Z) *
    π (Ico ((f.q i 0 : ℝ) * χ) (((f.q i 0 : ℝ) + 1) * χ))

def Covers (ρ : Measure (α × ℝ)) : Prop :=
  ρ {p | ∃ i, p.1 ∈ f.A i}ᶜ = 0

def Floors (π : Measure ℝ) (d Z : ℝ) (ρ : Measure (α × ℝ)) : Prop :=
  ∀ i, f.weight π d Z i ≤ ρ (f.cell i)

theorem weight_div (π : Measure ℝ) (d : ℝ) {Z : ℝ} (hZ : 0 < Z) (i : Fin f.n) :
    f.weight π d Z i = ENNReal.ofReal Z⁻¹ * f.weight π d 1 i := by
  unfold weight
  rw [div_one, div_eq_mul_inv, mul_comm (D ^ 2 * a ^ d) Z⁻¹,
    ENNReal.ofReal_mul (inv_nonneg.mpr hZ.le), mul_assoc]

theorem sum_weight_div (π : Measure ℝ) (d : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    (∑ i, f.weight π d Z i) = ENNReal.ofReal Z⁻¹ * ∑ i, f.weight π d 1 i := by
  simp_rw [f.weight_div π d hZ]
  rw [Finset.mul_sum]

theorem weight_ratio (π : Measure ℝ) (d : ℝ) {Z₀ Z : ℝ}
    (hZ₀ : 0 < Z₀) (hZ : 0 < Z) (i : Fin f.n) :
    f.weight π d Z i = ENNReal.ofReal (Z₀ / Z) * f.weight π d Z₀ i := by
  unfold weight
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hZ₀.le hZ.le)]
  congr 2
  field_simp

theorem sum_cell_le (ρ : Measure (α × ℝ)) : (∑ i, ρ (f.cell i)) ≤ ρ univ := by
  have hd : (↑(Finset.univ : Finset (Fin f.n)) : Set (Fin f.n)).PairwiseDisjoint f.cell := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    rintro p ⟨hpi, hpt⟩ ⟨hpj, hpt'⟩
    exact Set.disjoint_left.mp (f.disjoint i j hij) hpi hpj
  rw [← measure_biUnion_finset hd (fun i _ => (f.measurable i).prod measurableSet_Icc)]
  exact measure_mono (subset_univ _)

/-- Floors measured before a later restriction pay for the sum of all
smaller proposed floors using the original, disjoint assignment masses. -/
theorem final_threshold_budget (π : Measure ℝ) (d : ℝ) {Z₀ Z : ℝ}
    (hZ₀ : 0 < Z₀) (hZ : 0 < Z) (ρ : Measure (α × ℝ))
    (hf : f.Floors π d Z₀ ρ) :
    (∑ i, f.weight π d Z i) ≤ ENNReal.ofReal (Z₀ / Z) * ρ univ := by
  simp_rw [f.weight_ratio π d hZ₀ hZ]
  rw [← Finset.mul_sum]
  exact mul_le_mul' le_rfl ((Finset.sum_le_sum (fun i _ => hf i)).trans (f.sum_cell_le ρ))

/-- Passing to a subfamily keeps every geometric witness unchanged. -/
def reindex {n' : ℕ} (idx : Fin n' → Fin f.n) (hinj : Function.Injective idx) :
    PredictorFamily b χ D a C M where
  n := n'
  A := f.A ∘ idx
  q := f.q ∘ idx
  h := f.h ∘ idx
  measurable i := f.measurable (idx i)
  disjoint i j hij := f.disjoint (idx i) (idx j) (fun h => hij (hinj h))
  bins i := f.bins (idx i)
  coefficients i := f.coefficients (idx i)
  norm i := f.norm (idx i)
  fit i := f.fit (idx i)

end PredictorFamily

end

end Submission.Obl.k4_horizontal_coefficient_count
