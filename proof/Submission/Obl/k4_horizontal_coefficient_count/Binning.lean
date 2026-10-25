import Submission.Obl.k4_horizontal_coefficient_count.Families

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

def horizontalCode (χ a : ℝ) (b : Fin 6 → ℝ) : Fin 5 → ℤ :=
  ![⌊b 3 / χ⌋, ⌊b 0 / a⌋, ⌊b 1 / a⌋, ⌊b 2 / a⌋, ⌊b 5 / a⌋]

theorem measurable_horizontalCode {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (χ a : ℝ) :
    Measurable (fun l => horizontalCode χ a (b l)) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> dsimp [horizontalCode] <;> fun_prop

theorem affine_error_of_horizontalCode_eq {χ a : ℝ} (ha : 0 < a)
    {b b' : Fin 6 → ℝ} (h : horizontalCode χ a b = horizontalCode χ a b')
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |b 2 + t * b 5 - (b' 2 + t * b' 5)| ≤ 2 * a := by
  have he (i : Fin 6) (hi : ⌊b i / a⌋ = ⌊b' i / a⌋) : |b i - b' i| ≤ a := by
    have hh := (Int.abs_sub_lt_one_of_floor_eq_floor hi).le
    rw [← sub_div, abs_div, abs_of_pos ha, div_le_iff₀ ha] at hh
    simpa using hh
  have h₂ := he 2 (by simpa [horizontalCode] using congrFun h 3)
  have h₅ := he 5 (by simpa [horizontalCode] using congrFun h 4)
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  calc
    _ = |(b 2 - b' 2) + t * (b 5 - b' 5)| := by congr 1; ring
    _ ≤ |b 2 - b' 2| + |t| * |b 5 - b' 5| := by
      simpa only [abs_mul] using abs_add_le (b 2 - b' 2) (t * (b 5 - b' 5))
    _ ≤ a + 1 * a := add_le_add h₂ (mul_le_mul ht' h₅ (abs_nonneg _) zero_le_one)
    _ = 2 * a := by ring

/-- Construct the geometric witnesses for any chosen finite set of occupied
coefficient bins, using actual input representatives. -/
def binnedFamily {α : Type*} [MeasurableSpace α]
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (G : Set α) (hG : MeasurableSet G)
    {χ a L C M : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hC : L ≤ C)
    (hM : 2 * L ≤ M) (hM2 : 2 ≤ M)
    (hbound : ∀ l ∈ G, |b l 2| ≤ L ∧ |b l 5| ≤ L)
    (Q : Finset (Fin 5 → ℤ)) (hQ : (Q : Set (Fin 5 → ℤ)) ⊆ horizontalCode χ a ∘ b '' G) :
    PredictorFamily b χ a a C M := by
  classical
  let e : Q ≃ Fin Q.card := Q.equivFin
  have hrep : ∀ q : Q, ∃ l, l ∈ G ∧ horizontalCode χ a (b l) = q.val := by
    intro q
    obtain ⟨l, hl, heq⟩ := hQ q.property
    exact ⟨l, hl, heq⟩
  choose rep hrepG hrepCode using hrep
  let r (i : Fin Q.card) : α := rep (e.symm i)
  let A (i : Fin Q.card) : Set α :=
    {l | l ∈ G ∧ horizontalCode χ a (b l) = (e.symm i).val}
  refine {
    n := Q.card
    A := A
    q := fun i => ![(e.symm i).val 0, (e.symm i).val 1, (e.symm i).val 2]
    h := fun i => ![b (r i) 2, b (r i) 5, 0, 0, 0, 0]
    measurable := ?_
    disjoint := ?_
    bins := ?_
    coefficients := ?_
    norm := ?_
    fit := ?_ }
  · intro i
    exact hG.inter ((measurable_horizontalCode hb χ a) (measurableSet_singleton _))
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro l hl hl'
    exact hij (e.symm.injective (Subtype.ext (hl.2.symm.trans hl'.2)))
  · intro i l hl
    exact ⟨by simpa [horizontalCode] using congrFun hl.2 0,
      by simpa [horizontalCode] using congrFun hl.2 1,
      by simpa [horizontalCode] using congrFun hl.2 2⟩
  · intro i j
    have hri := hbound (r i) (hrepG (e.symm i))
    have hC0 : 0 ≤ C := hL.trans hC
    fin_cases j
    · change |b (r i) 2| ≤ C
      exact hri.1.trans hC
    · change |b (r i) 5| ≤ C
      exact hri.2.trans hC
    all_goals simpa using hC0
  · intro i t ht p hp q hq
    have hri := hbound (r i) (hrepG (e.symm i))
    have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
    change |b (r i) 2 + b (r i) 5 * t + (0 + 0 * t) * p + (0 + 0 * t) * q| ≤ M
    simp only [zero_mul, add_zero]
    calc
      |b (r i) 2 + b (r i) 5 * t| ≤ |b (r i) 2| + |b (r i) 5| * |t| := by
        simpa only [abs_mul] using abs_add_le (b (r i) 2) (b (r i) 5 * t)
      _ ≤ L + L * 1 := add_le_add hri.1 (mul_le_mul hri.2 ht' (abs_nonneg _) hL)
      _ ≤ M := by linarith
  · intro i l hl t ht
    have heq : horizontalCode χ a (b l) = horizontalCode χ a (b (r i)) :=
      hl.2.trans (hrepCode (e.symm i)).symm
    have hh := affine_error_of_horizontalCode_eq ha heq ht
    change |b l 2 + t * b l 5 - (b (r i) 2 + b (r i) 5 * t +
      (0 + 0 * t) * b l 0 + (0 + 0 * t) * b l 1)| ≤ M * a
    simp only [zero_mul, add_zero]
    calc
      _ = |b l 2 + t * b l 5 - (b (r i) 2 + t * b (r i) 5)| := by congr 1; ring
      _ ≤ 2 * a := hh
      _ ≤ M * a := mul_le_mul_of_nonneg_right hM2 ha.le

section BinnedProperties

variable {α : Type*} [MeasurableSpace α]
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (G : Set α) (hG : MeasurableSet G)
    {χ a L C M : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hC : L ≤ C)
    (hM : 2 * L ≤ M) (hM2 : 2 ≤ M)
    (hbound : ∀ l ∈ G, |b l 2| ≤ L ∧ |b l 5| ≤ L)
    (Q : Finset (Fin 5 → ℤ)) (hQ : (Q : Set (Fin 5 → ℤ)) ⊆ horizontalCode χ a ∘ b '' G)

theorem binnedFamily_cover (l : α) :
    (∃ i, l ∈ (binnedFamily b hb G hG ha hL hC hM hM2 hbound Q hQ).A i) ↔
      l ∈ G ∧ horizontalCode χ a (b l) ∈ Q := by
  classical
  change (∃ i : Fin Q.card, l ∈ G ∧
    horizontalCode χ a (b l) = (Q.equivFin.symm i).val) ↔ _
  constructor
  · rintro ⟨i, hl, hi⟩
    exact ⟨hl, hi.symm ▸ (Q.equivFin.symm i).property⟩
  · rintro ⟨hl, hcode⟩
    refine ⟨Q.equivFin ⟨horizontalCode χ a (b l), hcode⟩, hl, ?_⟩
    simp

theorem binnedFamily_sum_weight (π : Measure ℝ) (d Z : ℝ) :
    (∑ i, (binnedFamily b hb G hG ha hL hC hM hM2 hbound Q hQ).weight π d Z i) =
      ENNReal.ofReal (a ^ 2 * a ^ d / Z) *
        ∑ q ∈ Q, π (Ico ((q 0 : ℝ) * χ) (((q 0 : ℝ) + 1) * χ)) := by
  classical
  let w (q : Fin 5 → ℤ) := π (Ico ((q 0 : ℝ) * χ) (((q 0 : ℝ) + 1) * χ))
  change (∑ i : Fin Q.card, ENNReal.ofReal (a ^ 2 * a ^ d / Z) *
    w (Q.equivFin.symm i).val) = _
  rw [← Finset.mul_sum]
  congr 1
  calc
    (∑ i : Fin Q.card, w (Q.equivFin.symm i).val) = ∑ q : Q, w q.val :=
      Q.equivFin.symm.sum_comp (fun q : Q => w q.val)
    _ = ∑ q ∈ Q, w q := Finset.sum_attach _ _

end BinnedProperties

end
end Submission.Obl.k4_horizontal_coefficient_count
