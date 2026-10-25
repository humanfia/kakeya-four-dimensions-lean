import Submission.Obl.k4_scalar_grid_polynomial_qualification.GraphSelection

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

noncomputable section

def predecessorCells {n : ℕ} (a : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j => {a j - 1, a j}

theorem card_predecessorCells {n : ℕ} (a : Fin n → ℤ) :
    (predecessorCells a).card = 2 ^ n := by
  simp [predecessorCells, Fintype.card_piFinset]

theorem mem_predecessorCells_of_mem_successorCells {n : ℕ} {a a' : Fin n → ℤ}
    (h : a ∈ successorCells a') : a' ∈ predecessorCells a := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj := Fintype.mem_piFinset.mp h j
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj ⊢
  omega

/-- Moving both fine and coarse cell assignments to centers of the original
fine states costs at most four possibilities per physical coordinate. -/
theorem assigned_hereditary_cell_list {X : Type*} {n : ℕ}
    (Z : X → Fin n → ℝ) (E : Set X) {b p ρ B : ℝ}
    (hb : 0 < b) (hbp : b ≤ p) (hbρ : b ≤ ρ)
    (F : (Fin n → ℤ) → Finset (Fin n → ℤ))
    (hcard : ∀ q, ((F q).card : ℝ) ≤ B)
    (hmem : ∀ z ∈ E, cell p (Z z) ∈ F (cell ρ (Z z))) (q : Fin n → ℤ) :
    ∃ L : Finset (Fin n → ℤ), (L.card : ℝ) ≤ (4 : ℝ) ^ n * B ∧
      ∀ z ∈ E, cell ρ (leftCorner b (cell b (Z z))) = q →
        cell p (leftCorner b (cell b (Z z))) ∈ L := by
  classical
  let L := (successorCells q).biUnion (fun q₀ => (F q₀).biUnion predecessorCells)
  have hinner (q₀ : Fin n → ℤ) :
      (((F q₀).biUnion predecessorCells).card : ℝ) ≤ (2 : ℝ) ^ n * B := by
    calc
      _ ≤ ∑ a ∈ F q₀, ((predecessorCells a).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := F q₀) (t := predecessorCells)
      _ = ((F q₀).card : ℝ) * (2 : ℝ) ^ n := by
        simp only [card_predecessorCells, Nat.cast_pow, Nat.cast_ofNat,
          Finset.sum_const, nsmul_eq_mul]
      _ ≤ B * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_right (hcard q₀) (by positivity)
      _ = _ := mul_comm _ _
  refine ⟨L, ?_, ?_⟩
  · calc
      (L.card : ℝ) ≤ ∑ q₀ ∈ successorCells q,
          (((F q₀).biUnion predecessorCells).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := successorCells q)
          (t := fun q₀ => (F q₀).biUnion predecessorCells)
      _ ≤ ∑ _q₀ ∈ successorCells q, (2 : ℝ) ^ n * B :=
        Finset.sum_le_sum (fun q₀ _ => hinner q₀)
      _ = (2 : ℝ) ^ n * ((2 : ℝ) ^ n * B) := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_successorCells,
          Nat.cast_pow, Nat.cast_ofNat]
      _ = (4 : ℝ) ^ n * B := by rw [← mul_assoc, ← mul_pow]; norm_num
  · intro z hz hq
    have hcoarse : cell ρ (Z z) ∈ successorCells q := by
      simpa only [hq] using cell_mem_successorCells hb hbρ (Z z)
    exact Finset.mem_biUnion.mpr ⟨cell ρ (Z z), hcoarse,
      Finset.mem_biUnion.mpr ⟨cell p (Z z), hmem z hz,
        mem_predecessorCells_of_mem_successorCells (cell_mem_successorCells hb hbp (Z z))⟩⟩

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification
