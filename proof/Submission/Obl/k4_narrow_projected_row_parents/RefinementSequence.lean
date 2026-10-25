import Submission.Obl.k4_narrow_projected_row_parents.MajorRefinement
import Submission.Obl.k4_narrow_projected_row_parents.RefinementWidth
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

namespace Submission.Obl.k4_narrow_projected_row_parents.MajorRefinement

open MeasureTheory Set Filter
open Submission.Obl.k4_general_parent_projected_layers

variable {α : Type} [MeasurableSpace α]

/-- Refine every projected layer to a prescribed finer width, uniformly
in the exponent and without a mesh-ratio loss in the retained density. -/
theorem exists_refined_layers_at_width (N H : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hH : ∀ k, 1 ≤ H k) (hHsub : Model.Subpow N H)
    (d ell La s m : ℝ) (ξ : ℕ → ℝ) (hξ : ∀ k, 0 < ξ k)
    (hξold : ∀ k, ξ k ≤ N k ^ (-m))
    (b : ℕ → α → Fin 6 → ℝ) (hb : ∀ k, Measurable (b k))
    (P : ℕ → MvPolynomial (Fin 4) ℝ) (π : ℕ → Measure ℝ)
    (ρ ζ : ℕ → Measure (α × ℝ)) (L : ℕ → ProjLayer α)
    (hgood : ∀ k, (L k).Good (N k) (H k) d ell La s (N k ^ (-m)) (b k) (P k) (π k) (ρ k))
    (hbudget : ∀ k, ∑ i, (L k).weight (N k) d s (N k ^ (-m)) (π k) i ≤ ENNReal.ofReal (H k))
    (hζρ : ∀ k, ζ k ≤ ρ k) (hmass : ∀ k, ENNReal.ofReal (H k)⁻¹ ≤ ζ k univ)
    (hcover : ∀ k, ∀ᵐ z ∂ζ k, z.2 ∈ Icc (0 : ℝ) 1 ∧ ∃ i, z.1 ∈ (L k).C i) :
    Model.Subpow N (fun k => 4 * H k ^ 2) ∧
    ∃ (L' : ℕ → ProjLayer α) (ζ' : ℕ → Measure (α × ℝ))
      (toOld : (k : ℕ) → Fin (L' k).n → Fin (L k).n), ∀ k,
      ζ' k ≤ ζ k ∧ ENNReal.ofReal ((4 * H k ^ 2)⁻¹) ≤ ζ' k univ ∧ (L' k).β = (L k).β ∧
      (L' k).Good (N k) (4 * H k ^ 2) d ell La s
        (N k ^ (-m) / factor (N k ^ (-m)) (ξ k)) (b k) (P k) (π k) (ρ k) ∧
      (∀ i, (L' k).C i ⊆ (L k).C (toOld k i) ∧ (L' k).u i = (L k).u (toOld k i) ∧
        (L' k).v i = (L k).v (toOld k i) ∧ (L' k).G i = (L k).G (toOld k i)) ∧
      (∀ᵐ z ∂ζ' k, ∃ i, z.1 ∈ (L' k).C i) ∧
      ξ k / 2 ≤ N k ^ (-m) / factor (N k ^ (-m)) (ξ k) ∧
      N k ^ (-m) / factor (N k ^ (-m)) (ξ k) ≤ ξ k := by
  have hNp : ∀ k, 0 < N k := fun k => zero_lt_one.trans_le (hN k)
  have hsub : Model.Subpow N (fun k => 4 * H k ^ 2) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNp (fun _ => by norm_num)
      (fun k => sq_nonneg (H k))
      (Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hNt 4)
      (Submission.Obl.k4_discrete_of_terminal_charts.subpower_pow hN
        (fun k => zero_le_one.trans (hH k)) hHsub 2)
  have hJ (k : ℕ) : 0 < factor (N k ^ (-m)) (ξ k) :=
    (width_bounds (Real.rpow_pos_of_pos (hNp k) _) (hξ k) (hξold k)).1
  choose L' ζ' toOld hζ' hmass' hβ' hgood' hdata hcover' using fun k =>
    exists_dense_aligned_refinement (L k) (hNp k) (hH k) (Real.rpow_pos_of_pos (hNp k) _)
      (b k) (hb k) (P k) (π k) (ρ k) (ζ k) (hgood k) (hbudget k) (hζρ k) (hmass k)
      (hcover k) (hJ k)
  exact ⟨hsub, L', ζ', toOld, fun k =>
    ⟨hζ' k, hmass' k, hβ' k, hgood' k, hdata k, hcover' k,
      (width_bounds (Real.rpow_pos_of_pos (hNp k) _) (hξ k) (hξold k)).2⟩⟩

/-- Refine every projected layer to a prescribed finer power scale, uniformly
in the exponent and without a mesh-ratio loss in the retained density. -/
theorem exists_refined_layers (N H : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hH : ∀ k, 1 ≤ H k) (hHsub : Model.Subpow N H)
    (d ell La s m chiExp : ℝ) (hFine : m ≤ chiExp)
    (b : ℕ → α → Fin 6 → ℝ) (hb : ∀ k, Measurable (b k))
    (P : ℕ → MvPolynomial (Fin 4) ℝ) (π : ℕ → Measure ℝ)
    (ρ ζ : ℕ → Measure (α × ℝ)) (L : ℕ → ProjLayer α)
    (hgood : ∀ k, (L k).Good (N k) (H k) d ell La s (N k ^ (-m)) (b k) (P k) (π k) (ρ k))
    (hbudget : ∀ k, ∑ i, (L k).weight (N k) d s (N k ^ (-m)) (π k) i ≤ ENNReal.ofReal (H k))
    (hζρ : ∀ k, ζ k ≤ ρ k) (hmass : ∀ k, ENNReal.ofReal (H k)⁻¹ ≤ ζ k univ)
    (hcover : ∀ k, ∀ᵐ z ∂ζ k, z.2 ∈ Icc (0 : ℝ) 1 ∧ ∃ i, z.1 ∈ (L k).C i) :
    Model.Subpow N (fun k => 4 * H k ^ 2) ∧
    ∃ (L' : ℕ → ProjLayer α) (ζ' : ℕ → Measure (α × ℝ))
      (toOld : (k : ℕ) → Fin (L' k).n → Fin (L k).n), ∀ k,
      ζ' k ≤ ζ k ∧ ENNReal.ofReal ((4 * H k ^ 2)⁻¹) ≤ ζ' k univ ∧ (L' k).β = (L k).β ∧
      (L' k).Good (N k) (4 * H k ^ 2) d ell La s
        (N k ^ (-m) / factor (N k ^ (-m)) (N k ^ (-chiExp))) (b k) (P k) (π k) (ρ k) ∧
      (∀ i, (L' k).C i ⊆ (L k).C (toOld k i) ∧ (L' k).u i = (L k).u (toOld k i) ∧
        (L' k).v i = (L k).v (toOld k i) ∧ (L' k).G i = (L k).G (toOld k i)) ∧
      (∀ᵐ z ∂ζ' k, ∃ i, z.1 ∈ (L' k).C i) ∧
      N k ^ (-chiExp) / 2 ≤ N k ^ (-m) / factor (N k ^ (-m)) (N k ^ (-chiExp)) ∧
      N k ^ (-m) / factor (N k ^ (-m)) (N k ^ (-chiExp)) ≤ N k ^ (-chiExp) := by
  have hNp : ∀ k, 0 < N k := fun k => zero_lt_one.trans_le (hN k)
  have hsub : Model.Subpow N (fun k => 4 * H k ^ 2) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNp (fun _ => by norm_num)
      (fun k => sq_nonneg (H k))
      (Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hNt 4)
      (Submission.Obl.k4_discrete_of_terminal_charts.subpower_pow hN
        (fun k => zero_le_one.trans (hH k)) hHsub 2)
  have hJ (k : ℕ) : 0 < factor (N k ^ (-m)) (N k ^ (-chiExp)) :=
    (power_width_bounds N hN hFine k).1
  choose L' ζ' toOld hζ' hmass' hβ' hgood' hdata hcover' using fun k =>
    exists_dense_aligned_refinement (L k) (hNp k) (hH k) (Real.rpow_pos_of_pos (hNp k) _)
      (b k) (hb k) (P k) (π k) (ρ k) (ζ k) (hgood k) (hbudget k) (hζρ k) (hmass k)
      (hcover k) (hJ k)
  exact ⟨hsub, L', ζ', toOld, fun k =>
    ⟨hζ' k, hmass' k, hβ' k, hgood' k, hdata k, hcover' k,
      (power_width_bounds N hN hFine k).2⟩⟩

end Submission.Obl.k4_narrow_projected_row_parents.MajorRefinement
