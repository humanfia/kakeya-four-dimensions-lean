/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file RowPreparation.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.GraphLists

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

/-- The original positive-mass row counts alone supply whole-cell row
selection on any residual submeasure. Finiteness, the common null core and
the boundary lists are all established internally. -/
theorem prepare_original_graph_rows {X : Type*} [MeasurableSpace X] {D q : ℕ}
    (μ ν : Measure X) (hμν : μ ≤ ν)
    (Z : X → Fin D → ℝ) (hZ : Measurable Z) {b : ℝ} (hb : 0 < b)
    (G : (Fin D → ℤ) → Fin q → ℝ) {H : ℝ} (hH0 : 0 ≤ H)
    (hbound : ∀ᵐ p ∂ν, ∀ e, |G (cell b (Z p)) e| ≤ H)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (A : ℝ) (hA1 : 1 ≤ A)
    (hs0 : s 0 = 1) (hspos : ∀ i, 0 < s i)
    (hbs : ∀ i < L, b ≤ s i)
    (hA : ∀ i, i + 1 < L → s i ≤ A * s (i + 1))
    (hcount : ∀ i < L, ∀ n,
      ((positiveRowValues ν (fun p => cell (s i) (Z p))
        (fun p => G (cell b (Z p))) (s i) n).ncard : ℝ) ≤ H) :
    ∃ S : Set (Fin D → ℤ), MeasurableSet S ∧
      μ univ ≤ (∏ _i ∈ Finset.range L, ((4 : ENNReal) ^ D * (2 ^ D * (⌈H⌉₊ : ENNReal)))) *
        μ {p | cell b (Z p) ∈ S} ∧
      ∀ p, cell b (Z p) ∈ S → ∀ p', cell b (Z p') ∈ S →
        ‖G (cell b (Z p)) - G (cell b (Z p'))‖ ≤
          6 * (A + H) * (‖Z p - Z p'‖ + s (L - 1)) := by
  classical
  let f : X → Fin q → ℝ := fun p => G (cell b (Z p))
  have hlist (i : ℕ) (hi : i < L) (n : Fin D → ℤ) :=
    exists_original_row_list ν (fun p => cell (s i) (Z p)) f (hspos i) hbound n (hcount i hi n)
  let F : ℕ → (Fin D → ℤ) → Finset (Fin q → ℤ) := fun i n =>
    if hi : i < L then Classical.choose (hlist i hi n) else ∅
  have hFcard (i : ℕ) (hi : i < L) (n : Fin D → ℤ) : (F i n).card ≤ ⌈H⌉₊ := by
    simpa only [F, dite_eq_left hi] using (Classical.choose_spec (hlist i hi n)).1
  let record : ℕ → X → (Fin D → ℤ) × (Fin q → ℤ) :=
    fun i p => (cell (s i) (Z p), cell (s i) (f p))
  let E : Set X := {p | (∀ e, |f p e| ≤ H) ∧ p ∈ positiveRecordCore ν record}
  have hcore : ∀ᵐ p ∂μ, p ∈ positiveRecordCore ν record :=
    hμν.absolutelyContinuous.ae_le (ae_mem_positiveRecordCore ν record)
  have hbound' : ∀ᵐ p ∂μ, ∀ e, |f p e| ≤ H := hμν.absolutelyContinuous.ae_le hbound
  have hEae : ∀ᵐ p ∂μ, p ∈ E := by
    filter_upwards [hbound', hcore] with p hp hc
    exact ⟨hp, hc⟩
  have hEnull : μ Eᶜ = 0 := by
    have heq : Eᶜ = {p | ¬p ∈ E} := by ext p; simp only [mem_compl_iff, mem_ofPred_eq]
    rw [heq]
    exact ae_iff.mp hEae
  have hnorm : ∀ p ∈ E, ‖G (cell b (Z p))‖ ≤ H := by
    intro p hp
    apply (pi_norm_le_iff_of_nonneg hH0).2
    intro e
    simpa only [Real.norm_eq_abs] using hp.1 e
  have hFpoint : ∀ i < L, ∀ p ∈ E,
      cell (s i) (G (cell b (Z p))) ∈ F i (cell (s i) (Z p)) := by
    intro i hi p hp
    have hc := hp.2 i
    have hpos : ν {p' | cell (s i) (Z p') = cell (s i) (Z p) ∧
      cell (s i) (f p') = cell (s i) (f p)} ≠ 0 := by
      simpa only [record, Set.preimage, mem_singleton_iff, Prod.mk.injEq] using hc
    simpa only [F, dite_eq_left hi] using (Classical.choose_spec
      (hlist i hi (cell (s i) (Z p)))).2 _ hpos
  exact graph_whole_cell_selection μ Z hZ hb G E hEnull hH0 hnorm
    L hL s (fun _ => ⌈H⌉₊) A hA1 hs0 hspos hbs hA F hFcard hFpoint

end Submission.Obl.k4_scalar_graph_residual_discovery
