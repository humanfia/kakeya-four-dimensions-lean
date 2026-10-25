/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldResidualSelection.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldResidualScale
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldTimeRow

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

/-- The actual retained event after residual common choice, together with
its time row. Its mass bound is in the unchanged original incidence law. -/
structure ResidualWorldSelection (μ : Measure ScalarIncidence) (R : Set ScalarIncidence)
    (ρ b : ℝ) (q : Fin 5 → ℤ) (Hc Krow Hrow A ζ : ℝ) (n : ℕ) (K : ℕ → ℕ)
    (G : (Fin 3 → ℤ) → Fin 2 → ℝ) where
  F : ℝ → ℝ
  event : Set ScalarIncidence
  measurable_event : MeasurableSet event
  sub : event ⊆ R ∩ {p | cell ρ p.1.2 = q}
  mass : μ (R ∩ {p | cell ρ p.1.2 = q}) ≤
    (∏ i ∈ Finset.range n, ((4 : ℝ≥0∞) ^ 3 * K i)) * μ event
  measurable_F : Measurable F
  row_bound : ∀ t, |F t| ≤ Hrow
  row_close : ∀ p ∈ event, |G (cell b (scalarPosition p)) 1 - F p.2| ≤
    4 * worldRowConstant Hc Krow ^ 2 * ρ
  row_cmp : ∀ p ∈ event, ∀ p' ∈ event, |F p.2 - F p'.2| ≤
    12 * worldRowConstant Hc Krow ^ 2 * (|p.2 - p'.2| + ζ)
  residual_cmp : ∀ p ∈ event, ∀ p' ∈ event,
    |residual ρ q F p.1 p.2 - residual ρ q F p'.1 p'.2| ≤
      6 * (A + Hrow + 5) * (‖position ρ q p - position ρ q p'‖ + ζ)

noncomputable section

/-- Primitive original floors produce the time row, all raw residual
lists, and the final whole-state residual comparison. The selected event
is a measurable subset of the original coefficient world. Global filling
and original prior caps may consequently still be used on it by monotonicity. -/
theorem exists_residual_world_selection
    (μ : Measure ScalarIncidence) [IsFiniteMeasure μ]
    (θ : Measure ScalarLine) (π : Measure ℝ) [IsFiniteMeasure π]
    {R E : Set ScalarIncidence} (hR : MeasurableSet R) (hRE : R ⊆ E)
    {ρ b H Hc Krow Hrow A ζ ε : ℝ}
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hb : 0 < b) (hH : 1 ≤ H)
    (hHc : 1 ≤ Hc) (hKrow : 0 ≤ Krow) (hHrow : 0 ≤ Hrow)
    (hA : 1 ≤ A) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hρζ : ρ ≤ ζ)
    (hdiam : (1 + 3 * Hc) * b / ρ ≤ ζ)
    (herror : 4 * worldRowConstant Hc Krow ^ 2 * ρ + ε / ρ + 2 * Hc * b / ρ ≤ ζ)
    (q : Fin 5 → ℤ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hcoeff : ∀ p ∈ R, ∀ e, |p.1.2 e| ≤ H)
    (htime : ∀ p ∈ R, p.2 ∈ Icc (0 : ℝ) 1)
    (hcenter : ∀ e, |(center ρ q).2 e| ≤ Hc)
    (hbound : ∀ p ∈ R, cell ρ p.1.2 = q → |G (cell b (scalarPosition p)) 1| ≤ Hrow)
    (hcompare : ∀ p ∈ R, cell ρ p.1.2 = q → ∀ p' ∈ R, cell ρ p'.1.2 = q →
      |G (cell b (scalarPosition p)) 1 - G (cell b (scalarPosition p')) 1| ≤
        Krow * (‖scalarPosition p - scalarPosition p'‖ + ρ))
    (hgraph : ∀ p ∈ R,
      |p.1.2 3 + 2 * p.2 * p.1.2 4 - G (cell b (scalarPosition p)) 0 -
        G (cell b (scalarPosition p)) 1 * p.1.2 1| ≤ ε)
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ → ℝ) (K : ℕ → ℕ)
    (hs₀ : s 0 = 1) (hs : ∀ i, 0 < s i)
    (hζs : ∀ i < n, ζ ≤ s i)
    (hratio : ∀ i, i + 1 < n → s i ≤ A * s (i + 1)) (hlast : s (n - 1) = ζ)
    (raw : (i : Fin n) → OriginalResidualScale μ θ π R E ρ b (s i) H q)
    (hbudget : ∀ i : Fin n,
      (raw i).listBound Hrow (12 * worldRowConstant Hc Krow ^ 2) ≤ (K i : ℝ)) :
    Nonempty (ResidualWorldSelection μ R ρ b q Hc Krow Hrow A ζ n K G) := by
  classical
  let Rq := R ∩ {p : ScalarIncidence | cell ρ p.1.2 = q}
  have hRq : MeasurableSet Rq := hR.inter (measurable_fst (measurableSet_block ρ q))
  obtain ⟨F, hF, hFbound, hFclose, hFcmp⟩ := exists_world_time_row (E := Rq) hρ hHc hKrow hHrow q G
    (fun p hp => hp.2) (fun p hp => htime p hp.1) hcenter
    (fun p hp => hbound p hp.1 hp.2)
    (fun p hp p' hp' => hcompare p hp.1 hp.2 p' hp'.1 hp'.2)
  have hvar (p : ScalarIncidence) (hp : p ∈ Rq) (p' : ScalarIncidence) (hp' : p' ∈ Rq) :
      |F p.2 - F p'.2| ≤ 12 * worldRowConstant Hc Krow ^ 2 * (|p.2 - p'.2| + ζ) :=
    (hFcmp p hp p' hp').trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hρζ) (by positivity))
  have hlists (i : ℕ) (hi : i < n) (z : Fin 3 → ℤ) : ∃ Q : Finset ℤ,
      (Q.card : ℝ) ≤ (K i : ℝ) ∧ ∀ p ∈ Rq, cell (s i) (position ρ q p) = z →
        ⌊stateResidual ρ b q G (cell b (scalarPosition p)) / s i⌋ ∈ Q := by
    obtain ⟨Q, hQcard, hQmem⟩ := (raw ⟨i, hi⟩).lists hR hRE hρ hb (hs i) hH hcoeff
      (by
        intro p hp
        rw [abs_of_nonneg (htime p hp).1]
        exact (htime p hp).2)
      F G hHrow (by positivity) (hζs i hi) herror (hcenter 4)
      (fun p _ _ => hFbound p.2)
      (fun p hp hq p' hp' hq' => hvar p ⟨hp, hq⟩ p' ⟨hp', hq'⟩)
      (fun p hp hq => hFclose p ⟨hp, hq⟩) hgraph z
    exact ⟨Q, hQcard.trans (hbudget ⟨i, hi⟩), fun p hp hz => hQmem p hp.1 hp.2 hz⟩
  let κ := μ.restrict Rq
  have hsupp : κ Rqᶜ = 0 := by
    rw [Measure.restrict_apply hRq.compl]
    simp
  obtain ⟨S, hS, hmass, hresidual⟩ := original_state_choice_of_cellwise_residual_lists κ Rq
    hsupp hρ hρ₁ hb hζ hζ₁ hHrow hHc q F G
    (fun p hp => hp.2) (fun p hp => htime p hp.1) (fun p _ => hFbound p.2)
    hcenter hFclose (fun p hp => hgraph p hp.1) hdiam herror n hn s K A hA hs₀ hs hratio hlast hlists
  let V := {p : ScalarIncidence | cell b (scalarPosition p) ∈ S}
  have hV : MeasurableSet V := (measurable_cell b measurable_scalarPosition) hS
  let R₁ := Rq ∩ V
  have hm₀ : κ univ = μ Rq := by simp only [κ, Measure.restrict_apply_univ]
  have hm₁ : κ V = μ R₁ := by rw [Measure.restrict_apply hV, inter_comm]
  rw [hm₀, hm₁] at hmass
  refine ⟨{
    F := F
    event := R₁
    measurable_event := hRq.inter hV
    sub := inter_subset_left
    mass := hmass
    measurable_F := hF
    row_bound := hFbound
    row_close := fun p hp => hFclose p hp.1
    row_cmp := fun p hp p' hp' => hvar p hp.1 p' hp'.1
    residual_cmp := ?_
  }⟩
  intro p hp p' hp'
  exact hresidual p hp.1 hp.2 p' hp'.1 hp'.2

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
