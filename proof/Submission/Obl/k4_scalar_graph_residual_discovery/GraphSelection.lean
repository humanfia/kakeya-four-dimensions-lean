/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file GraphSelection.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ParameterRefinement

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_density_extension

noncomputable section

def leftCorner {n : ℕ} (b : ℝ) (a : Fin n → ℤ) : Fin n → ℝ := fun j => (a j : ℝ) * b

def successorCells {n : ℕ} (a : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j => {a j, a j + 1}

theorem card_successorCells {n : ℕ} (a : Fin n → ℤ) : (successorCells a).card = 2 ^ n := by
  simp [successorCells, Fintype.card_piFinset]

theorem cell_mem_successorCells {n : ℕ} {b s : ℝ} (hb : 0 < b) (hbs : b ≤ s)
    (z : Fin n → ℝ) :
    cell s z ∈ successorCells (cell s (leftCorner b (cell b z))) := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact floorCompatible_coarse_mem hb hbs _ _ ⟨z j, rfl, rfl⟩

theorem norm_sub_leftCorner_le {n : ℕ} {b : ℝ} (hb : 0 < b) (z : Fin n → ℝ) :
    ‖z - leftCorner b (cell b z)‖ ≤ b := by
  have hc : cell b (leftCorner b (cell b z)) = cell b z := by
    ext j
    simp only [cell, leftCorner, mul_div_cancel_right₀ _ hb.ne', Int.floor_intCast]
  exact (norm_sub_lt_of_cell_eq hb hc.symm).le

/-- Apply common local choice on the discrete fine states themselves. Its
pullback therefore keeps or removes each original fine state as a whole. -/
theorem whole_state_common_choice {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    {D q : ℕ} (μ : Measure X) (record : X → Q) (hrecord : Measurable record)
    (Z : Q → Fin D → ℝ) (Y : Q → Fin q → ℝ)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a, (μ.map record) {a} ≠ 0 → ‖Y a‖ ≤ B)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (K : ℕ → ℕ) (A : ℝ) (hA1 : 1 ≤ A)
    (hs0 : s 0 = 1) (hspos : ∀ i, 0 < s i)
    (hA : ∀ i, i + 1 < L → s i ≤ A * s (i + 1))
    (hlist : ∀ i < L, ∀ n, ∃ F : Finset (Fin q → ℤ), F.card ≤ K i ∧
      ∀ a, (μ.map record) {a} ≠ 0 → cell (s i) (Z a) = n → cell (s i) (Y a) ∈ F) :
    ∃ S : Set Q, MeasurableSet S ∧
      (∀ a ∈ S, (μ.map record) {a} ≠ 0) ∧
      μ univ ≤ (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ D * K i)) * μ (record ⁻¹' S) ∧
      ∀ a ∈ S, ∀ a' ∈ S,
        ‖Y a - Y a'‖ ≤ 2 * (A + B) * (‖Z a - Z a'‖ + s (L - 1)) := by
  let Ω : Set Q := {a | (μ.map record) {a} ≠ 0}
  have hΩ : MeasurableSet Ω := (to_countable Ω).measurableSet
  have hae : ∀ᵐ a ∂μ.map record, a ∈ Ω := by
    simpa only [Ω, mem_ofPred_eq, id_eq, ofPred_eq_eq_singleton] using
      Submission.Obl.k4_two_velocity_row_list_completion.ae_record_mass_ne_zero (μ.map record) id
  have hfull : (μ.map record) Ω = (μ.map record) univ := by
    have hnull : (μ.map record) Ωᶜ = 0 := ae_iff.mp hae
    simpa only [hnull, add_zero] using measure_add_measure_compl (μ := μ.map record) hΩ
  obtain ⟨S, P, hS, hsub, hdesc, hmass, hcmp⟩ := common_local_choice
    (μ.map record) (fun _ : Q => ()) measurable_const Z (measurable_of_countable Z)
    Y (measurable_of_countable Y) Ω hΩ B hB0 (fun a ha => hB a ha)
    L hL s K A hA1 hs0 hspos hA (fun i hi _ n => by
      obtain ⟨F, hcard, hF⟩ := hlist i hi n
      exact ⟨F, hcard, fun a ha _ han => hF a ha han⟩)
  refine ⟨S, hS, hsub, ?_, fun a ha a' ha' => hcmp a ha a' ha' rfl⟩
  calc
    μ univ = (μ.map record) univ := by simp [Measure.map_apply hrecord]
    _ = (μ.map record) Ω := hfull.symm
    _ ≤ (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ D * K i)) * (μ.map record) S := by
      simpa only [preimage_const_of_mem (mem_singleton ()), inter_univ] using hmass ()
    _ = _ := by rw [Measure.map_apply hrecord hS]

/-- Coarse row lists select whole fine physical states, including states
that straddle a boundary of a coarser floor grid. No velocity law is
conditioned inside one of those states by this selection. -/
theorem graph_whole_cell_selection {X : Type*} [MeasurableSpace X] {D q : ℕ}
    (μ : Measure X) (Z : X → Fin D → ℝ) (hZ : Measurable Z)
    {b : ℝ} (hb : 0 < b) (G : (Fin D → ℤ) → Fin q → ℝ)
    (E : Set X) (hE : μ Eᶜ = 0)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ p ∈ E, ‖G (cell b (Z p))‖ ≤ B)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (K : ℕ → ℕ) (A : ℝ) (hA1 : 1 ≤ A)
    (hs0 : s 0 = 1) (hspos : ∀ i, 0 < s i)
    (hbs : ∀ i < L, b ≤ s i)
    (hA : ∀ i, i + 1 < L → s i ≤ A * s (i + 1))
    (F : ℕ → (Fin D → ℤ) → Finset (Fin q → ℤ))
    (hFcard : ∀ i < L, ∀ n, (F i n).card ≤ K i)
    (hF : ∀ i < L, ∀ p ∈ E, cell (s i) (G (cell b (Z p))) ∈ F i (cell (s i) (Z p))) :
    ∃ S : Set (Fin D → ℤ), MeasurableSet S ∧
      μ univ ≤ (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ D * (2 ^ D * K i))) *
        μ {p | cell b (Z p) ∈ S} ∧
      ∀ p, cell b (Z p) ∈ S → ∀ p', cell b (Z p') ∈ S →
        ‖G (cell b (Z p)) - G (cell b (Z p'))‖ ≤
          6 * (A + B) * (‖Z p - Z p'‖ + s (L - 1)) := by
  classical
  let record : X → Fin D → ℤ := fun p => cell b (Z p)
  have hrecord : Measurable record := measurable_cell b hZ
  have hwitness (a : Fin D → ℤ) (ha : (μ.map record) {a} ≠ 0) :
      ∃ p ∈ E, record p = a := by
    have hmass : μ (record ⁻¹' {a} ∩ E) ≠ 0 := by
      rw [measure_inter_conull hE]
      simpa only [Measure.map_apply hrecord (measurableSet_singleton a)] using ha
    obtain ⟨p, hp, hpE⟩ := nonempty_of_measure_ne_zero hmass
    exact ⟨p, hpE, hp⟩
  have hbound (a : Fin D → ℤ) (ha : (μ.map record) {a} ≠ 0) : ‖G a‖ ≤ B := by
    obtain ⟨p, hp, hpa⟩ := hwitness a ha
    simpa only [← hpa] using hB p hp
  have hlists (i : ℕ) (hi : i < L) (n : Fin D → ℤ) :
      ∃ F' : Finset (Fin q → ℤ), F'.card ≤ 2 ^ D * K i ∧
        ∀ a, (μ.map record) {a} ≠ 0 → cell (s i) (leftCorner b a) = n →
          cell (s i) (G a) ∈ F' := by
    refine ⟨(successorCells n).biUnion (F i), ?_, ?_⟩
    · calc
        _ ≤ ∑ n' ∈ successorCells n, (F i n').card := Finset.card_biUnion_le
        _ ≤ ∑ _n' ∈ successorCells n, K i :=
          Finset.sum_le_sum (fun n' _ => hFcard i hi n')
        _ = 2 ^ D * K i := by simp [card_successorCells]
    · intro a ha han
      obtain ⟨p, hp, hpa⟩ := hwitness a ha
      have hneighbor := cell_mem_successorCells hb (hbs i hi) (Z p)
      change cell (s i) (Z p) ∈ successorCells (cell (s i) (leftCorner b (record p))) at hneighbor
      rw [hpa, han] at hneighbor
      exact Finset.mem_biUnion.mpr ⟨cell (s i) (Z p), hneighbor, by
        simpa only [← hpa] using hF i hi p hp⟩
  obtain ⟨S, hS, hSpos, hmass, hcmp⟩ := whole_state_common_choice μ record hrecord
    (leftCorner b) G hB0 hbound L hL s (fun i => 2 ^ D * K i) A hA1 hs0 hspos hA hlists
  refine ⟨S, hS, ?_, ?_⟩
  · simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, record, Set.preimage] using hmass
  intro p hp p' hp'
  have h := hcmp (record p) hp (record p') hp'
  have hpos : ‖leftCorner b (record p) - leftCorner b (record p')‖ ≤ ‖Z p - Z p'‖ + 2 * b := by
    calc
      _ ≤ ‖leftCorner b (record p) - Z p‖ + ‖Z p - leftCorner b (record p')‖ := by
        simpa only [dist_eq_norm] using dist_triangle (leftCorner b (record p)) (Z p)
          (leftCorner b (record p'))
      _ ≤ ‖leftCorner b (record p) - Z p‖ + (‖Z p - Z p'‖ + ‖Z p' - leftCorner b (record p')‖) := by
        gcongr
        simpa only [dist_eq_norm] using dist_triangle (Z p) (Z p') (leftCorner b (record p'))
      _ ≤ b + (‖Z p - Z p'‖ + b) := by
        gcongr
        · simpa only [norm_sub_rev] using norm_sub_leftCorner_le hb (Z p)
        · exact norm_sub_leftCorner_le hb (Z p')
      _ = _ := by ring
  have hinner : ‖leftCorner b (record p) - leftCorner b (record p')‖ + s (L - 1) ≤
      3 * (‖Z p - Z p'‖ + s (L - 1)) := by
    have hbLast := hbs (L - 1) (by omega)
    linarith [norm_nonneg (Z p - Z p')]
  exact h.trans ((mul_le_mul_of_nonneg_left hinner (by linarith : 0 ≤ 2 * (A + B))).trans_eq
    (by ring))

end

end Submission.Obl.k4_scalar_graph_residual_discovery
