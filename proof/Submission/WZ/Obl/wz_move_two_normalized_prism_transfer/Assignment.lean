-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.Assignment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Unions
import Submission.WZ.Obl.wz_coarse_grains_assembly.Packing
import Submission.WZ.Obl.wz_rescaled_tube_estimate.WeightedSelection

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer

open Set MeasureTheory Metric

/-- Two coarse tubes conflict if they contain a common fine tube. -/
def CoverConflict {n N : ℕ} (δ ρ : ℝ) (x v : Fin n → V) (y w : Fin N → V)
    (k k' : Fin N) : Prop :=
  k = k' ∨ ∃ i, T δ (x i) (v i) ⊆ T ρ (y k) (w k) ∧
    T δ (x i) (v i) ⊆ T ρ (y k') (w k')

/-- A coarse tube sharing a whole unit fine tube lies in a fixed dilation of the first. -/
lemma conflict_tube_subset {n N : ℕ} {δ ρ : ℝ} {x v : Fin n → V} {y w : Fin N → V}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ k, ‖w k‖ = 1)
    {k k' : Fin N} (hconf : CoverConflict δ ρ x v y w k k') :
    T ρ (y k') (w k') ⊆ T (5 * ρ) (y k) (w k) := by
  rcases hconf with rfl | ⟨i, hi, hi'⟩
  · exact Metric.thickening_mono (by linarith) _
  · have hseg := Metric.self_subset_thickening hδ (segment ℝ (x i) (x i + v i))
    have hrev := WangZahlLot.Obl.wz_coarse_grains_assembly.pk_ends_subset (hv i) (hw k')
      (hi' (hseg (left_mem_segment ℝ _ _))) (hi' (hseg (right_mem_segment ℝ _ _)))
    intro p hp
    have hthick := Metric.thickening_subset_of_subset (4 * ρ) (hseg.trans hi) (hrev hp)
    have hh := Metric.thickening_thickening_subset (4 * ρ) ρ
      (segment ℝ (y k) (y k + w k)) hthick
    simpa only [show 4 * ρ + ρ = 5 * ρ by ring] using hh

/-- The conflict degree is bounded by an absolute constant, independent of the fine family. -/
theorem cover_conflict_degree {n N : ℕ} {δ ρ : ℝ} {x v : Fin n → V} {y w : Fin N → V}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ k, ‖w k‖ = 1) (hX : X ρ N y w) :
    ∀ k, ({k' | CoverConflict δ ρ x v y w k k'}.ncard : ℝ) ≤ 10 ^ 16 := by
  classical
  intro k
  let F := Finset.univ.filter (fun k' => CoverConflict δ ρ x v y w k k')
  have hvol : volume (T (5 * ρ) (y k) (w k)) ≤ O (32768 * ρ ^ 2) := by
    apply (WangZahlLot.Obl.wz_coarse_grains_assembly.pk_tube_vol_le
      (by positivity : 0 < 5 * ρ) (y k) (w k) (hw k)).trans
    apply ENNReal.ofReal_le_ofReal
    have hm := mul_le_mul_of_nonneg_right hρ1 (sq_nonneg ρ)
    nlinarith [sq_nonneg ρ]
  have hpack := WangZahlLot.Obl.wz_coarse_grains_assembly.pk_packing hρ y w F
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol) hw
    (fun k' hk' => conflict_tube_subset hδ hρ hv hw (Finset.mem_filter.mp hk').2) hX
  have hcard := WangZahlLot.Obl.wz_coarse_grains_assembly.pk_card_le hρ
    (by norm_num : (0 : ℝ) ≤ 32768) hpack hvol
  have he : {k' | CoverConflict δ ρ x v y w k k'} = (F : Set (Fin N)) := by
    ext k'
    simp [F]
  rw [he, Set.ncard_coe_finset]
  exact hcard.trans (by norm_num)

/-- One constant-cost selection of coarse tubes makes the fine-to-coarse assignment unique.
Whole prism fibres may be retained, so this selection does not change their pointwise broadness. -/
theorem coarse_assignment_selection {n N : ℕ} {δ ρ : ℝ} {x v : Fin n → V} {y w : Fin N → V}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ k, ‖w k‖ = 1) (hX : X ρ N y w)
    (weight : Fin N → ENNReal) :
    ∃ Q : Finset (Fin N),
      (∑ k, weight k) ≤ (10 ^ 16 : ENNReal) * ∑ k ∈ Q, weight k ∧
      ∀ i k k', k ∈ Q → k' ∈ Q →
        T δ (x i) (v i) ⊆ T ρ (y k) (w k) →
        T δ (x i) (v i) ⊆ T ρ (y k') (w k') → k = k' := by
  classical
  let R := CoverConflict δ ρ x v y w
  have hrefl : ∀ k, R k k := fun _ => Or.inl rfl
  have hsym : ∀ k k', R k k' → R k' k := by
    intro k k' h
    rcases h with h | ⟨i, hi, hi'⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨i, hi', hi⟩
  have hdegree : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      (Finset.univ.filter (R k)).card ≤ 10 ^ 16 := by
    intro k _
    have hd := cover_conflict_degree (x := x) hδ hρ hρ1 hv hw hX k
    have he : {k' | CoverConflict δ ρ x v y w k k'} =
        (Finset.univ.filter (R k) : Set (Fin N)) := by
      ext k'
      simp [R]
    rw [he, Set.ncard_coe_finset] at hd
    exact_mod_cast hd
  obtain ⟨Q, hQ, hsep, hmass⟩ :=
    WangZahlLot.Obl.wz_rescaled_tube_estimate.weighted_separated_subfamily R hrefl (fun {k k'} h => hsym k k' h)
      (10 ^ 16) (fun k => hdegree k (Finset.mem_univ k)) weight Finset.univ
  refine ⟨Q, by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmass, ?_⟩
  intro i k k' hk hk' hi hi'
  by_contra hne
  exact hsep k hk k' hk' hne (Or.inr ⟨i, hi, hi'⟩)


/-- Applied to the prism masses, coarse selection retains complete fibres and supplies
one assignment for all retained incidence pieces. -/
theorem assigned_prism_selection {n L N : ℕ} {δ ρ : ℝ} {x v : Fin n → V}
    {y w : Fin N → V} {γ : Fin L → Fin N} {W : Fin n → Fin L → Set V}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ k, ‖w k‖ = 1) (hX : X ρ N y w)
    (hW : ∀ i j, MeasurableSet (W i j))
    (hdisj : ∀ i j j', j ≠ j' → Disjoint (W i j) (W i j'))
    (hcont : ∀ i j, (W i j).Nonempty → T δ (x i) (v i) ⊆ T ρ (y (γ j)) (w (γ j)))
    (hpos : 0 < ∑ i, ∑ j, μ (W i j)) :
    ∃ (Q : Finset (Fin N)) (f : Fin n → Fin N), Q.Nonempty ∧
      (∑ i, ∑ j, μ (W i j)) ≤
        (10 ^ 16 : ENNReal) * ∑ k ∈ Q, ∑ i, μ (pieceFibre W γ k i) ∧
      (∀ i, f i ∈ Q) ∧
      (∀ i j, γ j ∈ Q → (W i j).Nonempty → f i = γ j) ∧
      (∀ i k k', k ∈ Q → k' ∈ Q →
        T δ (x i) (v i) ⊆ T ρ (y k) (w k) →
        T δ (x i) (v i) ⊆ T ρ (y k') (w k') → k = k') := by
  classical
  obtain ⟨Q, hmass, huniq⟩ := coarse_assignment_selection (x := x) hδ hρ hρ1 hv hw hX
    (fun k => ∑ i, μ (pieceFibre W γ k i))
  rw [pieceFibre_mass W γ hW hdisj] at hmass
  have hQ : Q.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, mul_zero] at hmass
    exact (not_le_of_gt hpos) hmass
  obtain ⟨k₀, hk₀⟩ := hQ
  let f (i : Fin n) : Fin N :=
    if h : ∃ k ∈ Q, T δ (x i) (v i) ⊆ T ρ (y k) (w k) then h.choose else k₀
  have hfQ : ∀ i, f i ∈ Q := by
    intro i
    dsimp only [f]
    split_ifs with h
    · exact h.choose_spec.1
    · exact hk₀
  refine ⟨Q, f, ⟨k₀, hk₀⟩, hmass, hfQ, ?_, huniq⟩
  intro i j hj hne
  have hex : ∃ k ∈ Q, T δ (x i) (v i) ⊆ T ρ (y k) (w k) :=
    ⟨γ j, hj, hcont i j hne⟩
  have hfcont : T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i)) := by
    dsimp only [f]
    rw [dite_eq_left hex]
    exact hex.choose_spec.2
  exact huniq i (f i) (γ j) (hfQ i) hj hfcont (hcont i j hne)

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
