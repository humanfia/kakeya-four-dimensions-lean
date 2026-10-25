-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Orientation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Canonical

/-!
# Orientation normalization (no antipodal directions)

`sticky_branch` (and the separation of nets) needs a family without antipodal directions:
`1 ≤ ‖v i + v j‖`. A tube is unchanged when its segment is traversed backwards
(`tube_reorient`), so each tube can be oriented so that its dominant coordinate is positive.
Keeping the most popular dominant coordinate (at least a third of the family) removes all
antipodal pairs (`orientation_class`). This must be done before canonicalizing, since reversing a
tube swaps its left and right canonical ends.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- A tube is the same set when its segment is traversed backwards. -/
lemma tube_reorient (δ : ℝ) (x v : Sp) :
    Metric.thickening δ (segment ℝ x (x + v)) =
      Metric.thickening δ (segment ℝ (x + v) ((x + v) + (-v))) := by
  rw [show (x + v) + (-v) = x by abel, segment_symm]

/-- A unit vector has a coordinate of square at least `1/3`. -/
lemma exists_dominant {v : Sp} (hv : ‖v‖ = 1) : ∃ c : Fin 3, 1 / 3 ≤ (v c) ^ 2 := by
  by_contra h
  push Not at h
  have hsum : ‖v‖ ^ 2 = ∑ c, ‖v c‖ ^ 2 := EuclideanSpace.norm_sq_eq v
  have hlt : ∑ c, ‖v c‖ ^ 2 < ∑ _c : Fin 3, (1 / 3 : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro c _
    rw [Real.norm_eq_abs, sq_abs]
    exact h c
  rw [hv] at hsum
  simp only [Real.norm_eq_abs, sq_abs, one_pow] at hsum hlt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  linarith

/-- Orienting by the sign of coordinate `c`. -/
noncomputable def orientDir (c : Fin 3) (v : Sp) : Sp := if 0 ≤ v c then v else -v

noncomputable def orientStart (c : Fin 3) (x v : Sp) : Sp := if 0 ≤ v c then x else x + v

lemma orient_tube (δ : ℝ) (c : Fin 3) (x v : Sp) :
    Metric.thickening δ (segment ℝ (orientStart c x v) (orientStart c x v + orientDir c v)) =
      Metric.thickening δ (segment ℝ x (x + v)) := by
  unfold orientStart orientDir
  split_ifs
  · rfl
  · exact (tube_reorient δ x v).symm

lemma norm_orientDir (c : Fin 3) {v : Sp} (hv : ‖v‖ = 1) : ‖orientDir c v‖ = 1 := by
  unfold orientDir; split_ifs <;> simp [hv]

lemma orientDir_coord (c : Fin 3) (v : Sp) : (orientDir c v) c = |v c| := by
  unfold orientDir
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · rw [PiLp.neg_apply, abs_of_neg (lt_of_not_ge h)]

/-- Two unit vectors whose `c`-coordinates are both at least `1/√3` (after orientation) are not
antipodal: `1 ≤ ‖w + w'‖`. -/
lemma one_le_norm_add_of_dominant {w w' : Sp} {c : Fin 3} (hw : 1 / 3 ≤ (w c) ^ 2)
    (hw' : 1 / 3 ≤ (w' c) ^ 2) (hc : 0 ≤ w c) (hc' : 0 ≤ w' c) : 1 ≤ ‖w + w'‖ := by
  have h1 : 1 / 2 < w c := by nlinarith
  have h1' : 1 / 2 < w' c := by nlinarith
  calc (1 : ℝ) ≤ |w c + w' c| := by rw [abs_of_nonneg (by linarith)]; linarith
    _ = ‖(w + w') c‖ := by rw [PiLp.add_apply, Real.norm_eq_abs]
    _ ≤ ‖w + w'‖ := PiLp.norm_apply_le _ _

/-- Orientation normalization: for unit directions, some coordinate `c` and a third of the
family on which, after orienting each tube by the sign of its `c`-coordinate, no two directions
are antipodal. The tubes themselves are unchanged. -/
theorem orientation_class {n : ℕ} (v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (U : Finset (Fin n)) (hU : U.Nonempty) :
    ∃ c : Fin 3, ∃ S ⊆ U, S.Nonempty ∧ (U.card : ℝ) ≤ 3 * S.card ∧
      ∀ i ∈ S, ∀ j ∈ S, 1 ≤ ‖orientDir c (v i) + orientDir c (v j)‖ := by
  classical
  let dom : Fin n → Fin 3 := fun i => (exists_dominant (hv i)).choose
  have hdom : ∀ i, 1 / 3 ≤ (v i (dom i)) ^ 2 := fun i => (exists_dominant (hv i)).choose_spec
  have hmaps : ∀ i ∈ U, dom i ∈ (Finset.univ : Finset (Fin 3)) := fun _ _ => Finset.mem_univ _
  have hpos : (0 : ℝ) < (Finset.univ : Finset (Fin 3)).card := by simp
  obtain ⟨c, -, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps
    Finset.univ_nonempty (b := (U.card : ℝ) / (Finset.univ : Finset (Fin 3)).card) (by
      rw [nsmul_eq_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ hpos.ne'])
  set S := U.filter (fun i => dom i = c) with hSdef
  refine ⟨c, S, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · rw [← Finset.card_pos]
    have hUpos : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.2 hU
    have : (0 : ℝ) < (U.card : ℝ) / (Finset.univ : Finset (Fin 3)).card := div_pos hUpos hpos
    exact_mod_cast lt_of_lt_of_le this hc
  · have h3 : ((Finset.univ : Finset (Fin 3)).card : ℝ) = 3 := by simp
    rw [h3, div_le_iff₀ (by norm_num)] at hc
    linarith
  · intro i hi j hj
    have hci : dom i = c := (Finset.mem_filter.1 hi).2
    have hcj : dom j = c := (Finset.mem_filter.1 hj).2
    have hi3 := hdom i
    have hj3 := hdom j
    rw [hci] at hi3
    rw [hcj] at hj3
    apply one_le_norm_add_of_dominant (c := c)
    · rw [orientDir_coord, sq_abs]; exact hi3
    · rw [orientDir_coord, sq_abs]; exact hj3
    · rw [orientDir_coord]; exact abs_nonneg _
    · rw [orientDir_coord]; exact abs_nonneg _

/-- Selection without reorientation (usable after canonicalizing): the largest of the six
classes (dominant coordinate, sign) has no antipodal pairs and keeps a sixth of the family. -/
theorem antipode_free_class {n : ℕ} (v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (U : Finset (Fin n)) (hU : U.Nonempty) :
    ∃ S ⊆ U, S.Nonempty ∧ (U.card : ℝ) ≤ 6 * S.card ∧ ∀ i ∈ S, ∀ j ∈ S, 1 ≤ ‖v i + v j‖ := by
  classical
  let dom : Fin n → Fin 3 := fun i => (exists_dominant (hv i)).choose
  have hdom : ∀ i, 1 / 3 ≤ (v i (dom i)) ^ 2 := fun i => (exists_dominant (hv i)).choose_spec
  let key : Fin n → Fin 3 × Bool := fun i => (dom i, decide (0 ≤ v i (dom i)))
  have hmaps : ∀ i ∈ U, key i ∈ (Finset.univ : Finset (Fin 3 × Bool)) := fun _ _ =>
    Finset.mem_univ _
  have hcard6 : ((Finset.univ : Finset (Fin 3 × Bool)).card : ℝ) = 6 := by
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  have hpos : (0 : ℝ) < (Finset.univ : Finset (Fin 3 × Bool)).card := by rw [hcard6]; norm_num
  obtain ⟨y, -, hy⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps
    Finset.univ_nonempty (b := (U.card : ℝ) / (Finset.univ : Finset (Fin 3 × Bool)).card) (by
      rw [nsmul_eq_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ hpos.ne'])
  set S := U.filter (fun i => key i = y) with hSdef
  refine ⟨S, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · rw [← Finset.card_pos]
    have hUpos : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.2 hU
    have : (0 : ℝ) < (U.card : ℝ) / (Finset.univ : Finset (Fin 3 × Bool)).card := div_pos hUpos hpos
    exact_mod_cast lt_of_lt_of_le this hy
  · rw [hcard6, div_le_iff₀ (by norm_num)] at hy
    linarith
  · intro i hi j hj
    have hki : key i = y := (Finset.mem_filter.1 hi).2
    have hkj : key j = y := (Finset.mem_filter.1 hj).2
    have hkk : key i = key j := hki.trans hkj.symm
    have hdij : dom i = dom j := congrArg Prod.fst hkk
    have hsij : decide (0 ≤ v i (dom i)) = decide (0 ≤ v j (dom j)) := congrArg Prod.snd hkk
    set c := dom i with hc
    have hi3 := hdom i
    have hj3 := hdom j
    rw [← hdij] at hj3 hsij
    by_cases hpos' : 0 ≤ v i c
    · have hposj : 0 ≤ v j c := by
        have := hsij; simp only [hpos', decide_true] at this
        exact of_decide_eq_true this.symm
      exact one_le_norm_add_of_dominant hi3 hj3 hpos' hposj
    · have hnegj : ¬ 0 ≤ v j c := by
        have := hsij; simp only [hpos', decide_false] at this
        intro h; rw [decide_eq_true h] at this; exact Bool.false_ne_true this
      have h1 := one_le_norm_add_of_dominant (w := -v i) (w' := -v j) (c := c)
        (by rw [PiLp.neg_apply, neg_sq]; exact hi3) (by rw [PiLp.neg_apply, neg_sq]; exact hj3)
        (by rw [PiLp.neg_apply]; linarith [lt_of_not_ge hpos'])
        (by rw [PiLp.neg_apply]; linarith [lt_of_not_ge hnegj])
      rwa [← neg_add, norm_neg] at h1

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
