-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.StripCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.StripCode

/-!
# Separated strips through one point and through two points

Among `r`-separated strip labels with points of norm `≤ 4`, at most
`1536 / r + 48` strips contain a given point of norm `≤ 4`, and at most
`1536 / d + 24` contain two given points at distance `d ≥ 4 r`.

Ported from session x0394 (o141, commit d684c60).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- The first coordinate axis. -/
noncomputable def ax0 : E2 := !₂[1, 0]
/-- The second coordinate axis. -/
noncomputable def ax1 : E2 := !₂[0, 1]

lemma norm_ax0 : ‖ax0‖ = 1 := by
  rw [EuclideanSpace.norm_eq]; simp [ax0]

lemma norm_ax1 : ‖ax1‖ = 1 := by
  rw [EuclideanSpace.norm_eq]; simp [ax1]

lemma inner_ax0 (e : E2) : inner ℝ e ax0 = e 0 := by
  rw [inner_coords]; simp [ax0]

lemma inner_ax1 (e : E2) : inner ℝ e ax1 = e 1 := by
  rw [inner_coords]; simp [ax1]

/-- One-point bound. -/
lemma card_strips_through_point {r : ℝ} (hr : 0 < r) (J : Finset (E2 × E2))
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1) (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    {y : E2} (hy : ‖y‖ ≤ 4) :
    ((J.filter (fun j => |inner ℝ (y - j.1) j.2| < r)).card : ℝ) ≤ 1536 / r + 48 := by
  classical
  set F := J.filter (fun j => |inner ℝ (y - j.1) j.2| < r) with hF
  set F0 := F.filter (fun j => (j.2 0) ^ 2 ≤ 1 / 2) with hF0
  set F1 := F.filter (fun j => ¬ (j.2 0) ^ 2 ≤ 1 / 2) with hF1
  have hsplit : F.card = F0.card + F1.card := (Finset.card_filter_add_card_filter_not _).symm
  have hsepF : ∀ G ⊆ F, (G : Set (E2 × E2)).Pairwise (StripSep r) := fun G hG =>
    hsep.mono (fun x hx => (Finset.mem_filter.mp (hG hx)).1)
  have hmemF : ∀ j ∈ F, ‖j.2‖ = 1 ∧ ‖y - j.1‖ ≤ 8 ∧ |inner ℝ (y - j.1) j.2| < r := by
    intro j hj
    obtain ⟨hjJ, hjr⟩ := Finset.mem_filter.mp hj
    exact ⟨(hJ j hjJ).2, norm_le_eight_of_norm_le_four hy (hJ j hjJ).1, hjr⟩
  have hb0 : (F0.card : ℝ) ≤ 12 * (64 * 1 / r + 2) := by
    apply card_le_of_frame norm_ax0 hr zero_le_one F0 (hsepF F0 (Finset.filter_subset _ _))
    intro j hj
    obtain ⟨hjF, hj0⟩ := Finset.mem_filter.mp hj
    obtain ⟨he, hy8, hjr⟩ := hmemF j hjF
    refine ⟨he, hy8, by rw [inner_ax0]; exact hj0, ?_, hjr⟩
    calc |inner ℝ j.2 ax0| ≤ ‖j.2‖ * ‖ax0‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [he, norm_ax0]; norm_num
  have hb1 : (F1.card : ℝ) ≤ 12 * (64 * 1 / r + 2) := by
    apply card_le_of_frame norm_ax1 hr zero_le_one F1 (hsepF F1 (Finset.filter_subset _ _))
    intro j hj
    obtain ⟨hjF, hj0⟩ := Finset.mem_filter.mp hj
    obtain ⟨he, hy8, hjr⟩ := hmemF j hjF
    refine ⟨he, hy8, ?_, ?_, hjr⟩
    · rw [inner_ax1]
      have h := norm_sq_coords j.2
      rw [he] at h
      replace hj0 := not_le.mp hj0
      nlinarith
    · calc |inner ℝ j.2 ax1| ≤ ‖j.2‖ * ‖ax1‖ := abs_real_inner_le_norm _ _
        _ = 1 := by rw [he, norm_ax1]; norm_num
  have : (F.card : ℝ) = F0.card + F1.card := by exact_mod_cast hsplit
  rw [this]
  have : 12 * (64 * 1 / r + 2) + 12 * (64 * 1 / r + 2) = 1536 / r + 48 := by ring
  linarith

/-- Two-point bound. -/
lemma card_strips_through_two_points {r : ℝ} (hr : 0 < r) (J : Finset (E2 × E2))
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1) (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    {y y' : E2} (hy : ‖y‖ ≤ 4) (hd : 4 * r ≤ ‖y - y'‖) :
    ((J.filter (fun j => |inner ℝ (y - j.1) j.2| < r ∧ |inner ℝ (y' - j.1) j.2| < r)).card : ℝ) ≤
      1536 / ‖y - y'‖ + 24 := by
  classical
  set d := ‖y - y'‖ with hddef
  have hd0 : 0 < d := by linarith
  set u : E2 := d⁻¹ • (y - y') with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, norm_norm, ← hddef]; field_simp
  set F := J.filter (fun j => |inner ℝ (y - j.1) j.2| < r ∧ |inner ℝ (y' - j.1) j.2| < r)
  have hbound := card_le_of_frame (y := y) (amax := 2 * r / d) hu hr (by positivity) F
    (hsep.mono (fun x hx => (Finset.mem_filter.mp hx).1)) ?_
  · have : 12 * (64 * (2 * r / d) / r + 2) = 1536 / d + 24 := by field_simp; ring
    linarith
  intro j hj
  obtain ⟨hjJ, h1, h2⟩ := Finset.mem_filter.mp hj
  have he := (hJ j hjJ).2
  have hinner : inner ℝ j.2 u = d⁻¹ * (inner ℝ (y - j.1) j.2 - inner ℝ (y' - j.1) j.2) := by
    rw [hudef, inner_smul_right, real_inner_comm]
    congr 1
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm j.2 y, real_inner_comm j.2 y']
    ring
  have habs : |inner ℝ j.2 u| ≤ 2 * r / d := by
    rw [hinner, abs_mul, abs_inv, abs_of_pos hd0]
    have : |inner ℝ (y - j.1) j.2 - inner ℝ (y' - j.1) j.2| ≤ 2 * r := by
      have := abs_sub (inner ℝ (y - j.1) j.2) (inner ℝ (y' - j.1) j.2)
      linarith
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right this hd0.le
  have hsmall : 2 * r / d ≤ 1 / 2 := by
    rw [div_le_iff₀ hd0]; linarith
  refine ⟨he, norm_le_eight_of_norm_le_four hy (hJ j hjJ).1, ?_, habs, h1⟩
  have : |inner ℝ j.2 u| ≤ 1 / 2 := habs.trans hsmall
  have h0 : 0 ≤ |inner ℝ j.2 u| := abs_nonneg _
  rw [← sq_abs]
  nlinarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
