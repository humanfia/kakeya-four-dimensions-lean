-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_cell_weighted_cover.Grid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Basic

/-!
# Selecting points along a line (a discrete Fubini argument)

Let `Y'` lie in `P₀ ∩ B(x, b)`, `P₀ = prism a b c₀ u₀`, and let `(u₀ 0, w, v)` be an orthonormal
frame. Grid by `⌊⟪w, q - x⟫ / a⌋` and `⌊⟪v, q - x⟫ / Δ⌋`: each cell of the grid meets `P₀` in a
box of volume `≤ 8 · a · (a/2) · (Δ/2) = 2 a² Δ` (`volume_le_of_coords`), and there are at most
`2 ⌈b/a⌉ + 1 ≤ 5 b / a` rows. Pigeonhole a row, keep the cells of the row of one parity
(at least half), and pick a point of `Y'` in each kept cell.
-/

namespace WangZahlLot.Obl.wz_transverse_cell_weighted_cover

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- Two reals in the same cell of the grid of step `a` differ by less than `a`. -/
private theorem grid_sub_lt_of_floor_eq {s t a : ℝ} (ha : 0 < a) (h : ⌊s / a⌋ = ⌊t / a⌋) :
    |s - t| < a := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos ha, div_lt_one ha] at h1
  exact h1

/-- An even nonzero integer has absolute value at least two. -/
private theorem grid_two_le_abs {d : ℤ} (he : Even d) (hd : d ≠ 0) : (2 : ℝ) ≤ |(d : ℝ)| := by
  obtain ⟨k, rfl⟩ := he
  have hk : k ≠ 0 := by omega
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  push_cast
  rw [show (k : ℝ) + k = 2 * k by ring, abs_mul, abs_two]
  linarith

/-- Reals in the cells `j`, `j'` of the grid of step `Δ`, with `|j - j'| ≥ 2`, are at least
`|j - j'| Δ / 2` apart. -/
private theorem grid_sep_of_floor {s t Δ : ℝ} (hΔ : 0 < Δ) {j j' : ℤ} (hs : ⌊s / Δ⌋ = j)
    (ht : ⌊t / Δ⌋ = j') (h2 : 2 ≤ |(j : ℝ) - j'|) : |(j : ℝ) - j'| * Δ / 2 ≤ |s - t| := by
  obtain ⟨hs1, hs2⟩ := Int.floor_eq_iff.mp hs
  obtain ⟨ht1, ht2⟩ := Int.floor_eq_iff.mp ht
  rw [le_div_iff₀ hΔ] at hs1 ht1
  rw [div_lt_iff₀ hΔ] at hs2 ht2
  rcases le_abs.mp h2 with h | h
  · rw [abs_of_pos (by linarith : (0 : ℝ) < j - j')]
    refine le_trans ?_ (le_abs_self _)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ j - j' - 2) hΔ.le]
  · rw [abs_of_neg (by linarith : (j : ℝ) - j' < 0), abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ j' - j - 2) hΔ.le]

/-- One parity class of a finite set of integers has at least half of its elements. -/
private theorem grid_parity_subset (s : Finset ℤ) :
    ∃ J ⊆ s, s.card ≤ 2 * J.card ∧ ∀ j ∈ J, ∀ j' ∈ J, Even (j - j') := by
  have hsum := Finset.card_filter_add_card_filter_not (s := s) (fun j : ℤ => Even j)
  by_cases h : (s.filter (fun j : ℤ => ¬ Even j)).card ≤ (s.filter (fun j : ℤ => Even j)).card
  · refine ⟨s.filter (fun j : ℤ => Even j), Finset.filter_subset _ _, by omega, ?_⟩
    intro j hj j' hj'
    rw [Finset.mem_filter] at hj hj'
    exact Int.even_sub.mpr (iff_of_true hj.2 hj'.2)
  · refine ⟨s.filter (fun j : ℤ => ¬ Even j), Finset.filter_subset _ _, by omega, ?_⟩
    intro j hj j' hj'
    rw [Finset.mem_filter] at hj hj'
    exact Int.even_sub.mpr (iff_of_false hj.2 hj'.2)

/-- A floor of a quotient of a number of absolute value `< b` lies in `[-⌈b/c⌉, ⌈b/c⌉]`. -/
private theorem grid_floor_mem {t b c : ℝ} (hc : 0 < c) (ht : |t| < b) :
    ⌊t / c⌋ ∈ Finset.Icc (-⌈b / c⌉) ⌈b / c⌉ := by
  rw [Finset.mem_Icc]
  obtain ⟨ht1, ht2⟩ := abs_lt.mp ht
  have hc1 : -b / c < t / c := (div_lt_div_iff_of_pos_right hc).mpr ht1
  have hc2 : t / c < b / c := (div_lt_div_iff_of_pos_right hc).mpr ht2
  have hce := Int.le_ceil (b / c)
  have hfl := Int.floor_le (t / c)
  rw [neg_div] at hc1
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith
  · have : ((⌊t / c⌋ : ℤ) : ℝ) ≤ ((⌈b / c⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this

theorem grid_selection {a b Δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hΔ : a ≤ Δ)
    {u₀ : Fin 3 → Space} (hu₀ : Orthonormal ℝ u₀) {c₀ x w v : Space}
    (hframe : Orthonormal ℝ ![u₀ 0, w, v]) (Y' : Set Space)
    (hY' : Y' ⊆ prism a b c₀ u₀ ∩ ball x b) :
    ∃ (J : Finset ℤ) (y : ℤ → Space), (∀ j ∈ J, y j ∈ Y') ∧
      volume Y' ≤ ENNReal.ofReal (20 * a * b * Δ * J.card) ∧
      (∀ j ∈ J, ∀ j' ∈ J, j ≠ j' →
        |inner ℝ w (y j - y j')| < a ∧
        (|(j : ℝ) - j'|) * Δ / 2 ≤ |inner ℝ v (y j - y j')| ∧ 2 ≤ |(j : ℝ) - j'|) ∧
      (∀ j ∈ J, |(j : ℝ)| ≤ b / Δ + 1) := by
  classical
  have hΔ0 : 0 < Δ := ha.trans_le hΔ
  have hb0 : 0 < b := ha.trans_le hab
  -- `w` and `v` are unit vectors
  have hw1 : ‖w‖ = 1 := by simpa using hframe.1 1
  have hv1 : ‖v‖ = 1 := by simpa using hframe.1 2
  have hww : inner ℝ w w = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hw1]; norm_num
  have hvv : inner ℝ v v = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv1]; norm_num
  -- the coordinates along `w` and `v`, measured from `x`
  obtain ⟨ζw, hζw⟩ : ∃ f : Space → ℝ, ∀ q, f q = inner ℝ w (q - x) := ⟨_, fun _ => rfl⟩
  obtain ⟨ζv, hζv⟩ : ∃ f : Space → ℝ, ∀ q, f q = inner ℝ v (q - x) := ⟨_, fun _ => rfl⟩
  have hζb : ∀ q ∈ Y', |ζw q| < b ∧ |ζv q| < b := by
    intro q hq
    have hqb : ‖q - x‖ < b := by
      have := (hY' hq).2
      rwa [mem_ball, dist_eq_norm] at this
    refine ⟨?_, ?_⟩
    · calc |ζw q| ≤ ‖w‖ * ‖q - x‖ := by rw [hζw]; exact abs_real_inner_le_norm _ _
        _ < b := by rw [hw1, one_mul]; exact hqb
    · calc |ζv q| ≤ ‖v‖ * ‖q - x‖ := by rw [hζv]; exact abs_real_inner_le_norm _ _
        _ < b := by rw [hv1, one_mul]; exact hqb
  -- the grid
  obtain ⟨Nw, hNw⟩ : ∃ N : ℤ, N = ⌈b / a⌉ := ⟨_, rfl⟩
  obtain ⟨Nv, hNv⟩ : ∃ N : ℤ, N = ⌈b / Δ⌉ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ → ℤ → Set Space, ∀ jw jv,
      C jw jv = {q | q ∈ Y' ∧ ⌊ζw q / a⌋ = jw ∧ ⌊ζv q / Δ⌋ = jv} := ⟨_, fun _ _ => rfl⟩
  obtain ⟨row, hrow⟩ : ∃ r : ℤ → Finset ℤ, ∀ jw, r jw = (Finset.Icc (-Nv) Nv).filter
      (fun jv => ∃ q ∈ Y', ⌊ζw q / a⌋ = jw ∧ ⌊ζv q / Δ⌋ = jv) := ⟨_, fun _ => rfl⟩
  have hmem : ∀ jw jv, jv ∈ row jw ↔
      jv ∈ Finset.Icc (-Nv) Nv ∧ ∃ q ∈ Y', ⌊ζw q / a⌋ = jw ∧ ⌊ζv q / Δ⌋ = jv := by
    intro jw jv
    rw [hrow, Finset.mem_filter]
  -- each cell of the grid has volume at most `2 a² Δ`
  have hcell : ∀ jw jv : ℤ, volume (C jw jv) ≤ ENNReal.ofReal (2 * a * a * Δ) := by
    intro jw jv
    have key := volume_le_of_coords hframe
      ![c₀, x + (((jw : ℝ) + 1 / 2) * a) • w, x + (((jv : ℝ) + 1 / 2) * Δ) • v]
      ![a, a / 2, Δ / 2] (C jw jv) ?_
    · calc volume (C jw jv) ≤ _ := key
        _ = ENNReal.ofReal (2 * a * a * Δ) := by
          congr 1
          simp
          ring
    · intro q hq k
      rw [hC] at hq
      obtain ⟨hqY, hqw, hqv⟩ := hq
      fin_cases k
      · have := (hY' hqY).1
        simp only [prism, mem_ofPred_eq] at this
        simpa using this.1
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [sub_add_eq_sub_sub, inner_sub_right, inner_smul_right, hww, mul_one, ← hζw]
        obtain ⟨h1, h2⟩ := Int.floor_eq_iff.mp hqw
        rw [le_div_iff₀ ha] at h1
        rw [div_lt_iff₀ ha] at h2
        rw [abs_le]
        constructor <;> nlinarith
      · simp
        rw [sub_add_eq_sub_sub, inner_sub_right, inner_smul_right, hvv, mul_one, ← hζv]
        obtain ⟨h1, h2⟩ := Int.floor_eq_iff.mp hqv
        rw [le_div_iff₀ hΔ0] at h1
        rw [div_lt_iff₀ hΔ0] at h2
        rw [abs_le]
        constructor <;> nlinarith
  -- the cells of the grid meeting `Y'` cover `Y'`
  have hcover : Y' ⊆ ⋃ jw ∈ Finset.Icc (-Nw) Nw, ⋃ jv ∈ row jw, C jw jv := by
    intro q hq
    have hb := hζb q hq
    simp only [Set.mem_iUnion]
    refine ⟨⌊ζw q / a⌋, hNw ▸ grid_floor_mem ha hb.1, ⌊ζv q / Δ⌋, ?_, ?_⟩
    · rw [hmem]
      exact ⟨hNv ▸ grid_floor_mem hΔ0 hb.2, q, hq, rfl, rfl⟩
    · rw [hC]
      exact ⟨hq, rfl, rfl⟩
  -- pigeonhole a row, and keep the cells of one parity
  have hWne : (Finset.Icc (-Nw) Nw).Nonempty := by
    have : 0 ≤ Nw := by rw [hNw]; exact Int.ceil_nonneg (div_nonneg hb0.le ha.le)
    exact Finset.nonempty_Icc.mpr (by omega)
  obtain ⟨jm, -, hjm⟩ :=
    Finset.exists_max_image (Finset.Icc (-Nw) Nw) (fun jw => (row jw).card) hWne
  obtain ⟨J, hJsub, hJcard, hJpar⟩ := grid_parity_subset (row jm)
  -- a point of `Y'` in each kept cell
  have hpick : ∀ j : ℤ, ∃ q : Space,
      j ∈ row jm → q ∈ Y' ∧ ⌊ζw q / a⌋ = jm ∧ ⌊ζv q / Δ⌋ = j := by
    intro j
    by_cases hj : j ∈ row jm
    · obtain ⟨-, q, hq, h1, h2⟩ := (hmem jm j).mp hj
      exact ⟨q, fun _ => ⟨hq, h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose y hy using hpick
  refine ⟨J, y, fun j hj => (hy j (hJsub hj)).1, ?_, ?_, ?_⟩
  · -- the volume bound
    have hWcard : ((Finset.Icc (-Nw) Nw).card : ℝ) * a ≤ 5 * b := by
      have hNw0 : 0 ≤ Nw := by rw [hNw]; exact Int.ceil_nonneg (div_nonneg hb0.le ha.le)
      have hc : ((Finset.Icc (-Nw) Nw).card : ℤ) = 2 * Nw + 1 := by
        rw [Int.card_Icc]; omega
      have hc' : ((Finset.Icc (-Nw) Nw).card : ℝ) = 2 * (Nw : ℝ) + 1 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hc
        push_cast at this
        exact this
      have hN : (Nw : ℝ) < b / a + 1 := by rw [hNw]; exact Int.ceil_lt_add_one _
      have hba : b / a * a = b := div_mul_cancel₀ b ha.ne'
      rw [hc']
      nlinarith
    calc volume Y' ≤ volume (⋃ jw ∈ Finset.Icc (-Nw) Nw, ⋃ jv ∈ row jw, C jw jv) :=
          measure_mono hcover
      _ ≤ ∑ jw ∈ Finset.Icc (-Nw) Nw, volume (⋃ jv ∈ row jw, C jw jv) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ jw ∈ Finset.Icc (-Nw) Nw, ∑ jv ∈ row jw, volume (C jw jv) :=
          Finset.sum_le_sum fun jw _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ jw ∈ Finset.Icc (-Nw) Nw, ∑ jv ∈ row jw, ENNReal.ofReal (2 * a * a * Δ) :=
          Finset.sum_le_sum fun jw _ => Finset.sum_le_sum fun jv _ => hcell jw jv
      _ = ∑ jw ∈ Finset.Icc (-Nw) Nw, ((row jw).card : ℝ≥0∞) * ENNReal.ofReal (2 * a * a * Δ) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ jw ∈ Finset.Icc (-Nw) Nw, ((row jm).card : ℝ≥0∞) * ENNReal.ofReal (2 * a * a * Δ) := by
          refine Finset.sum_le_sum fun jw hjw => mul_le_mul_of_nonneg_right ?_ zero_le
          exact_mod_cast hjm jw hjw
      _ = ((Finset.Icc (-Nw) Nw).card : ℝ≥0∞) *
            (((row jm).card : ℝ≥0∞) * ENNReal.ofReal (2 * a * a * Δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (((Finset.Icc (-Nw) Nw).card : ℝ) *
            (((row jm).card : ℝ) * (2 * a * a * Δ))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (20 * a * b * Δ * J.card) := by
          apply ENNReal.ofReal_le_ofReal
          have hRJ : ((row jm).card : ℝ) ≤ 2 * (J.card : ℝ) := by exact_mod_cast hJcard
          have h1 : ((Finset.Icc (-Nw) Nw).card : ℝ) * a * ((row jm).card : ℝ) ≤
              (5 * b) * (2 * (J.card : ℝ)) :=
            mul_le_mul hWcard hRJ (Nat.cast_nonneg _) (by linarith)
          have h2 : 0 ≤ 2 * a * Δ := by positivity
          calc ((Finset.Icc (-Nw) Nw).card : ℝ) * (((row jm).card : ℝ) * (2 * a * a * Δ))
              = ((Finset.Icc (-Nw) Nw).card : ℝ) * a * ((row jm).card : ℝ) * (2 * a * Δ) := by
                ring
            _ ≤ (5 * b) * (2 * (J.card : ℝ)) * (2 * a * Δ) := mul_le_mul_of_nonneg_right h1 h2
            _ = 20 * a * b * Δ * J.card := by ring
  · -- the separation properties
    intro j hj j' hj' hne
    obtain ⟨-, hwj, hvj⟩ := hy j (hJsub hj)
    obtain ⟨-, hwj', hvj'⟩ := hy j' (hJsub hj')
    have hinw : inner ℝ w (y j - y j') = ζw (y j) - ζw (y j') := by
      rw [hζw, hζw, ← inner_sub_right]
      congr 1
      abel
    have hinv : inner ℝ v (y j - y j') = ζv (y j) - ζv (y j') := by
      rw [hζv, hζv, ← inner_sub_right]
      congr 1
      abel
    have h2 : 2 ≤ |(j : ℝ) - j'| := by
      have := grid_two_le_abs (hJpar j hj j' hj') (sub_ne_zero.mpr hne)
      push_cast at this
      exact this
    refine ⟨?_, ?_, h2⟩
    · rw [hinw]
      exact grid_sub_lt_of_floor_eq ha (hwj.trans hwj'.symm)
    · rw [hinv]
      exact grid_sep_of_floor hΔ0 hvj hvj' h2
  · -- the range of the indices
    intro j hj
    have hjV := ((hmem jm j).mp (hJsub hj)).1
    rw [Finset.mem_Icc] at hjV
    have hN : (Nv : ℝ) < b / Δ + 1 := by rw [hNv]; exact Int.ceil_lt_add_one _
    have h1 : ((-Nv : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjV.1
    have h2 : (j : ℝ) ≤ (Nv : ℝ) := by exact_mod_cast hjV.2
    push_cast at h1
    rw [abs_le]
    constructor <;> linarith

end

end WangZahlLot.Obl.wz_transverse_cell_weighted_cover
