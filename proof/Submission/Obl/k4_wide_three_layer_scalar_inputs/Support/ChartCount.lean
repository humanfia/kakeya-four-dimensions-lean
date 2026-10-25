import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.DeepPrune

set_option linter.unusedVariables false

/-!
# Counting charts and their palette weights

Fine velocity bins inside a chart velocity bin, the palette weight of all chart velocity bins
(at most twice the palette), and the number of intercept bins of charts through a window.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- The fine velocity bins (width `δv`) compatible with the chart velocity bin `n` (width `χ`). -/
def Vt (δv χ : ℝ) (n : ℤ) : Set ℤ := {w | ⌊(w : ℝ) * δv / χ⌋ = n ∨ ⌊(w : ℝ) * δv / χ⌋ + 1 = n}

theorem vbin_mem_Vt {δv χ b : ℝ} (hδv : 0 < δv) (hχ : 0 < χ) (hle : δv ≤ χ) :
    vbin δv b ∈ Vt δv χ ⌊b / χ⌋ := by
  set w := ⌊b / δv⌋
  have h1 : (w : ℝ) * δv ≤ b := by
    have := Int.floor_le (b / δv); rwa [le_div_iff₀ hδv] at this
  have h2 : b < ((w : ℝ) + 1) * δv := by
    have := Int.lt_floor_add_one (b / δv); rwa [div_lt_iff₀ hδv] at this
  have hlo : ⌊(w : ℝ) * δv / χ⌋ ≤ ⌊b / χ⌋ := Int.floor_mono (div_le_div_of_nonneg_right h1 hχ.le)
  have hhi : ⌊b / χ⌋ ≤ ⌊(w : ℝ) * δv / χ⌋ + 1 := by
    have : b / χ < (w : ℝ) * δv / χ + 1 := by
      rw [div_lt_iff₀ hχ]
      have : (w : ℝ) * δv / χ * χ = (w : ℝ) * δv := by field_simp
      nlinarith
    have h3 : ⌊b / χ⌋ ≤ ⌊(w : ℝ) * δv / χ + 1⌋ := Int.floor_mono this.le
    rw [Int.floor_add_one] at h3
    exact h3
  show ⌊(w : ℝ) * δv / χ⌋ = ⌊b / χ⌋ ∨ ⌊(w : ℝ) * δv / χ⌋ + 1 = ⌊b / χ⌋
  omega

/-- The chart velocity bins carry at most twice the palette. -/
theorem sum_Vt_le (πV : Measure ℤ) [IsProbabilityMeasure πV] (δv χ : ℝ) (NF : Finset ℤ) :
    ∑ n ∈ NF, πV (Vt δv χ n) ≤ 2 := by
  classical
  set A : ℤ → Set ℤ := fun n => {w | ⌊(w : ℝ) * δv / χ⌋ = n}
  have hsplit : ∀ n, Vt δv χ n ⊆ A n ∪ A (n - 1) := by
    intro n w hw
    rcases hw with h | h
    · exact Or.inl h
    · right; show ⌊(w : ℝ) * δv / χ⌋ = n - 1; omega
  have hdisj : ∀ (S : Finset ℤ), Set.PairwiseDisjoint (↑S) A := by
    intro S a _ b _ hab
    exact Set.disjoint_left.mpr fun w h1 h2 => hab (h1.symm.trans h2)
  have hA : ∀ S : Finset ℤ, ∑ n ∈ S, πV (A n) ≤ 1 := by
    intro S
    rw [← measure_biUnion_finset (hdisj S) (fun n _ => (Set.to_countable _).measurableSet)]
    exact prob_le_one
  calc ∑ n ∈ NF, πV (Vt δv χ n) ≤ ∑ n ∈ NF, (πV (A n) + πV (A (n - 1))) :=
        Finset.sum_le_sum fun n _ => (measure_mono (hsplit n)).trans (measure_union_le _ _)
    _ = ∑ n ∈ NF, πV (A n) + ∑ n ∈ NF.image (fun n => n - 1), πV (A n) := by
        rw [Finset.sum_add_distrib, Finset.sum_image]
        intro a _ b _ h; simpa using h
    _ ≤ 1 + 1 := add_le_add (hA _) (hA _)
    _ = 2 := by norm_num

/-- Integers in a window of half-width `A` at scale `χ`. -/
theorem card_window_le (S : Finset ℤ) {χ A B : ℝ} (hχ : 0 < χ) (hA : 0 ≤ A) :
    ((S.filter (fun m : ℤ => |((m : ℝ) + 1 / 2) * χ - B| ≤ A)).card : ℝ) ≤ 2 * A / χ + 1 := by
  classical
  set T := S.filter (fun m : ℤ => |((m : ℝ) + 1 / 2) * χ - B| ≤ A)
  by_cases hT : T.Nonempty
  · set m₀ := T.min' hT
    have hm₀ : m₀ ∈ T := T.min'_mem hT
    have hsub : T ⊆ Finset.Icc m₀ (m₀ + ⌊2 * A / χ⌋) := by
      intro m hm
      rw [Finset.mem_Icc]
      refine ⟨T.min'_le m hm, ?_⟩
      have h1 := (Finset.mem_filter.mp hm).2
      have h2 := (Finset.mem_filter.mp hm₀).2
      have hdiff : ((m : ℝ) - m₀) * χ ≤ 2 * A := by
        have := abs_le.mp h1; have := abs_le.mp h2; nlinarith
      have hdiff' : ((m : ℝ) - m₀) ≤ 2 * A / χ := by rw [le_div_iff₀ hχ]; exact hdiff
      have : m - m₀ ≤ ⌊2 * A / χ⌋ := by
        rw [Int.le_floor]; push_cast; exact hdiff'
      omega
    have hcard := Finset.card_le_card hsub
    rw [Int.card_Icc] at hcard
    have hfl : (⌊2 * A / χ⌋ : ℝ) ≤ 2 * A / χ := Int.floor_le _
    have hpos : 0 ≤ ⌊2 * A / χ⌋ := Int.floor_nonneg.mpr (by positivity)
    have : (T.card : ℤ) ≤ ⌊2 * A / χ⌋ + 1 := by
      have := hcard
      have e : m₀ + ⌊2 * A / χ⌋ + 1 - m₀ = ⌊2 * A / χ⌋ + 1 := by ring
      rw [e] at this
      have h' := Int.toNat_of_nonneg (show 0 ≤ ⌊2 * A / χ⌋ + 1 by omega)
      omega
    have : (T.card : ℝ) ≤ (⌊2 * A / χ⌋ : ℝ) + 1 := by exact_mod_cast this
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hT]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

open scoped Classical in
/-- **Palette weight of the coarse predictors on charts in a window.**  If the charts satisfying
`P` have, for each velocity bin `n`, their intercept bin in a window of half-width `A`, and each
chart carries at most `H` listed coarse predictors, then the palette weight of the listed coarse
predictors on such charts is at most `2 H (2A/χ + 1)`. -/
theorem sum_window_charts_le {Γ : Type*} [Fintype Γ] (chartOf : Γ → ℤ × ℤ)
    (G : ℤ × ℤ → Finset Γ) {H : ℝ} (hH : 0 ≤ H) (hG : ∀ ch, ((G ch).card : ℝ) ≤ H)
    (P : ℤ × ℤ → Prop) {χ A : ℝ} (hχ : 0 < χ) (hA : 0 ≤ A) (B : ℤ → ℝ)
    (hP : ∀ n m, P (n, m) → |((m : ℝ) + 1 / 2) * χ - B n| ≤ A)
    (πV : Measure ℤ) [IsProbabilityMeasure πV] (δv : ℝ) :
    ∑ γ ∈ Finset.univ.filter (fun γ => P (chartOf γ) ∧ γ ∈ G (chartOf γ)),
      πV (Vt δv χ (chartOf γ).1) ≤ ENNReal.ofReal (2 * H * (2 * A / χ + 1)) := by
  set ChS : Finset (ℤ × ℤ) := Finset.univ.image chartOf
  set NF : Finset ℤ := ChS.image Prod.fst
  have h1 : ∑ γ ∈ Finset.univ.filter (fun γ => P (chartOf γ) ∧ γ ∈ G (chartOf γ)),
      πV (Vt δv χ (chartOf γ).1) ≤
      ∑ ch ∈ ChS.filter P, ((G ch).card : ℝ≥0∞) * πV (Vt δv χ ch.1) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := chartOf) (t := ChS.filter P)]
    · apply Finset.sum_le_sum
      intro ch _
      calc ∑ γ ∈ (Finset.univ.filter (fun γ => P (chartOf γ) ∧ γ ∈ G (chartOf γ))).filter
            (fun γ => chartOf γ = ch), πV (Vt δv χ (chartOf γ).1)
          = ∑ γ ∈ (Finset.univ.filter (fun γ => P (chartOf γ) ∧ γ ∈ G (chartOf γ))).filter
            (fun γ => chartOf γ = ch), πV (Vt δv χ ch.1) := by
            apply Finset.sum_congr rfl; intro γ hγ
            rw [(Finset.mem_filter.mp hγ).2]
        _ = (((Finset.univ.filter (fun γ => P (chartOf γ) ∧ γ ∈ G (chartOf γ))).filter
            (fun γ => chartOf γ = ch)).card : ℝ≥0∞) * πV (Vt δv χ ch.1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((G ch).card : ℝ≥0∞) * πV (Vt δv χ ch.1) := by
            gcongr
            intro γ hγ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
            rw [← hγ.2]; exact hγ.1.2
    · intro γ hγ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
      simp only [ChS, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨γ, rfl⟩, hγ.1⟩
  have h2 : ∑ ch ∈ ChS.filter P, ((G ch).card : ℝ≥0∞) * πV (Vt δv χ ch.1) ≤
      ∑ ch ∈ ChS.filter P, ENNReal.ofReal H * πV (Vt δv χ ch.1) := by
    gcongr with ch _
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hG ch)
  have h3 : ∑ ch ∈ ChS.filter P, ENNReal.ofReal H * πV (Vt δv χ ch.1) =
      ENNReal.ofReal H * ∑ n ∈ NF, (((ChS.filter P).filter (fun ch => ch.1 = n)).card : ℝ≥0∞) *
        πV (Vt δv χ n) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := NF)]
    · apply Finset.sum_congr rfl; intro n _
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro ch hch
      rw [(Finset.mem_filter.mp hch).2]; simp
    · intro ch hch
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hch).1
  have h4 : ∀ n, ((((ChS.filter P).filter (fun ch => ch.1 = n)).card : ℝ≥0∞)) ≤
      ENNReal.ofReal (2 * A / χ + 1) := by
    intro n
    set T := (ChS.filter P).filter (fun ch => ch.1 = n) with hTdef
    have hcard : T.card = (T.image Prod.snd).card := by
      rw [Finset.card_image_of_injOn]
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact Prod.ext (ha'.trans hb'.symm) hab
    have hS : (T.image Prod.snd).filter (fun m : ℤ => |((m : ℝ) + 1 / 2) * χ - B n| ≤ A) =
        T.image Prod.snd := by
      apply Finset.filter_true_of_mem
      intro m hm
      obtain ⟨ch, hch, rfl⟩ := Finset.mem_image.mp hm
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hch).1).2
      have h2 := (Finset.mem_filter.mp hch).2
      have := hP ch.1 ch.2 (by simpa using h1)
      rw [h2] at this
      exact this
    have hw := card_window_le (T.image Prod.snd) hχ hA (B := B n)
    rw [hS, ← hcard] at hw
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hw
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ ENNReal.ofReal H * ∑ n ∈ NF, ENNReal.ofReal (2 * A / χ + 1) * πV (Vt δv χ n) := by
        gcongr with n _; exact h4 n
    _ = ENNReal.ofReal H * ENNReal.ofReal (2 * A / χ + 1) * ∑ n ∈ NF, πV (Vt δv χ n) := by
        rw [← Finset.mul_sum, mul_assoc]
    _ ≤ ENNReal.ofReal H * ENNReal.ofReal (2 * A / χ + 1) * 2 := by
        gcongr; exact sum_Vt_le πV δv χ NF
    _ = ENNReal.ofReal (2 * H * (2 * A / χ + 1)) := by
        rw [← ENNReal.ofReal_mul hH, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
