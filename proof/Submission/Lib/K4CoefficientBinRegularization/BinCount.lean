-- Adapted from: here:o202 (session x0952), Regularization/BinCount.lean.
import Submission.Lib.K4CoefficientBinRegularization.Model
import Submission.Lib.K4CoefficientBinRegularization.DurationCount
import Submission.Lib.K4ProjectedGroups.BandCover
import Submission.Lib.K4QuadraticSheets.JetBins

namespace Submission.Lib.K4CoefficientBinRegularization.Reg

open MeasureTheory Set FirstJet
open scoped ENNReal Classical

noncomputable section

/-- The four original static coefficients, on a common grid. -/
def coefficientCode {Ω : Type*} (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (r : ℝ) (l : Ω) :
    Fin 4 → ℤ := ![⌊y l 0 / r⌋, ⌊y l 1 / r⌋, ⌊β l / r⌋, ⌊γ l / r⌋]

/-- A fixed polynomial cost for passing from instantaneous support to static coefficients. -/
def packingBound (K : ℝ) : ℝ := (4 * K + 5) ^ 2 * K * (20 * K ^ 2 + 3) ^ 4

/-- Long labeled times and the slope comparison bound all occupied coefficient bins.
The witnesses and their durations are measured before any coefficient-bin deletion. -/
theorem coefficient_count_of_long_witnesses {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ r δ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ)
    (hSlope : SlopeComparison y β γ E K ζ) (hK : 1 ≤ K)
    (hζ : 0 < ζ) (hr : ζ ≤ r) (hr1 : r ≤ 1) (hδ : 0 < δ)
    (C : Finset (Fin 4 → ℤ))
    (hw : ∀ b ∈ C, ∃ l : Ω, ENNReal.ofReal δ ≤ volume (Prod.mk l ⁻¹' E) ∧
      coefficientCode y β γ r l = b) :
    (C.card : ℝ) * δ ≤ packingBound K * r ^ (-2 - d) := by
  classical
  have hr0 : 0 < r := hζ.trans_le hr
  have hK0 : 0 ≤ K := by linarith
  rcases C.eq_empty_or_nonempty with hC | hC
  · rw [hC, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (by dsimp [packingBound]; positivity) (Real.rpow_nonneg hr0.le _)
  haveI : Nonempty Ω := ⟨(hw hC.choose hC.choose_spec).choose⟩
  choose! l hlong hcode using hw
  apply finite_count_of_duration C (fun b => Prod.mk (l b) ⁻¹' E) hδ
    (mul_nonneg (by dsimp [packingBound]; positivity) (Real.rpow_nonneg hr0.le _))
    (fun b _ => measurable_prodMk_left hU.measurableSet_E)
    (fun b _ t ht => (hU.subset_E ht).2) hlong
  intro t
  let G := C.filter fun b => (l b, t) ∈ E
  let Y : Finset (Fin 2 → ℤ) := G.image fun b => fun i => ⌊y (l b) i / r⌋
  let key : (Fin 4 → ℤ) → (Fin 2 → ℤ) × ℤ :=
    fun b => (fun i => ⌊y (l b) i / r⌋, ⌊scal y β γ F (l b) t / r⌋)
  obtain ⟨S, hS, hSmem⟩ := hU.support t r hr hr1
  have hG (b : Fin 4 → ℤ) (hb : b ∈ G) : b ∈ C ∧ (l b, t) ∈ E := Finset.mem_filter.mp hb
  have hY : (Y.card : ℝ) ≤ (4 * K / r + 5) ^ 2 := by
    have hd : ∀ a ∈ Y, ∀ b ∈ Y, ∀ i, |(a i : ℝ) - (b i : ℝ)| ≤ 2 * K / r + 1 := by
      intro a ha b hb i
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
      apply Submission.Lib.K4ProjectedGroups.abs_code_sub_le hr0
      calc |y (l a') i - y (l b') i| ≤ |y (l a') i| + |y (l b') i| := abs_sub _ _
        _ ≤ 2 * K := by linarith [hU.bound_y (l a') i, hU.bound_y (l b') i]
    have hc := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter Y
      (show 0 ≤ 2 * K / r + 1 by positivity) hd
    norm_num only [Fintype.card_fin] at hc
    convert hc using 1 <;> congr 1 <;> ring
  have hkeys : (G.image key).card ≤ Y.card * S.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨b, hb, rfl⟩, hSmem (l b) (hG b hb).2⟩
  have hfiber : ∀ a ∈ G.image key,
      (((G.filter fun b => key b = a).card : ℝ)) ≤ (20 * K ^ 2 + 3) ^ 4 := by
    intro a ha
    apply (Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter _
      (show 0 ≤ 10 * K ^ 2 by positivity) ?_).trans_eq
      (by norm_num only [Fintype.card_fin]; congr 1 <;> ring)
    intro b hb b' hb' i
    obtain ⟨hbG, hbkey⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbG', hbkey'⟩ := Finset.mem_filter.mp hb'
    have hekey : key b = key b' := hbkey.trans hbkey'.symm
    have hy : ∀ j, |y (l b) j - y (l b') j| ≤ r := by
      intro j
      apply (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hr0 ?_).le
      exact congrFun (congrArg Prod.fst hekey) j
    have hsc : |scal y β γ F (l b) t - scal y β γ F (l b') t| ≤ r :=
      (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hr0
        (congrArg Prod.snd hekey)).le
    have hx : |xbar β γ (l b) t - xbar β γ (l b') t| ≤ (2 * K + 1) * r := by
      have heq : xbar β γ (l b) t - xbar β γ (l b') t =
          (scal y β γ F (l b) t - scal y β γ F (l b') t) +
            F t 0 * (y (l b) 0 - y (l b') 0) + F t 1 * (y (l b) 1 - y (l b') 1) := by
        dsimp [scal]; ring
      rw [heq]
      calc
        _ ≤ |scal y β γ F (l b) t - scal y β γ F (l b') t| +
            |F t 0 * (y (l b) 0 - y (l b') 0)| + |F t 1 * (y (l b) 1 - y (l b') 1)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ r + K * r + K * r := by
          rw [abs_mul, abs_mul]
          exact add_le_add (add_le_add hsc (mul_le_mul (hU.bound_F t 0) (hy 0) (abs_nonneg _) hK0))
            (mul_le_mul (hU.bound_F t 1) (hy 1) (abs_nonneg _) hK0)
        _ = _ := by ring
    have hg : |γ (l b) - γ (l b')| ≤ 6 * K ^ 2 * r := by
      have hs := hSlope (l b) (l b') t t (hG b hbG).2 (hG b' hbG').2
      simp only [sub_self, abs_zero, zero_add] at hs
      calc
        _ ≤ K * (|xbar β γ (l b) t - xbar β γ (l b') t| +
            |y (l b) 0 - y (l b') 0| + |y (l b) 1 - y (l b') 1| + ζ) := hs
        _ ≤ K * (((2 * K + 1) * r) + r + r + r) := by gcongr; exact hy 0; exact hy 1
        _ ≤ 6 * K ^ 2 * r := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg hr0.le hK0)]
    have ht : t ∈ Icc (0 : ℝ) 1 := (hU.subset_E (hG b hbG).2).2
    have hβ : |β (l b) - β (l b')| ≤ 9 * K ^ 2 * r := by
      have heq : β (l b) - β (l b') =
          (xbar β γ (l b) t - xbar β γ (l b') t) - t * (γ (l b) - γ (l b')) := by
        dsimp [xbar]; ring
      rw [heq]
      calc
        _ ≤ |xbar β γ (l b) t - xbar β γ (l b') t| + |t * (γ (l b) - γ (l b'))| := abs_sub _ _
        _ ≤ (2 * K + 1) * r + 6 * K ^ 2 * r := by
          rw [abs_mul, abs_of_nonneg ht.1]
          exact add_le_add hx ((mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans (by simpa using hg))
        _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg hr0.le (show 0 ≤ 3 * K + 1 by positivity))]
    have hKsq : 1 ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
    have hround {v w L : ℝ} (h : |v - w| ≤ L * r) :
        |(⌊v / r⌋ : ℝ) - (⌊w / r⌋ : ℝ)| ≤ L + 1 := by
      have h' := Submission.Lib.K4ProjectedGroups.abs_code_sub_le hr0 h
      simpa only [mul_div_cancel_right₀ _ hr0.ne'] using h'
    rw [← hcode b (hG b hbG).1, ← hcode b' (hG b' hbG').1]
    fin_cases i
    · change |(⌊y (l b) 0 / r⌋ : ℝ) - (⌊y (l b') 0 / r⌋ : ℝ)| ≤ _
      have h' := hround (show |y (l b) 0 - y (l b') 0| ≤ 1 * r by simpa using hy 0)
      linarith
    · change |(⌊y (l b) 1 / r⌋ : ℝ) - (⌊y (l b') 1 / r⌋ : ℝ)| ≤ _
      have h' := hround (show |y (l b) 1 - y (l b') 1| ≤ 1 * r by simpa using hy 1)
      linarith
    · change |(⌊β (l b) / r⌋ : ℝ) - (⌊β (l b') / r⌋ : ℝ)| ≤ _
      exact (hround hβ).trans (by linarith)
    · change |(⌊γ (l b) / r⌋ : ℝ) - (⌊γ (l b') / r⌋ : ℝ)| ≤ _
      exact (hround hg).trans (by linarith)
  have hGcard : (G.card : ℝ) ≤ (G.image key).card * (20 * K ^ 2 + 3) ^ 4 := by
    rw [Finset.card_eq_sum_card_image key G, Nat.cast_sum]
    calc
      _ ≤ ∑ _a ∈ G.image key, (20 * K ^ 2 + 3) ^ 4 := Finset.sum_le_sum hfiber
      _ = _ := by simp
  have hYbound : (4 * K / r + 5) ^ 2 ≤ ((4 * K + 5) / r) ^ 2 := by
    gcongr
    apply (le_div_iff₀ hr0).mpr
    have hrmul : (4 * K / r) * r = 4 * K := div_mul_cancel₀ _ hr0.ne'
    nlinarith
  have hreq : r ^ (-2 - d) = (r ^ 2)⁻¹ * r ^ (-d) := by
    rw [show (-2 - d : ℝ) = -2 + (-d) by ring, Real.rpow_add hr0,
      Real.rpow_neg hr0.le, Real.rpow_two]
  change (G.card : ℝ) ≤ _
  calc
    _ ≤ ((Y.card : ℝ) * S.card) * (20 * K ^ 2 + 3) ^ 4 :=
      hGcard.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkeys) (by positivity))
    _ ≤ (((4 * K + 5) / r) ^ 2 * (K * r ^ (-d))) * (20 * K ^ 2 + 3) ^ 4 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hY.trans hYbound) hS (Nat.cast_nonneg _) (by positivity)) (by positivity)
    _ = packingBound K * r ^ (-2 - d) := by
      rw [hreq, div_pow]
      dsimp [packingBound]
      ring

end
end Submission.Lib.K4CoefficientBinRegularization.Reg
