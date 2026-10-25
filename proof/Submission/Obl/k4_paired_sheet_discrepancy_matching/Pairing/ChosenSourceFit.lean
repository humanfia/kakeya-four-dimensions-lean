/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/ChosenSourceFit.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SourceSheets
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SheetBridge

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MvPolynomial Set

/-- The nearest branch selected at the source remains the nearest branch on a
short trajectory segment. The source sign is kept explicitly for the jet table. -/
theorem chosen_simpleSheet_source_fit
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (zline : ℝ → EuclideanSpace ℝ (Fin 3)) (wline : ℝ → ℝ)
    {m d s e t₀ A B V r σ : ℝ}
    (hse : s < e) (hA : 0 ≤ A) (hB : 0 < B) (hV : 0 ≤ V)
    (hσ : σ ^ 2 = 1)
    (hderiv : ∀ t ∈ Icc s e, realDerivativeTrace P zline wline t = m * t + d)
    (hbound : ∀ t ∈ Icc s e, |realDerivativeTrace P zline wline t| ≤ A)
    (hfloor : B ≤ |m * t₀ + d|) (hsign : σ * (m * t₀ + d) = |m * t₀ + d|)
    (hres : ∀ t ∈ Icc s e, |realTrace P zline wline t| ≤ V)
    (hdisc : ∀ t ∈ Icc s e ∩ Icc (t₀ - r) (t₀ + r),
      0 ≤ eval (fun i => zline t i) (disc P))
    (hsmall : (2 * A / (e - s)) * r ≤ B / 2) :
    ∀ t ∈ Icc s e ∩ Icc (t₀ - r) (t₀ + r),
      ‖(wline t : ℂ) - simpleSheet P σ (emb (zline t))‖ ≤ 4 * V / B := by
  have hs : |m * s + d| ≤ A := by
    rw [← hderiv s ⟨le_rfl, hse.le⟩]
    exact hbound s ⟨le_rfl, hse.le⟩
  have he : |m * e + d| ≤ A := by
    rw [← hderiv e ⟨hse.le, le_rfl⟩]
    exact hbound e ⟨hse.le, le_rfl⟩
  intro t ht
  have hdist : |t - t₀| ≤ r := abs_le.mpr ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
  have hchange : |(m * t + d) - (m * t₀ + d)| ≤ B / 2 := by
    calc _ = |m| * |t - t₀| := by rw [← abs_mul]; congr 1; ring
      _ ≤ (2 * A / (e - s)) * r :=
        mul_le_mul (affine_slope_bound hse hs he) hdist (abs_nonneg _) (by positivity)
      _ ≤ B / 2 := hsmall
  obtain ⟨hfloor', hsign'⟩ := derivative_sign_persists hB hσ hsign hfloor hchange
  have hne : realDerivativeTrace P zline wline t ≠ 0 := by
    rw [hderiv t ht.1]
    intro hz
    rw [hz, abs_zero] at hfloor'
    linarith
  have herr := simpleSheet_error P hP σ hσ (zline t) (wline t) (hdisc t ht) hne (by
    change σ * realDerivativeTrace P zline wline t = |realDerivativeTrace P zline wline t|
    rw [hderiv t ht.1]
    exact hsign')
  rw [norm_sub_rev]
  refine herr.trans ?_
  change 2 * |realTrace P zline wline t| / |realDerivativeTrace P zline wline t| ≤ _
  rw [hderiv t ht.1]
  calc _ ≤ 2 * V / (B / 2) :=
        div_le_div₀ (mul_nonneg (by norm_num) hV)
          (mul_le_mul_of_nonneg_left (hres t ht.1) (by norm_num)) (by positivity) hfloor'
    _ = 4 * V / B := by ring

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
