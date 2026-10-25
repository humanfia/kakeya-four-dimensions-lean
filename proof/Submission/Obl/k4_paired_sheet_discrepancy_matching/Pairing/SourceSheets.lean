/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/SourceSheets.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/SourceSheets.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.PolynomialSheets
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.ShortSegments

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MvPolynomial Set

noncomputable def realTrace (P : MvPolynomial (Fin 4) ℝ)
    (zline : ℝ → EuclideanSpace ℝ (Fin 3)) (wline : ℝ → ℝ) (t : ℝ) : ℝ :=
  eval (Fin.snoc (fun i : Fin 3 => zline t i) (wline t)) P

noncomputable def realDerivativeTrace (P : MvPolynomial (Fin 4) ℝ)
    (zline : ℝ → EuclideanSpace ℝ (Fin 3)) (wline : ℝ → ℝ) (t : ℝ) : ℝ :=
  realTrace (pderiv (3 : Fin 4) P) zline wline t

/-- Choose a source branch once, and retain its actual-trajectory fit on the
short segment. Holomorphy and simplicity of this same named sheet are supplied
by `simpleSheet_spec`. -/
theorem exists_simpleSheet_source_fit (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (U : Set (EuclideanSpace ℂ (Fin 3)))
    (hdisc : ∀ z ∈ U, 0 < (eval (fun i => z i) ((disc P).map (algebraMap ℝ ℂ))).re)
    (zline : ℝ → EuclideanSpace ℝ (Fin 3)) (wline : ℝ → ℝ)
    {m d s e t₀ V B ρ r : ℝ} (hse : s < e) (hV : 0 ≤ V) (hB : 0 < B) (hρ : 0 ≤ ρ)
    (hr : 0 ≤ r) (ht₀ : t₀ ∈ Icc s e)
    (hs : |m * s + d| ≤ V) (he : |m * e + d| ≤ V) (hfloor : B ≤ |m * t₀ + d|)
    (hsmall : (2 * V / (e - s)) * r ≤ B / 2)
    (hderiv : ∀ t ∈ Icc s e, realDerivativeTrace P zline wline t = m * t + d)
    (hres : ∀ t ∈ Icc s e, |realTrace P zline wline t| ≤ ρ)
    (hmap : ∀ t ∈ Icc s e ∩ Icc (t₀ - r) (t₀ + r), emb (zline t) ∈ U) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧
      ‖simpleSheet P σ (emb (zline t₀)) - (wline t₀ : ℂ)‖ ≤ 2 * ρ / B ∧
      ∀ t ∈ Icc s e ∩ Icc (t₀ - r) (t₀ + r),
        ‖(wline t : ℂ) - simpleSheet P σ (emb (zline t))‖ ≤ 4 * ρ / B := by
  let σ : ℝ := if 0 ≤ m * t₀ + d then 1 else -1
  have hσ : σ ^ 2 = 1 := by dsimp [σ]; split_ifs <;> norm_num
  have hsign : σ * (m * t₀ + d) = |m * t₀ + d| := by
    dsimp [σ]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have hreal (x : EuclideanSpace ℝ (Fin 3)) (hx : emb x ∈ U) :
      0 ≤ eval (fun i => x i) (disc P) := by
    have hh := hdisc (emb x) hx
    change 0 < (eval (fun i : Fin 3 => (x i : ℂ)) ((disc P).map (algebraMap ℝ ℂ))).re at hh
    rw [eval_complexification] at hh
    simpa only [Complex.ofReal_re] using hh.le
  have ht₀' : t₀ ∈ Icc s e ∩ Icc (t₀ - r) (t₀ + r) :=
    ⟨ht₀, by constructor <;> linarith⟩
  refine ⟨σ, hσ, ?_, ?_⟩
  · have hne : realDerivativeTrace P zline wline t₀ ≠ 0 := by
      rw [hderiv t₀ ht₀]
      intro hz
      simp only [hz, abs_zero] at hfloor
      linarith
    have herr := simpleSheet_error P hP σ hσ (zline t₀) (wline t₀)
      (hreal _ (hmap t₀ ht₀')) hne (by
        change σ * realDerivativeTrace P zline wline t₀ = |realDerivativeTrace P zline wline t₀|
        rw [hderiv t₀ ht₀]
        exact hsign)
    refine herr.trans ?_
    change 2 * |realTrace P zline wline t₀| / |realDerivativeTrace P zline wline t₀| ≤ _
    rw [hderiv t₀ ht₀]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left (hres t₀ ht₀) (by norm_num)) hB hfloor
  · intro t ht
    have hdist : |t - t₀| ≤ r := abs_le.mpr ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
    have hchange : |(m * t + d) - (m * t₀ + d)| ≤ B / 2 := by
      calc
        |(m * t + d) - (m * t₀ + d)| = |m| * |t - t₀| := by
          rw [← abs_mul]; congr 1; ring
        _ ≤ (2 * V / (e - s)) * r :=
          mul_le_mul (affine_slope_bound hse hs he) hdist (abs_nonneg _) (by positivity)
        _ ≤ B / 2 := hsmall
    obtain ⟨hBt, hsignt⟩ := derivative_sign_persists hB hσ hsign hfloor hchange
    have hne : realDerivativeTrace P zline wline t ≠ 0 := by
      rw [hderiv t ht.1]
      intro hz
      simp only [hz, abs_zero] at hBt
      linarith
    have herr := simpleSheet_error P hP σ hσ (zline t) (wline t)
      (hreal _ (hmap t ht)) hne (by
        change σ * realDerivativeTrace P zline wline t = |realDerivativeTrace P zline wline t|
        rw [hderiv t ht.1]
        exact hsignt)
    rw [norm_sub_rev] at herr
    refine herr.trans ?_
    change 2 * |realTrace P zline wline t| / |realDerivativeTrace P zline wline t| ≤ _
    rw [hderiv t ht.1]
    calc
      2 * |realTrace P zline wline t| / |m * t + d| ≤ 2 * ρ / (B / 2) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hres t ht.1) (by norm_num))
          (by positivity) hBt
      _ = 4 * ρ / B := by ring

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
