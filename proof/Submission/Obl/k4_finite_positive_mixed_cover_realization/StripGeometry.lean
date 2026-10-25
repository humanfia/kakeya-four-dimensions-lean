/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/StripGeometry.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Lib.K4VelocityStrips
import Submission.Lib.K4XInterface.Outputs
import Submission.Obl.k4_native_finite_terminal_atlas_lift.FrameComposition

/-!
Whole-block strip narrowing in the original chart coordinates. We use the
accepted unit-block strip frame and the accepted exact affine composition
formulas, keeping the original time interval and quadratic test.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open scoped RealInnerProductSpace
open Submission.Lib.K4XInterface
open Submission.Lib.K4VelocityStrips
open Submission.Obl.k4_native_finite_terminal_atlas_lift

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Frame := Matrix (Fin 2) (Fin 2) ℝ
abbrev Line := ℕ × (Fin 6 → ℝ)

/-- The spatial residual on a chart's actual block is affine in unit time. -/
theorem normalized_offset_affine (l : Line) (t₀ q τ : ℝ)
    (c u : Plane) (Q : Frame) :
    Matrix.toEuclideanLin Q⁻¹ (gy l (t₀ + q * τ) - c - (t₀ + q * τ) • u) =
      Matrix.toEuclideanLin Q⁻¹ (gy l t₀ - c - t₀ • u) +
        τ • (q • Matrix.toEuclideanLin Q⁻¹ (gv l - u)) := by
  rw [gy_offset_eq l c u t₀ (t₀ + q * τ)]
  simp only [map_add, map_smul]
  module

/-- A velocity strip and a midpoint bin narrow the original frame throughout
the entire actual time block, with the exact composed center and velocity. -/
theorem composed_strip_whole_block_fit (l : Line)
    {t₀ q K D r s β : ℝ} {c u e n : Plane} {Q : Frame}
    (hq : 0 < q) (hQ : Q.det ≠ 0)
    (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (hfit : ∀ t ∈ Set.Icc t₀ (t₀ + q),
      ‖Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)‖ ≤ K)
    (hvel : |inner ℝ (q • Matrix.toEuclideanLin Q⁻¹ (gv l - u)) n - β| ≤ D * r)
    (hmid : |inner ℝ (Matrix.toEuclideanLin Q⁻¹
      (gy l (t₀ + q / 2) - c - (t₀ + q / 2) • u)) n - s| ≤ r)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ (t₀ + q)) :
    ‖Matrix.toEuclideanLin (Q * stripLocalFrame K D r e n)⁻¹
      (gy l t - compositeCenter t₀ q c (stripCenter n s β) u (stripVelocity n β) Q -
        t • compositeVelocity q u (stripVelocity n β) Q)‖ ≤ 2 := by
  let a := Matrix.toEuclideanLin Q⁻¹ (gy l t₀ - c - t₀ • u)
  let v := q • Matrix.toEuclideanLin Q⁻¹ (gv l - u)
  have hfit' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖a + τ • v‖ ≤ K := by
    intro τ hτ
    rw [← normalized_offset_affine]
    apply hfit
    constructor <;> nlinarith [hτ.1, hτ.2]
  have hmid' : |inner ℝ (a + (1 / 2 : ℝ) • v) n - s| ≤ r := by
    change |inner ℝ
      (Matrix.toEuclideanLin Q⁻¹ (gy l t₀ - c - t₀ • u) +
        (1 / 2 : ℝ) • (q • Matrix.toEuclideanLin Q⁻¹ (gv l - u))) n - s| ≤ r
    rw [← normalized_offset_affine]
    simpa only [mul_one_div] using hmid
  let τ := (t - t₀) / q
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hq.le
    · exact (div_le_one hq).mpr (by linarith [ht.2])
  have htτ : t₀ + q * τ = t := by dsimp [τ]; field_simp; ring
  rw [composite_frame_residual t₀ q t hq.ne' c (stripCenter n s β) u
    (stripVelocity n β) (gy l t) Q (stripLocalFrame K D r e n) hQ]
  have hoff : Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u) = a + τ • v := by
    rw [← normalized_offset_affine, htτ]
  rw [hoff]
  exact strip_whole_block_fit hK hD hr he hn hen hfit' hvel hmid' hτ

/-- The determinant saving composes with the old chart's normalized width.
All geometric losses are charged before comparing the width exponents. -/
theorem composed_strip_width_gain (Q : Frame) (T : ℕ)
    {K D r N w error gain saving : ℝ} {e n : Plane}
    (hN : 1 ≤ N) (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (hwidth : |Q.det| * (4 : ℝ) ^ T ≤ N ^ (-w + error))
    (hfactor : K * (1 + D) * r ≤ N ^ (-saving))
    (hbudget : error + gain ≤ saving) :
    |(Q * stripLocalFrame K D r e n).det| * (4 : ℝ) ^ T ≤ N ^ (-(w + gain)) := by
  rw [strip_composite_determinant Q T hK hD hr he hn hen]
  calc
    _ ≤ N ^ (-w + error) * N ^ (-saving) :=
      mul_le_mul hwidth hfactor (by positivity) (Real.rpow_nonneg (by linarith) _)
    _ = N ^ (-w + error - saving) := by
      rw [← Real.rpow_add (by linarith : 0 < N)]
      congr 1
    _ ≤ N ^ (-(w + gain)) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The midpoint bin of the normalized trajectory can be listed from the
current original spatial base and time, on the original block. -/
theorem original_midpoint_bin_mem_list (l : Line)
    {t₀ q r β t : ℝ} {C : ℕ} {c u n : Plane} {Q : Frame}
    (hq : 0 < q) (hr : 0 < r) (ht : t ∈ Set.Icc t₀ (t₀ + q))
    (hvel : |inner ℝ (q • Matrix.toEuclideanLin Q⁻¹ (gv l - u)) n - β| ≤
      (C : ℝ) * r) :
    ⌊inner ℝ (Matrix.toEuclideanLin Q⁻¹
      (gy l (t₀ + q / 2) - c - (t₀ + q / 2) • u)) n / r⌋ ∈
      midpointBinList r n β ((t - t₀) / q)
        (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) C := by
  have hτ : (t - t₀) / q ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hq.le
    · exact (div_le_one hq).mpr (by linarith [ht.2])
  have htτ : t₀ + q * ((t - t₀) / q) = t := by field_simp; ring
  have h := midpoint_bin_mem_list
    (a := Matrix.toEuclideanLin Q⁻¹ (gy l t₀ - c - t₀ • u)) hr hτ hvel
  rw [← normalized_offset_affine, ← normalized_offset_affine] at h
  simpa only [mul_one_div, htτ] using h

/-- Retaining a true quadratic chart while replacing its spatial frame by
the strip frame. The explicit format and coefficient budgets are independent
of the incidence mass calculation. -/
theorem gchart_composed_strip
    {Nk κ κ' j r₀ Bv Dstrip ρ s β : ℝ} {M M' D D' T : ℕ}
    {Ev : Set (Line × ℝ)} {c u e n : Plane} {Q : Frame}
    {R : MvPolynomial (Fin 4) ℝ} {A A' : Set Line}
    {F F' : Set (Line × ℝ)} {ex ex' : Prop}
    (h : gchart Nk M D κ T j r₀ Bv Ev c u Q R A F ex)
    (hNk : 1 ≤ Nk) (hM : M ≤ M') (hD : D ≤ D')
    (hκ : 0 < κ) (hκκ : κ ≤ κ') (hκ' : 4 ≤ κ') (hB : 0 ≤ Bv)
    (hDs : 0 ≤ Dstrip) (hρ : 0 < ρ)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (hvel : ∀ l ∈ A',
      |inner ℝ (((2 : ℝ) ^ T)⁻¹ • Matrix.toEuclideanLin Q⁻¹ (gv l - u)) n - β| ≤
        Dstrip * ρ)
    (hmid : ∀ l ∈ A', |inner ℝ (Matrix.toEuclideanLin Q⁻¹
      (gy l (j / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ / 2) - c -
        (j / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ / 2) • u)) n - s| ≤ ρ)
    (hcu : ‖compositeCenter (j / (2 : ℝ) ^ T) (((2 : ℝ) ^ T)⁻¹)
        c (stripCenter n s β) u (stripVelocity n β) Q‖ +
      ‖compositeVelocity (((2 : ℝ) ^ T)⁻¹) u (stripVelocity n β) Q‖ ≤ Nk ^ M')
    (hbudget : ∑ i : Fin 2, ∑ k : Fin 2,
      (|(Q * stripLocalFrame κ Dstrip ρ e n) i k| +
        |(Q * stripLocalFrame κ Dstrip ρ e n)⁻¹ i k|) ≤ Nk ^ M')
    (hsize : ∑ i : Fin 2, ∑ k : Fin 2,
      |(Q * stripLocalFrame κ Dstrip ρ e n) i k| ≤ κ' / (2 : ℝ) ^ T)
    (hA : A' ⊆ A) (hF : F' ⊆ F) (hFA : ∀ p ∈ F', p.1 ∈ A')
    (hmA : MeasurableSet A') (hmF : MeasurableSet F')
    (hfmt : ∀ i, gfmt 6 (Nk ^ M') D' {x | (i, x) ∈ A'} ∧
      gfmt 7 (Nk ^ M') D' {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F'})
    (hex : ex') :
    gchart Nk M' D' κ' T j r₀ Bv Ev
      (compositeCenter (j / (2 : ℝ) ^ T) (((2 : ℝ) ^ T)⁻¹)
        c (stripCenter n s β) u (stripVelocity n β) Q)
      (compositeVelocity (((2 : ℝ) ^ T)⁻¹) u (stripVelocity n β) Q)
      (Q * stripLocalFrame κ Dstrip ρ e n) R A' F' ex' := by
  let Q' := Q * stripLocalFrame κ Dstrip ρ e n
  have hQ : Q.det ≠ 0 := h.1
  have hQ' : Q'.det ≠ 0 := by
    dsimp only [Q']
    rw [Matrix.det_mul]
    apply mul_ne_zero hQ
    apply abs_pos.mp
    rw [stripLocalFrame_abs_det hκ hDs hρ he hn hen]
    positivity
  have hinv : (Q'⁻¹)⁻¹ = Q' := inv_inv_of_det_ne_zero Q' hQ'
  have hfull (l : Line) (hl : l ∈ A') :
      ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T),
        ‖Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)‖ ≤ κ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hwhole, -, -⟩ := h
    exact fun t ht => ((hwhole l (hA hl)).2.2 t ht).1
  have hend : j / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ = (j + 1) / (2 : ℝ) ^ T := by
    ring
  have hgeom (l : Line) (hl : l ∈ A') (t : ℝ)
      (ht : t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)) :
      ‖Matrix.toEuclideanLin Q'⁻¹
        (gy l t - compositeCenter (j / (2 : ℝ) ^ T) (((2 : ℝ) ^ T)⁻¹)
          c (stripCenter n s β) u (stripVelocity n β) Q -
          t • compositeVelocity (((2 : ℝ) ^ T)⁻¹) u (stripVelocity n β) Q)‖ ≤ 2 := by
    apply composed_strip_whole_block_fit l (by positivity) hQ hκ hDs hρ he hn hen
      (fun z hz => hfull l hl z (by simpa only [hend] using hz)) (hvel l hl) (hmid l hl)
    simpa only [hend] using ht
  have hout := gchart_reframe h hNk hM hD hκ hκκ hB
    Q'⁻¹ (by rw [det_inv_fin2]; exact inv_ne_zero hQ') _ _
    (a := 2) (b := 2) (by linarith) (fun l hl t ht => ?_)
    hcu (by simpa only [hinv] using hbudget) (by simpa only [hinv] using hsize)
    hA hF hFA hmA hmF hfmt hex
  · simpa only [hinv] using hout
  · constructor
    · simpa only [toEuclideanLin_apply_fin2, Real.norm_eq_abs] using
        (PiLp.norm_apply_le _ (0 : Fin 2)).trans (hgeom l hl t ht)
    · simpa only [toEuclideanLin_apply_fin2, Real.norm_eq_abs] using
        (PiLp.norm_apply_le _ (1 : Fin 2)).trans (hgeom l hl t ht)

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
