/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/SharpRootCover.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.StableRootCover

/-!
# Stable hidden sheets with the sharp fit error

`sharp_root_cover` improves `stable_root_cover`: the hidden coordinate of every point is within
`4 K⁴ a` of its sheet, an error independent of the base density bound `H`; only the radius and
the number of balls depend on `H`.

Below curvature `1 / (4 K³ a)` the discriminant is at least `1 / (2 K²)` at the points, so the
holomorphic root branch of the accepted o171 construction (`exists_sheet`, which needs only a
positive real part of the discriminant on a complex box) exists on a ball whose radius is fixed
by the discriminant coefficient bound (accepted o242). The exact quadratic identity
`F(W) - F(φ) = (W - φ) (∂_w F(W) + ∂_w F(φ)) / 2`, with both derivatives of the same sign, gives
`|W - φ| ≤ 2 K² a`. Above that curvature the points are within `4 K⁴ a` of the affine critical
center.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set Filter MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

/-- The exact difference identity of a quadratic in the hidden variable. -/
theorem qF_sub_eq {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (x : Fin 3 → ℝ) (W φ : ℝ) :
    eval (Fin.snoc x W) F - eval (Fin.snoc x φ) F =
      (W - φ) * (eval (Fin.snoc x W) (pderiv 3 F) + eval (Fin.snoc x φ) (pderiv 3 F)) / 2 := by
  rw [eval_snoc_qF hF, eval_snoc_qF hF, eval_snoc_qFw hF, eval_snoc_qFw hF]
  ring

/-- Two points of the same branch with one on the root: the sharp hidden distance. -/
theorem abs_sub_root_le {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    {K a : ℝ} (hK : 0 < K) (x : Fin 3 → ℝ) (W φ : ℝ)
    (hroot : eval (Fin.snoc x φ) F = 0) (hfit : |eval (Fin.snoc x W) F| ≤ K * a)
    (hder : K⁻¹ ≤ |eval (Fin.snoc x W) (pderiv 3 F)|)
    (hsign : 0 < eval (Fin.snoc x W) (pderiv 3 F) * eval (Fin.snoc x φ) (pderiv 3 F)) :
    |W - φ| ≤ 2 * K ^ 2 * a := by
  have hid := qF_sub_eq hF x W φ
  rw [hroot, sub_zero] at hid
  set d₁ := eval (Fin.snoc x W) (pderiv 3 F)
  set d₂ := eval (Fin.snoc x φ) (pderiv 3 F)
  have hsum : |d₁| ≤ |d₁ + d₂| := by
    rcases lt_or_gt_of_ne (show d₁ ≠ 0 by intro h; rw [h, zero_mul] at hsign; exact lt_irrefl _ hsign)
      with h1 | h1
    · have h2 : d₂ < 0 := by
        by_contra h; rw [not_lt] at h; nlinarith
      rw [abs_of_neg h1, abs_of_neg (by linarith)]; linarith
    · have h2 : 0 < d₂ := by
        by_contra h; rw [not_lt] at h; nlinarith
      rw [abs_of_pos h1, abs_of_pos (by linarith)]; linarith
  have hpos : 0 < |d₁ + d₂| := lt_of_lt_of_le (lt_of_lt_of_le (by positivity) hder) hsum
  have hWφ : |W - φ| = 2 * |eval (Fin.snoc x W) F| / |d₁ + d₂| := by
    rw [eq_div_iff hpos.ne', hid, abs_div, abs_mul]
    rw [show |(2 : ℝ)| = 2 by norm_num]
    field_simp
  rw [hWφ, div_le_iff₀ hpos]
  calc 2 * |eval (Fin.snoc x W) F| ≤ 2 * (K * a) := by gcongr
    _ = 2 * K ^ 2 * a * K⁻¹ := by field_simp
    _ ≤ 2 * K ^ 2 * a * |d₁ + d₂| := by
        have : 0 ≤ 2 * K ^ 2 * a := by
          have := abs_nonneg (eval (Fin.snoc x W) F); nlinarith [sq_nonneg K]
        exact mul_le_mul_of_nonneg_left (hder.trans hsum) this

/-- The radius of the sharp local sheet. -/
def sharpRadius (K B : ℝ) : ℝ := (864 * B * (K + 1) ^ 2 * K ^ 2)⁻¹

theorem sharpRadius_pos {K B : ℝ} (hK : 0 < K) (hB : 0 < B) : 0 < sharpRadius K B := by
  unfold sharpRadius; positivity

theorem sharpRadius_le_one {K B : ℝ} (hK : 1 ≤ K) (hB : 1 ≤ B) : sharpRadius K B ≤ 1 := by
  unfold sharpRadius
  apply inv_le_one_of_one_le₀
  have h1 : (1 : ℝ) ≤ (K + 1) ^ 2 := by nlinarith
  have h2 : (1 : ℝ) ≤ K ^ 2 := by nlinarith
  calc (1 : ℝ) ≤ 864 * 1 * 1 * 1 := by norm_num
    _ ≤ 864 * B * (K + 1) ^ 2 * K ^ 2 := by gcongr

/-- **One sharp stable sheet** (accepted o171 `exists_sheet`). Below curvature `1/(4K³a)`, a
point with the chart bounds carries a holomorphic root branch on the ball of radius
`sharpRadius K B`, and every same-branch point of that ball with the chart bounds is within
`2 K² a` of it. -/
theorem local_sharp_sheet {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    {K a B : ℝ} (hK : 2 ≤ K) (ha : 0 < a) (hB : 1 ≤ B)
    (hdisc : ∀ e, |(qdisc F).coeff e| ≤ B) (hlow : |curvature F 3| < (4 * K ^ 3 * a)⁻¹)
    (u₀ : Fin 3 → ℝ) (w₀ : ℝ) (hu₀ : ∀ i, |u₀ i| ≤ K)
    (hF0 : |eval (Fin.snoc u₀ w₀) F| ≤ K * a)
    (hFw0 : K⁻¹ ≤ |eval (Fin.snoc u₀ w₀) (pderiv 3 F)|)
    (hFw0' : |eval (Fin.snoc u₀ w₀) (pderiv 3 F)| ≤ K) :
    ∃ f : EuclideanSpace ℂ (Fin 3) → ℂ,
      DifferentiableOn ℂ f (ball (emb (toEuc u₀)) (sharpRadius K B)) ∧
      (∀ z ∈ ball (emb (toEuc u₀)) (sharpRadius K B),
        eval (Fin.snoc (fun i : Fin 3 => z i) (f z)) (F.map (algebraMap ℝ ℂ)) = 0) ∧
      (∀ u : Fin 3 → ℝ, ‖toEuc u - toEuc u₀‖ < sharpRadius K B →
        (f (emb (toEuc u))).im = 0) ∧
      (∀ (u : Fin 3 → ℝ) (w : ℝ), ‖toEuc u - toEuc u₀‖ < sharpRadius K B →
        |eval (Fin.snoc u w) F| ≤ K * a →
        K⁻¹ ≤ |eval (Fin.snoc u w) (pderiv 3 F)| →
        0 < eval (Fin.snoc u w) (pderiv 3 F) * eval (Fin.snoc u₀ w₀) (pderiv 3 F) →
        |w - (f (emb (toEuc u))).re| ≤ 2 * K ^ 2 * a) := by
  have hK0 : 0 < K := by linarith
  set r₀ := sharpRadius K B with hr₀
  have hr₀pos : 0 < r₀ := sharpRadius_pos hK0 (by linarith)
  have hr₀1 : r₀ ≤ 1 := sharpRadius_le_one (by linarith) hB
  set σ := eval (Fin.snoc u₀ w₀) (pderiv 3 F) with hσ
  have hσ0 : σ ≠ 0 := by
    intro h; rw [h, abs_zero] at hFw0; have : (0 : ℝ) < K⁻¹ := by positivity
    linarith
  -- the discriminant at the base point
  have hΔ0 : (2 * K ^ 2)⁻¹ ≤ eval u₀ (qdisc F) := by
    rw [eval_qdisc hF u₀ w₀]
    have h1 : K⁻¹ ^ 2 ≤ σ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hFw0 2
      rwa [sq_abs] at this
    have h2 : |4 * qa F * eval (Fin.snoc u₀ w₀) F| ≤ (2 * K ^ 2)⁻¹ := by
      rw [qa, abs_mul, abs_mul]
      have hq : |curvature F 3 / 2| = |curvature F 3| / 2 := by rw [abs_div]; norm_num
      rw [hq, show |(4 : ℝ)| = 4 by norm_num]
      calc 4 * (|curvature F 3| / 2) * |eval (Fin.snoc u₀ w₀) F|
          ≤ 4 * ((4 * K ^ 3 * a)⁻¹ / 2) * (K * a) := by gcongr
        _ = (2 * K ^ 2)⁻¹ := by field_simp
    have h3 : K⁻¹ ^ 2 = 2 * (2 * K ^ 2)⁻¹ := by field_simp
    have := le_abs_self (4 * qa F * eval (Fin.snoc u₀ w₀) F)
    linarith
  -- positive real part of the discriminant on the complex box
  have hDpos : ∀ y : Fin 3 → ℂ, (∀ i, ‖y i - ((toEuc u₀) i : ℂ)‖ < r₀) →
      0 < (eval₂ (algebraMap ℝ ℂ) y (qb F * qb F - MvPolynomial.C (4 * qa F) * qc F)).re := by
    intro y hy
    have hvar := Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_sub_le (qdisc F)
      (qdisc_degree hF) B hdisc (K + 1) r₀ (by linarith) hr₀pos.le hr₀1
      (fun j => ((u₀ j : ℝ) : ℂ)) y
      (fun i => by rw [Complex.norm_real, Real.norm_eq_abs]; linarith [hu₀ i])
      (fun i => (hy i).le)
    rw [Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_ofReal] at hvar
    have hsmall : 216 * B * (K + 1) ^ 2 * r₀ = (4 * K ^ 2)⁻¹ := by
      rw [hr₀, sharpRadius]; field_simp; ring
    rw [hsmall] at hvar
    have hre : |(eval₂ (algebraMap ℝ ℂ) y (qdisc F)).re - eval u₀ (qdisc F)| ≤ (4 * K ^ 2)⁻¹ := by
      have := Complex.abs_re_le_norm (eval₂ (algebraMap ℝ ℂ) y (qdisc F) - (eval u₀ (qdisc F) : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re] at this
      linarith
    have h4 : (4 * K ^ 2)⁻¹ < (2 * K ^ 2)⁻¹ := by
      apply inv_strictAnti₀ (by positivity); nlinarith
    have := neg_abs_le ((eval₂ (algebraMap ℝ ℂ) y (qdisc F)).re - eval u₀ (qdisc F))
    show 0 < (eval₂ (algebraMap ℝ ℂ) y (qdisc F)).re
    linarith
  obtain ⟨f, hfd, hfrel, hfreal⟩ := Submission.Obl.k4_stable_quadratic_hidden_sheets.exists_sheet
    (qa F) (qb F) (qc F) (toEuc u₀) σ r₀ hr₀pos hσ0
    (by
      intro h0
      have : σ = eval u₀ (qb F) := by rw [hσ, eval_snoc_qFw hF, h0]; ring
      show 0 < eval u₀ (qb F) * σ
      rw [← this]; exact mul_self_pos.mpr hσ0)
    hDpos
  refine ⟨f, hfd, ?_, ?_, ?_⟩
  · intro z hz
    rw [eval_map_snoc_qF hF]
    have := hfrel z hz
    linear_combination this
  · intro u hu
    obtain ⟨φ, hφ, -, -⟩ := hfreal (toEuc u) hu
    rw [show emb (toEuc u) = WithLp.toLp 2 (fun j => ((toEuc u) j : ℂ)) from rfl, hφ]
    simp
  · intro u w hu hFuw hFwuw hsign
    obtain ⟨φ, hφ, hroot, hφsign⟩ := hfreal (toEuc u) hu
    have hfre : (f (emb (toEuc u))).re = φ := by
      rw [show emb (toEuc u) = WithLp.toLp 2 (fun j => ((toEuc u) j : ℂ)) from rfl, hφ]
      simp
    rw [hfre]
    have hroot' : eval (Fin.snoc u φ) F = 0 := by
      rw [eval_snoc_qF hF]
      have : eval (fun j => (toEuc u) j) (qb F) = eval u (qb F) := rfl
      have h2 : eval (fun j => (toEuc u) j) (qc F) = eval u (qc F) := rfl
      rw [this, h2] at hroot
      linear_combination hroot
    have hsign' : 0 < eval (Fin.snoc u w) (pderiv 3 F) * eval (Fin.snoc u φ) (pderiv 3 F) := by
      have hb : eval (fun j => (toEuc u) j) (qb F) = eval u (qb F) := rfl
      rw [hb] at hφsign
      have hφw : eval (Fin.snoc u φ) (pderiv 3 F) = 2 * qa F * φ + eval u (qb F) :=
        eval_snoc_qFw hF u φ
      rw [hφw]
      -- both factors have the sign of `σ`
      have h1 := hsign
      rcases lt_or_gt_of_ne hσ0 with hneg | hpos
      · have hA : eval (Fin.snoc u w) (pderiv 3 F) < 0 := by
          by_contra h; rw [not_lt] at h
          have : eval (Fin.snoc u w) (pderiv 3 F) * σ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos h hneg.le
          linarith
        have hB' : 2 * qa F * φ + eval u (qb F) < 0 := by
          by_contra h; rw [not_lt] at h
          have : (2 * qa F * φ + eval u (qb F)) * σ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos h hneg.le
          linarith
        exact mul_pos_of_neg_of_neg hA hB'
      · have hA : 0 < eval (Fin.snoc u w) (pderiv 3 F) := by
          by_contra h; rw [not_lt] at h
          have : eval (Fin.snoc u w) (pderiv 3 F) * σ ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg h hpos.le
          linarith
        have hB' : 0 < 2 * qa F * φ + eval u (qb F) := by
          by_contra h; rw [not_lt] at h
          have : (2 * qa F * φ + eval u (qb F)) * σ ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg h hpos.le
          linarith
        exact mul_pos hA hB'
    exact abs_sub_root_le hF hK0 u w φ hroot' hFuw hFwuw hsign'

/-- **Sharp stable root cover.** As `stable_root_cover`, with the hidden fit error `4 K⁴ a`
independent of the base density bound `H`. -/
theorem sharp_root_cover :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (K H a : ℝ), 2 ≤ K → 1 ≤ H → 0 < a → a ≤ 1 →
    ∀ (F : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (lam : Measure Ω), IsProbabilityMeasure lam →
    ∀ (u : Ω → Fin 3 → ℝ) (w : Ω → ℝ), Measurable u →
    (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
      lam (u ⁻¹' U) ≤ ENNReal.ofReal H * volume U) →
    (∀ᵐ ω ∂lam, (∀ i, |u ω i| ≤ K) ∧
      |eval (Fin.snoc (u ω) (w ω)) F| ≤ K * a ∧
      K⁻¹ ≤ |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| ∧
      |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| ≤ K ∧
      |curvature F 3| ≤ K / a) →
    ∃ (r : ℝ) (n : ℕ) (c : Fin n → EuclideanSpace ℝ (Fin 3))
      (f : Fin n → EuclideanSpace ℂ (Fin 3) → ℂ),
      (K * H) ^ (-(C : ℝ)) ≤ r ∧ r ≤ 1 ∧ (n : ℝ) ≤ (K * H) ^ (C : ℝ) ∧
      (∀ j, IsSheet 2 (fun z => f j (emb (c j) + ((r : ℝ) : ℂ) • z))) ∧
      ∀ᵐ ω ∂lam, ∃ j, ‖toEuc (u ω) - c j‖ ≤ r / 4 ∧
        |w ω - (f j (emb (toEuc (u ω)))).re| ≤ 4 * K ^ 4 * a := by
  classical
  obtain ⟨C₂, hC₂, hcal⟩ := coeff_bound_of_density
  set cA : ℕ := 3 * ⌈C₂⌉₊ + 10 with hcA
  set e : ℕ := cA + 19 with he
  set Cfin : ℕ := 3 * e + 25 with hCfin
  refine ⟨Cfin, by omega, ?_⟩
  intro K H a hK hH ha ha1 F hF Ω _ lam hlam u w hu hdom hae
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = K * H := ⟨_, rfl⟩
  have hX : 2 ≤ X := by
    rw [hXdef]
    calc (2 : ℝ) = 2 * 1 := by norm_num
      _ ≤ K * H := mul_le_mul hK hH (by norm_num) (by linarith only [hK])
  have hXpos : 0 < X := by linarith only [hX]
  have hX1 : 1 ≤ X := by linarith only [hX]
  have hKX : K ≤ X := by rw [hXdef]; exact le_mul_of_one_le_right (by linarith only [hK]) hH
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = X ^ cA := ⟨_, rfl⟩
  have hA2 : 2 ≤ A := by rw [hAdef]; exact hX.trans (le_self_pow₀ hX1 (by omega))
  have hApos : 0 < A := by linarith only [hA2]
  have hKA : 2 * K ≤ A := by
    have : X ^ 2 ≤ A := by rw [hAdef]; exact pow_le_pow_right₀ hX1 (by omega)
    calc 2 * K ≤ 2 * X := by linarith only [hKX]
      _ ≤ X * X := mul_le_mul_of_nonneg_right hX hXpos.le
      _ = X ^ 2 := by ring
      _ ≤ A := this
  -- the good set
  set G : Set Ω := {ω | (∀ i, |u ω i| ≤ K) ∧ |eval (Fin.snoc (u ω) (w ω)) F| ≤ K * a ∧
      K⁻¹ ≤ |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| ∧
      |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| ≤ K ∧ |curvature F 3| ≤ K / a} with hGdef
  have haeG : ∀ᵐ ω ∂lam, ω ∈ G := hae
  -- the discriminant coefficients
  have hdisc : ∀ e', |(qdisc F).coeff e'| ≤ A := by
    intro e'
    have h := hcal K H (3 * K ^ 2) (by linarith) hH (by positivity) (qdisc F) (qdisc_degree hF)
      Ω lam hlam u hu hdom (by
        filter_upwards [hae] with ω hω
        exact ⟨hω.1, abs_eval_qdisc_le hF ha (u ω) (w ω) hω.2.1 hω.2.2.2.1 hω.2.2.2.2⟩) e'
    exact h.trans (by rw [hAdef, hXdef]; exact calib_le_pow hC₂ hK hH)
  -- the radius and the grid
  have hXe : 0 < X ^ e := by positivity
  set r : ℝ := (X ^ e)⁻¹ / 8 with hrdef
  have hr : 0 < r := by positivity
  have h8r : 8 * r ≤ sharpRadius K A := by
    rw [hrdef, sharpRadius]
    have hK1 : (K + 1) ^ 2 ≤ X ^ 4 := by
      have : K + 1 ≤ X ^ 2 := by
        calc K + 1 ≤ X + X := by linarith only [hKX, hX]
          _ = 2 * X := by ring
          _ ≤ X * X := mul_le_mul_of_nonneg_right hX hXpos.le
          _ = X ^ 2 := by ring
      calc (K + 1) ^ 2 ≤ (X ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) this 2
        _ = X ^ 4 := by ring
    have hK2 : K ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) hKX 2
    have h864 : (864 : ℝ) ≤ X ^ 13 := by
      have : (2 : ℝ) ^ 13 ≤ X ^ 13 := pow_le_pow_left₀ (by norm_num) hX 13
      norm_num at this; linarith only [this]
    have hprod : 864 * A * (K + 1) ^ 2 * K ^ 2 ≤ X ^ e := by
      calc 864 * A * (K + 1) ^ 2 * K ^ 2 ≤ X ^ 13 * X ^ cA * X ^ 4 * X ^ 2 := by
            rw [hAdef]; gcongr
        _ = X ^ e := by rw [← pow_add, ← pow_add, ← pow_add, he]; ring_nf
    have hpos : 0 < 864 * A * (K + 1) ^ 2 * K ^ 2 := by positivity
    calc 8 * ((X ^ e)⁻¹ / 8) = (X ^ e)⁻¹ := by ring
      _ ≤ (864 * A * (K + 1) ^ 2 * K ^ 2)⁻¹ := inv_anti₀ hpos hprod
  set s : ℝ := r / 4 with hsdef
  have hs : 0 < s := by positivity
  set M : ℕ := ⌈K / s⌉₊ + 1 with hMdef
  have hnear : ∀ ω ∈ G, ∃ m : Fin 3 → Fin (2 * M + 1),
      ‖toEuc (u ω) - gridPt s M m‖ ≤ r / 4 := by
    intro ω hω
    obtain ⟨m, hm⟩ := exists_gridPt_near hs (by linarith) (u ω) hω.1
    exact ⟨m, hm.trans (le_of_eq hsdef)⟩
  have hnormu : ∀ ω ∈ G, ‖toEuc (u ω)‖ ≤ A := by
    intro ω hω
    have : ‖toEuc (u ω)‖ ≤ 2 * K := norm_toEuc_le (by linarith) fun i => by
      have := hω.1 i; linarith
    linarith
  -- the index set
  let I := (Fin 3 → Fin (2 * M + 1)) × Bool
  set n := Fintype.card I with hn
  let eI : I ≃ Fin n := Fintype.equivFin I
  have hFne : F ≠ 0 := by
    intro h0
    obtain ⟨ω, hω⟩ := haeG.exists
    have := hω.2.2.1
    simp only [h0, map_zero, abs_zero] at this
    have : (0 : ℝ) < K⁻¹ := by positivity
    linarith
  have hFmap0 : F.map (algebraMap ℝ ℂ) ≠ 0 := by
    intro h0
    apply hFne
    exact MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective ℝ ℂ)
      (h0.trans (map_zero _).symm)
  have hFmapdeg : (F.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 :=
    (Finset.sup_mono (support_map_subset (algebraMap ℝ ℂ) F)).trans hF
  -- counting
  have hcount : (n : ℝ) ≤ X ^ Cfin := by
    have hcard : n = (2 * M + 1) ^ 3 * 2 := by
      simp only [hn, I, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have hceil : (⌈K / s⌉₊ : ℝ) ≤ K / s + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hKs : K / s = 32 * K * X ^ e := by
      rw [hsdef, hrdef]; field_simp; ring
    have hX7 : (69 : ℝ) ≤ X ^ 7 := by
      have : (2 : ℝ) ^ 7 ≤ X ^ 7 := pow_le_pow_left₀ (by norm_num) hX 7
      norm_num at this; linarith only [this]
    have hXe1 : (1 : ℝ) ≤ X ^ (e + 1) := one_le_pow₀ hX1
    have hKXe : K * X ^ e ≤ X ^ (e + 1) := by
      rw [pow_succ X e, mul_comm (X ^ e) X]; exact mul_le_mul_of_nonneg_right hKX hXe.le
    have hM8 : ((2 * M + 1 : ℕ) : ℝ) ≤ X ^ (e + 8) := by
      push_cast [hMdef]
      calc 2 * ((⌈K / s⌉₊ : ℝ) + 1) + 1 ≤ 2 * (K / s + 1 + 1) + 1 := by linarith only [hceil]
        _ = 64 * (K * X ^ e) + 5 := by rw [hKs]; ring
        _ ≤ 64 * X ^ (e + 1) + 5 * X ^ (e + 1) := by linarith only [hKXe, hXe1]
        _ = 69 * X ^ (e + 1) := by ring
        _ ≤ X ^ 7 * X ^ (e + 1) := mul_le_mul_of_nonneg_right hX7 (by positivity)
        _ = X ^ (e + 8) := by rw [← pow_add]; ring_nf
    rw [hcard]
    push_cast
    calc ((2 * (M : ℝ) + 1)) ^ 3 * 2 ≤ (X ^ (e + 8)) ^ 3 * X := by
          have hM8' : 2 * (M : ℝ) + 1 ≤ X ^ (e + 8) := by exact_mod_cast hM8
          gcongr
      _ = X ^ (3 * e + 25) := by rw [← pow_mul, ← pow_succ]; ring_nf
      _ ≤ X ^ Cfin := pow_le_pow_right₀ hX1 (by omega)
  have hrX : X ^ (-(Cfin : ℝ)) ≤ r := by
    rw [Real.rpow_neg hXpos.le, Real.rpow_natCast, hrdef]
    have h8 : (8 : ℝ) ≤ X ^ 3 := by
      have : (2 : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
      norm_num at this; linarith only [this]
    have hle : X ^ e * 8 ≤ X ^ Cfin := by
      calc X ^ e * 8 ≤ X ^ e * X ^ 3 := mul_le_mul_of_nonneg_left h8 hXe.le
        _ = X ^ (e + 3) := by rw [← pow_add]
        _ ≤ X ^ Cfin := pow_le_pow_right₀ hX1 (by omega)
    rw [div_eq_mul_inv, ← mul_inv]
    exact inv_anti₀ (by positivity) hle
  have hr1 : r ≤ 1 := by
    rw [hrdef]
    have : (X ^ e)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hX1)
    linarith
  have hA1 : 1 ≤ A := by linarith only [hA2]
  by_cases hlow : |curvature F 3| < (4 * K ^ 3 * a)⁻¹
  · -- low curvature: one stable sheet per grid cell and branch
    have hex : ∀ ω ∈ G, ∃ f : EuclideanSpace ℂ (Fin 3) → ℂ,
        DifferentiableOn ℂ f (ball (emb (toEuc (u ω))) (sharpRadius K A)) ∧
        (∀ z ∈ ball (emb (toEuc (u ω))) (sharpRadius K A),
          eval (Fin.snoc (fun i : Fin 3 => z i) (f z)) (F.map (algebraMap ℝ ℂ)) = 0) ∧
        (∀ v : Fin 3 → ℝ, ‖toEuc v - toEuc (u ω)‖ < sharpRadius K A →
          (f (emb (toEuc v))).im = 0) ∧
        (∀ (v : Fin 3 → ℝ) (w' : ℝ), ‖toEuc v - toEuc (u ω)‖ < sharpRadius K A →
          |eval (Fin.snoc v w') F| ≤ K * a →
          K⁻¹ ≤ |eval (Fin.snoc v w') (pderiv 3 F)| →
          0 < eval (Fin.snoc v w') (pderiv 3 F) * eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) →
          |w' - (f (emb (toEuc v))).re| ≤ 2 * K ^ 2 * a) := by
      intro ω hω
      obtain ⟨hu1, hF1, hFw1, hFw2, -⟩ := hω
      exact local_sharp_sheet hF hK ha hA1 hdisc hlow (u ω) (w ω) hu1 hF1 hFw1 hFw2
    choose! sheetAt hsheetAt using hex
    let wit : I → Ω → Prop := fun mσ ω => ω ∈ G ∧ ‖toEuc (u ω) - gridPt s M mσ.1‖ ≤ r ∧
      (0 < eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) ↔ mσ.2 = true)
    let patch : I → EuclideanSpace ℂ (Fin 3) → ℂ := fun mσ =>
      if h : ∃ ω, wit mσ ω then sheetAt (Classical.choose h) else fun _ => 0
    have hball : ∀ (m : Fin 3 → Fin (2 * M + 1)) (ω₀ : Ω),
        ‖toEuc (u ω₀) - gridPt s M m‖ ≤ r →
        ball (emb (gridPt s M m)) (4 * r) ⊆ ball (emb (toEuc (u ω₀))) (sharpRadius K A) := by
      intro m ω₀ hd z hz
      rw [mem_ball] at hz ⊢
      refine lt_of_lt_of_le ?_ h8r
      calc dist z (emb (toEuc (u ω₀))) ≤ dist z (emb (gridPt s M m)) +
            dist (emb (gridPt s M m)) (emb (toEuc (u ω₀))) := dist_triangle _ _ _
        _ < 4 * r + r := by
            have h2 : dist (emb (gridPt s M m)) (emb (toEuc (u ω₀))) ≤ r := by
              rw [dist_emb, dist_comm, dist_eq_norm]; exact hd
            linarith only [hz, h2]
        _ ≤ 8 * r := by linarith only [hr]
    refine ⟨r, n, fun j => gridPt s M (eI.symm j).1, fun j => patch (eI.symm j), ?_, hr1, ?_, ?_, ?_⟩
    · rw [← hXdef]; exact hrX
    · rw [← hXdef, Real.rpow_natCast]; exact hcount
    · intro j
      show IsSheet 2 (fun z => patch (eI.symm j) (emb (gridPt s M (eI.symm j).1) + ((r : ℝ) : ℂ) • z))
      by_cases h : ∃ ω, wit (eI.symm j) ω
      · have hpatch : patch (eI.symm j) = sheetAt (Classical.choose h) := by
          simp only [patch, dif_pos h]
        rw [hpatch]
        obtain ⟨hω₀G, hω₀d, -⟩ := Classical.choose_spec h
        obtain ⟨hhol, hrel, hreal, -⟩ := hsheetAt _ hω₀G
        apply isSheet_of_local hFmap0 hFmapdeg hr
        · exact hhol.mono (hball _ _ hω₀d)
        · intro z hz; exact hrel z (hball _ _ hω₀d hz)
        · intro x hx
          have hx' : ‖toEuc (WithLp.ofLp x) - toEuc (u (Classical.choose h))‖ <
              sharpRadius K A := by
            refine lt_of_lt_of_le ?_ h8r
            simp only [toEuc, WithLp.toLp_ofLp]
            calc ‖x - toEuc (u (Classical.choose h))‖ ≤
                ‖x - gridPt s M (eI.symm j).1‖ + ‖gridPt s M (eI.symm j).1 -
                  toEuc (u (Classical.choose h))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ ≤ r + r := by
                  rw [norm_sub_rev (gridPt s M _)]; linarith only [hx, hω₀d]
              _ < 8 * r := by linarith only [hr]
          have := hreal _ hx'
          simpa only [toEuc, WithLp.toLp_ofLp] using this
      · have hpatch : patch (eI.symm j) = fun _ => 0 := by
          simp only [patch, dif_neg h]
        rw [hpatch]
        exact isSheet_zero (by norm_num)
    · filter_upwards [haeG] with ω hω
      obtain ⟨m, hm⟩ := hnear ω hω
      set σ : Bool := decide (0 < eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)) with hσ
      have hwit : ∃ ω', wit (m, σ) ω' :=
        ⟨ω, hω, hm.trans (by linarith only [hr]), by simp [hσ]⟩
      refine ⟨eI (m, σ), ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply]; exact hm
      · simp only [Equiv.symm_apply_apply]
        have hpatch : patch (m, σ) = sheetAt (Classical.choose hwit) := by
          simp only [patch, dif_pos hwit]
        rw [hpatch]
        obtain ⟨hω₀G, hω₀d, hω₀s⟩ := Classical.choose_spec hwit
        obtain ⟨-, -, -, hclose⟩ := hsheetAt _ hω₀G
        have hd : ‖toEuc (u ω) - toEuc (u (Classical.choose hwit))‖ < sharpRadius K A := by
          refine lt_of_lt_of_le ?_ h8r
          calc ‖toEuc (u ω) - toEuc (u (Classical.choose hwit))‖ ≤
              ‖toEuc (u ω) - gridPt s M m‖ + ‖gridPt s M m - toEuc (u (Classical.choose hwit))‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ r / 4 + r := by
                rw [norm_sub_rev (gridPt s M m)]; linarith only [hm, hω₀d]
            _ < 8 * r := by linarith only [hr]
        have hFw0 : eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) ≠ 0 := by
          intro h0
          have := hω.2.2.1
          rw [h0, abs_zero] at this
          have : (0 : ℝ) < K⁻¹ := by positivity
          linarith
        have hFw1 : eval (Fin.snoc (u (Classical.choose hwit)) (w (Classical.choose hwit)))
            (pderiv 3 F) ≠ 0 := by
          intro h0
          have := hω₀G.2.2.1
          rw [h0, abs_zero] at this
          have : (0 : ℝ) < K⁻¹ := by positivity
          linarith
        have hsign : 0 < eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) *
            eval (Fin.snoc (u (Classical.choose hwit)) (w (Classical.choose hwit))) (pderiv 3 F) := by
          by_cases hp : 0 < eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)
          · have hσt : σ = true := by simp [hσ, hp]
            have hp' := hω₀s.mpr hσt
            exact mul_pos hp hp'
          · have hσf : σ = false := by simp [hσ, hp]
            have hp' : ¬ 0 < eval (Fin.snoc (u (Classical.choose hwit))
                (w (Classical.choose hwit))) (pderiv 3 F) := by
              intro hh; have := hω₀s.mp hh; rw [hσf] at this; exact Bool.false_ne_true this
            have hneg : eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) < 0 :=
              lt_of_le_of_ne (not_lt.mp hp) hFw0
            have hneg' := lt_of_le_of_ne (not_lt.mp hp') hFw1
            exact mul_pos_of_neg_of_neg hneg hneg'
        have hcl := hclose (u ω) (w ω) hd hω.2.1 hω.2.2.1 hsign
        refine hcl.trans ?_
        have hK2 : (1 : ℝ) ≤ 2 * K ^ 2 := by
          have : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ (by linarith only [hK])
          linarith only [this]
        calc 2 * K ^ 2 * a = (2 * K ^ 2 * a) * 1 := (mul_one _).symm
          _ ≤ (2 * K ^ 2 * a) * (2 * K ^ 2) :=
              mul_le_mul_of_nonneg_left hK2 (by positivity)
          _ = 4 * K ^ 4 * a := by ring
  · -- high curvature: the vertex sheet everywhere
    rw [not_lt] at hlow
    have hcpos : 0 < |curvature F 3| := lt_of_lt_of_le (by positivity) hlow
    have hcurv0 : curvature F 3 ≠ 0 := abs_pos.mp hcpos
    refine ⟨r, n, fun j => gridPt s M (eI.symm j).1, fun _ => vertexSheet F, ?_, hr1, ?_, ?_, ?_⟩
    · rw [← hXdef]; exact hrX
    · rw [← hXdef, Real.rpow_natCast]; exact hcount
    · intro j
      apply isSheet_of_local (vertexRel_ne_zero F) (vertexRel_degree hF) hr
      · exact (differentiable_vertexSheet F).differentiableOn
      · intro z _; exact eval_vertexRel F z
      · intro x _
        have hx : x = toEuc (WithLp.ofLp x) := by simp [toEuc]
        rw [hx, vertexSheet_emb]
        simp
    · filter_upwards [haeG] with ω hω
      obtain ⟨m, hm⟩ := hnear ω hω
      refine ⟨eI (m, true), by simp only [Equiv.symm_apply_apply]; exact hm, ?_⟩
      rw [vertexSheet_emb, Complex.ofReal_re, abs_sub_vertex_le hF hcurv0, div_le_iff₀ hcpos]
      have hFw := hω.2.2.2.1
      have h4 : 1 ≤ 4 * K ^ 3 * a * |curvature F 3| := by
        have hpos : 0 < 4 * K ^ 3 * a := by positivity
        rw [inv_le_iff_one_le_mul₀ hpos] at hlow
        linarith only [hlow]
      calc |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| ≤ K := hFw
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * (4 * K ^ 3 * a * |curvature F 3|) := by
            exact mul_le_mul_of_nonneg_left h4 (by linarith only [hK])
        _ = 4 * K ^ 4 * a * |curvature F 3| := by ring


end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
