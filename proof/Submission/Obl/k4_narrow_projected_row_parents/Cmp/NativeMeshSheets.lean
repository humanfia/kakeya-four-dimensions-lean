/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/NativeMeshSheets.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.NativeMeshAlgebra

/-!
# Native sheets from finite mesh caps: one pass

For a probability law of points `(u, w)` with finite mesh caps `lam {cell = q} ≤ H δ³` and the
chart bounds of a quadratic hidden test `F` at width `a` and of the native signal `S`
(`NChart`), `PassResult` provides one holomorphic native sheet per branch (the sign of
`∂_w F`), defined on the complex ball of radius `4ρ`, `ρ ≥ (K H)^(-n)`, around every point
outside a set of mass `(K H)^(-A)`, bounded by `(K H)^n`, real on the real points, a root of
a nonzero relation of degree `≤ 4`, and within `32 K⁹ a` of the native value of the point.

The three regimes of the curvature `κ = ∂²_w F` are `pass_high` (critical center),
`pass_zero` (`κ = 0`) and `pass_low`; no continuous base density and no coefficient bound
of `F` or `S` is used, only fixed-degree mesh calibration of base polynomials.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

universe v

/-- The result of one native pass. -/
def PassResult (n A : ℕ) (K H a : ℝ) (F S : MvPolynomial (Fin 4) ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (lam : Measure Ω) (u : Ω → Fin 3 → ℝ) (w : Ω → ℝ) : Prop :=
  ∃ (ρ : ℝ) (R : MvPolynomial (Fin 4) ℂ) (g : Bool → EuclideanSpace ℂ (Fin 3) → ℂ) (E : Set Ω),
    ((K * H) ^ n)⁻¹ ≤ ρ ∧ ρ ≤ 1 ∧ R ≠ 0 ∧ R.totalDegree ≤ 4 ∧ MeasurableSet E ∧
    lam E ≤ ENNReal.ofReal (((K * H) ^ A)⁻¹) ∧
    ∀ᵐ ω ∂lam, ω ∉ E →
      SheetOn R (g (branch F (u ω) (w ω))) (toEuc (u ω)) (4 * ρ) ((K * H) ^ n) ∧
      |eval (Fin.snoc (u ω) (w ω)) S - (g (branch F (u ω) (w ω)) (emb (toEuc (u ω)))).re| ≤
        32 * K ^ 9 * a

theorem PassResult.mono {n n' A : ℕ} {K H a : ℝ} {F S : MvPolynomial (Fin 4) ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {lam : Measure Ω} {u : Ω → Fin 3 → ℝ} {w : Ω → ℝ}
    (hX : 1 ≤ K * H) (hn : n ≤ n') (h : PassResult n A K H a F S lam u w) :
    PassResult n' A K H a F S lam u w := by
  obtain ⟨ρ, R, g, E, hρ, hρ1, hR, hRd, hE, hEm, hae⟩ := h
  have hpow : (K * H) ^ n ≤ (K * H) ^ n' := pow_le_pow_right₀ hX hn
  refine ⟨ρ, R, g, E, ?_, hρ1, hR, hRd, hE, hEm, ?_⟩
  · refine le_trans ?_ hρ
    exact inv_anti₀ (by positivity) hpow
  · filter_upwards [hae] with ω hω hωE
    obtain ⟨h1, h2⟩ := hω hωE
    exact ⟨h1.mono hpow, h2⟩

/-! ### Common facts -/

theorem norm_toEuc_two {u : Fin 3 → ℝ} {K : ℝ} (hu : ∀ i, |u i| ≤ K) : ‖toEuc u‖ ≤ 2 * K := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hu 0)
  exact norm_toEuc_le (by linarith) (fun i => by have := hu i; linarith)

theorem norm_le_of_mem_ball_center {u : Fin 3 → ℝ} {K ρ : ℝ} (hK : 2 ≤ K)
    (hu : ∀ i, |u i| ≤ K) (hρ : ρ ≤ 1) {z : EuclideanSpace ℂ (Fin 3)}
    (hz : z ∈ ball (emb (toEuc u)) (4 * ρ)) : ‖z‖ ≤ 4 * K := by
  rw [mem_ball, dist_eq_norm] at hz
  have h1 : ‖emb (toEuc u)‖ ≤ 2 * K := by rw [norm_emb]; exact norm_toEuc_two hu
  have h2 : ‖z‖ ≤ ‖z - emb (toEuc u)‖ + ‖emb (toEuc u)‖ := by
    have := norm_add_le (z - emb (toEuc u)) (emb (toEuc u))
    simpa using this
  linarith

theorem cev_center (P : MvPolynomial (Fin 3) ℝ) (u : Fin 3 → ℝ) :
    cev P (emb (toEuc u)) = ((eval u P : ℝ) : ℂ) := by
  rw [cev_emb]

theorem cev_real_im (P : MvPolynomial (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    (cev P (emb x)).im = 0 := by
  rw [cev_emb]; exact Complex.ofReal_im _

/-- Mesh calibration on a probability law, in the form used below. -/
theorem calib_prob {D n : ℕ}
    (hcal : ∀ (K H m δ E : ℝ), 2 ≤ K → 1 ≤ H → 0 < m → m ≤ 1 → 0 < δ → 0 ≤ E →
      (K * H / m) ^ n * δ ≤ 1 →
      ∀ (Ω : Type v) [MeasurableSpace Ω] (μ : Measure Ω) (u : Ω → Fin 3 → ℝ),
      ENNReal.ofReal m ≤ μ univ →
      (∀ q : Fin 3 → ℤ, μ {ω | (fun i => ⌊u ω i / δ⌋) = q} ≤ ENNReal.ofReal (H * δ ^ 3)) →
      ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ D →
      (∀ᵐ ω ∂μ, (∀ i, |u ω i| ≤ K) ∧ |eval (u ω) P| ≤ E) →
      ∀ e, |P.coeff e| ≤ (K * H / m) ^ n * E)
    {K H δ E : ℝ} (hK : 2 ≤ K) (hH : 1 ≤ H) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmesh : (K * H) ^ n * δ ≤ 1) {Ω : Type v} [MeasurableSpace Ω] (lam : Measure Ω)
    [IsProbabilityMeasure lam] (u : Ω → Fin 3 → ℝ)
    (hcap : ∀ q : Fin 3 → ℤ, lam {ω | (fun i => ⌊u ω i / δ⌋) = q} ≤ ENNReal.ofReal (H * δ ^ 3))
    (P : MvPolynomial (Fin 3) ℝ) (hP : P.totalDegree ≤ D)
    (hgood : ∀ᵐ ω ∂lam, (∀ i, |u ω i| ≤ K) ∧ |eval (u ω) P| ≤ E) :
    ∀ e, |P.coeff e| ≤ (K * H) ^ n * E := by
  have h := hcal K H 1 δ E hK hH one_pos le_rfl hδ hE (by rwa [div_one]) Ω lam u
    (by rw [measure_univ, ENNReal.ofReal_one]) hcap P hP hgood
  simpa only [div_one] using h

/-! ### High curvature: the critical center -/

theorem pass_high :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (A : ℕ) (K H a δ : ℝ), 2 ≤ K → 1 ≤ H → 0 < a → a ≤ 1 → 0 < δ →
      (K * H) ^ n * δ ≤ 1 →
      ∀ (F S : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      (4 * K ^ 3 * a)⁻¹ ≤ |curvature F 3| →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (lam : Measure Ω), IsProbabilityMeasure lam →
      ∀ (u : Ω → Fin 3 → ℝ) (w : Ω → ℝ), Measurable u →
      (∀ q : Fin 3 → ℤ, lam {ω | (fun i => ⌊u ω i / δ⌋) = q} ≤ ENNReal.ofReal (H * δ ^ 3)) →
      (∀ᵐ ω ∂lam, NChart K a F S (u ω) (w ω)) →
      PassResult n A K H a F S lam u w := by
  obtain ⟨n₂, hn₂, hcal⟩ := mesh_calibration 2
  refine ⟨n₂ + 25, by omega, ?_⟩
  intro A K H a δ hK hH ha ha1 hδ hmesh F S hF hS hhigh Ω _ lam hprob u w hu hcap hgood
  have hX2 : 2 ≤ K * H := by nlinarith
  have hX1 : 1 ≤ K * H := by linarith
  have hKX : K ≤ K * H := by nlinarith
  have hK0 : 0 < K := by linarith
  set X := K * H with hXdef
  have hκpos : 0 < |curvature F 3| := lt_of_lt_of_le (by positivity) hhigh
  have hκ0 : curvature F 3 ≠ 0 := abs_pos.mp hκpos
  have hinvκ : |curvature F 3|⁻¹ ≤ 4 * K ^ 3 * a := by
    rw [inv_le_comm₀ hκpos (by positivity)]; exact hhigh
  set G := centerSignal F S with hGdef
  have hG : G.totalDegree ≤ 2 := (centerSignal_degree F S hF).trans hS
  -- pointwise facts
  have hpt : ∀ᵐ ω ∂lam, NChart K a F S (u ω) (w ω) →
      |eval (Fin.snoc (u ω) (w ω)) S - eval (u ω) G| ≤ 20 * K ^ 9 * a := by
    filter_upwards with ω hω
    obtain ⟨hu1, hF0, hFw0, hFw1, hcurv, hS0, hSw, hκ'⟩ := hω
    set c := eval (u ω) (centerPoly F)
    have hdist : |w ω - c| ≤ 4 * K ^ 4 * a := by
      rw [center_dist hF hκ0, abs_div]
      calc |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| / |curvature F 3|
          = |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| * |curvature F 3|⁻¹ := div_eq_mul_inv _ _
        _ ≤ K * (4 * K ^ 3 * a) := mul_le_mul hFw1 hinvκ (by positivity) hK0.le
        _ = 4 * K ^ 4 * a := by ring
    have hsub := signal_sub_bound hS (u ω) (w ω) c hSw hκ'
    rw [eval_centerSignal']
    refine hsub.trans ?_
    have hK1 : 1 ≤ K := by linarith
    have hK45 : K ^ 5 ≤ K ^ 9 := pow_le_pow_right₀ hK1 (by norm_num)
    have ha2 : a ^ 2 ≤ a := by nlinarith
    calc |w ω - c| * (K + K * |w ω - c|) ≤ (4 * K ^ 4 * a) * (K + K * (4 * K ^ 4 * a)) := by
          gcongr
      _ = 4 * K ^ 5 * a + 16 * K ^ 9 * a ^ 2 := by ring
      _ ≤ 4 * K ^ 9 * a + 16 * K ^ 9 * a := by gcongr
      _ = 20 * K ^ 9 * a := by ring
  have hval : ∀ᵐ ω ∂lam, (∀ i, |u ω i| ≤ K) ∧ |eval (u ω) G| ≤ 21 * K ^ 9 := by
    filter_upwards [hgood, hpt] with ω hω hω'
    refine ⟨hω.1, ?_⟩
    have h1 := hω' hω
    have h2 := hω.2.2.2.2.2.1
    have hK1 : 1 ≤ K := by linarith
    have hK9 : K ≤ K ^ 9 := le_self_pow₀ hK1 (by norm_num)
    have h3 : |eval (u ω) G| ≤ |eval (Fin.snoc (u ω) (w ω)) S| +
        |eval (Fin.snoc (u ω) (w ω)) S - eval (u ω) G| := by
      have := abs_sub_abs_le_abs_sub (eval (u ω) G) (eval (Fin.snoc (u ω) (w ω)) S)
      rw [abs_sub_comm (eval (u ω) G)] at this
      linarith
    nlinarith
  have hmesh₂ : X ^ n₂ * δ ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hX1 (by omega)) hδ.le) hmesh
  have hcoeff := calib_prob hcal hK hH hδ (by positivity) hmesh₂ lam u hcap G hG hval
  refine ⟨1, relLin G, fun _ => cev G, ∅, ?_, le_rfl, relLin_ne_zero G,
    relLin_degree (hG.trans (by norm_num)), MeasurableSet.empty, by simp, ?_⟩
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ hX1)
  · filter_upwards [hgood, hpt] with ω hω hω' _
    refine ⟨⟨(differentiable_cev G).differentiableOn, ?_, ?_, ?_⟩, ?_⟩
    · intro z _; rw [eval_relLin, sub_self]
    · intro z hz
      have hzK := norm_le_of_mem_ball_center hK hω.1 le_rfl (by simpa using hz)
      have hE0 : 0 ≤ X ^ n₂ * (21 * K ^ 9) := by positivity
      have h1 := norm_cev_le 2 G hG hE0 (by linarith) hcoeff z hzK
      have hK4 : 4 * K ≤ X ^ 3 := by
        have h4 : (4 : ℝ) ≤ X ^ 2 := by nlinarith
        calc 4 * K ≤ 4 * X := by linarith
          _ ≤ X ^ 2 * X := by nlinarith
          _ = X ^ 3 := by ring
      have hK9 : K ^ 9 ≤ X ^ 9 := pow_le_pow_left₀ (by linarith) hKX 9
      have h27 : ((2 + 1 : ℕ) : ℝ) ^ 3 * 21 ≤ X ^ 10 := by
        have : (2 : ℝ) ^ 10 ≤ X ^ 10 := pow_le_pow_left₀ (by norm_num) hX2 10
        norm_num at this ⊢; linarith
      calc ‖cev G z‖ ≤ ((2 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 2 * (X ^ n₂ * (21 * K ^ 9)) := h1
        _ = (((2 + 1 : ℕ) : ℝ) ^ 3 * 21) * (4 * K) ^ 2 * K ^ 9 * X ^ n₂ := by ring
        _ ≤ X ^ 10 * (X ^ 3) ^ 2 * X ^ 9 * X ^ n₂ := by gcongr
        _ = X ^ (n₂ + 25) := by ring
    · intro x _; exact cev_real_im G x
    · rw [cev_center, Complex.ofReal_re]
      have := hω' hω
      linarith [show 20 * K ^ 9 * a ≤ 32 * K ^ 9 * a by nlinarith [pow_pos hK0 9]]

/-! ### Zero curvature: `S = N₀ / β²` -/

theorem pass_zero :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (A : ℕ) (K H a δ : ℝ), 2 ≤ K → 1 ≤ H → 0 < a → a ≤ 1 → 0 < δ →
      (K * H) ^ n * δ ≤ 1 →
      ∀ (F S : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      curvature F 3 = 0 →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (lam : Measure Ω), IsProbabilityMeasure lam →
      ∀ (u : Ω → Fin 3 → ℝ) (w : Ω → ℝ), Measurable u →
      (∀ q : Fin 3 → ℤ, lam {ω | (fun i => ⌊u ω i / δ⌋) = q} ≤ ENNReal.ofReal (H * δ ^ 3)) →
      (∀ᵐ ω ∂lam, NChart K a F S (u ω) (w ω)) →
      PassResult n A K H a F S lam u w := by
  obtain ⟨n₁, hn₁, hcal₁⟩ := mesh_calibration 1
  obtain ⟨n₄, hn₄, hcal₄⟩ := mesh_calibration 4
  refine ⟨n₁ + n₄ + 60, by omega, ?_⟩
  intro A K H a δ hK hH ha ha1 hδ hmesh F S hF hS hκ Ω _ lam hprob u w hu hcap hgood
  have hX2 : 2 ≤ K * H := by nlinarith
  have hX1 : 1 ≤ K * H := by linarith
  have hKX : K ≤ K * H := by nlinarith
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  set X := K * H with hXdef
  set β := restrictBase (pderiv 3 F) with hβdef
  set N₀ := erN0 F S with hN₀def
  have hβdeg : β.totalDegree ≤ 1 := er_totalDegree_restrict_deriv F hF
  have hNdeg : N₀.totalDegree ≤ 4 := erN0_degree F S hF hS
  -- pointwise facts
  have hpt : ∀ ω, NChart K a F S (u ω) (w ω) →
      (K⁻¹ ≤ |eval (u ω) β| ∧ |eval (u ω) β| ≤ K) ∧ |eval (u ω) N₀| ≤ 3 * K ^ 7 ∧
      |eval (Fin.snoc (u ω) (w ω)) S - eval (u ω) N₀ / eval (u ω) β ^ 2| ≤ 2 * K ^ 5 * a := by
    intro ω hω
    obtain ⟨hu1, hF0, hFw0, hFw1, hcurv, hS0, hSw, hκ'⟩ := hω
    have hder : eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) = eval (u ω) β := by
      rw [quad_deriv hF, hκ, zero_mul, add_zero]
    rw [hder] at hFw0 hFw1
    set bu := eval (u ω) β with hbu
    have hbu0 : bu ≠ 0 := by
      intro h; rw [h, abs_zero] at hFw0
      exact absurd hFw0 (not_le.mpr (by positivity))
    have hbupos : 0 < |bu| := abs_pos.mpr hbu0
    have hinv : |bu|⁻¹ ≤ K := by rw [inv_le_comm₀ hbupos hK0]; exact hFw0
    set φ := w ω - eval (Fin.snoc (u ω) (w ω)) F / bu with hφ
    have hroot : eval (Fin.snoc (u ω) φ) F = 0 := by
      rw [quad_eval hF, hκ]
      have h1 := quad_eval hF (u ω) (w ω)
      rw [hκ] at h1
      rw [hφ, h1]
      field_simp
      ring
    have hdist : |w ω - φ| ≤ K ^ 2 * a := by
      rw [hφ, sub_sub_cancel, abs_div]
      calc |eval (Fin.snoc (u ω) (w ω)) F| / |bu| = |eval (Fin.snoc (u ω) (w ω)) F| * |bu|⁻¹ :=
            div_eq_mul_inv _ _
        _ ≤ (K * a) * K := mul_le_mul hF0 hinv (by positivity) (by positivity)
        _ = K ^ 2 * a := by ring
    have hsub := signal_sub_bound hS (u ω) (w ω) φ hSw hκ'
    have hval := zero_branch_value hF hS hκ (u ω) φ hroot
    have hSφ : eval (Fin.snoc (u ω) φ) S = eval (u ω) N₀ / bu ^ 2 := by
      rw [hval]; field_simp; try rfl
    have ha2 : a ^ 2 ≤ a := by nlinarith
    have hK35 : K ^ 3 ≤ K ^ 5 := pow_le_pow_right₀ hK1 (by norm_num)
    have herr : |eval (Fin.snoc (u ω) (w ω)) S - eval (Fin.snoc (u ω) φ) S| ≤ 2 * K ^ 5 * a := by
      refine hsub.trans ?_
      calc |w ω - φ| * (K + K * |w ω - φ|) ≤ (K ^ 2 * a) * (K + K * (K ^ 2 * a)) := by gcongr
        _ = K ^ 3 * a + K ^ 5 * a ^ 2 := by ring
        _ ≤ K ^ 5 * a + K ^ 5 * a := by gcongr
        _ = 2 * K ^ 5 * a := by ring
    refine ⟨⟨hFw0, hFw1⟩, ?_, by rw [← hSφ]; exact herr⟩
    rw [hval, abs_mul, abs_pow]
    have hSφb : |eval (Fin.snoc (u ω) φ) S| ≤ 3 * K ^ 5 := by
      have h1 : |eval (Fin.snoc (u ω) φ) S| ≤ |eval (Fin.snoc (u ω) (w ω)) S| +
          |eval (Fin.snoc (u ω) (w ω)) S - eval (Fin.snoc (u ω) φ) S| := by
        have := abs_sub_abs_le_abs_sub (eval (Fin.snoc (u ω) φ) S) (eval (Fin.snoc (u ω) (w ω)) S)
        rw [abs_sub_comm (eval (Fin.snoc (u ω) φ) S)] at this
        linarith
      have hK5 : K ≤ K ^ 5 := le_self_pow₀ hK1 (by norm_num)
      nlinarith
    calc |bu| ^ 2 * |eval (Fin.snoc (u ω) φ) S| ≤ K ^ 2 * (3 * K ^ 5) := by gcongr
      _ = 3 * K ^ 7 := by ring
  have hmesh₁ : X ^ n₁ * δ ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hX1 (by omega)) hδ.le) hmesh
  have hmesh₄ : X ^ n₄ * δ ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hX1 (by omega)) hδ.le) hmesh
  have hcβ := calib_prob (E := K) hcal₁ hK hH hδ hK0.le hmesh₁ lam u hcap β hβdeg
    (by filter_upwards [hgood] with ω hω using ⟨hω.1, ((hpt ω hω).1.2)⟩)
  have hcN := calib_prob (E := 3 * K ^ 7) hcal₄ hK hH hδ (by positivity) hmesh₄ lam u hcap N₀
    hNdeg
    (by filter_upwards [hgood] with ω hω using ⟨hω.1, ((hpt ω hω).2.1)⟩)
  -- the radius
  set ρ : ℝ := (X ^ (n₁ + 12))⁻¹ with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hX1)
  have hlow : ∀ ω, NChart K a F S (u ω) (w ω) → ∀ z ∈ ball (emb (toEuc (u ω))) (4 * ρ),
      (2 * K)⁻¹ ≤ ‖cev β z‖ := by
    intro ω hω z hz
    have hzK := norm_le_of_mem_ball_center hK hω.1 hρ1 hz
    have hcK : ‖emb (toEuc (u ω))‖ ≤ 4 * K := by
      rw [norm_emb]; have := norm_toEuc_two hω.1; linarith
    have hE0 : 0 ≤ X ^ n₁ * K := by positivity
    have hlip := cev_lipschitz 1 β hβdeg hE0 (by linarith) hcβ z (emb (toEuc (u ω))) hzK hcK
    rw [mem_ball, dist_eq_norm] at hz
    rw [cev_center] at hlip
    have hb := (hpt ω hω).1.1
    have hstep : 4 * (((1 + 1 : ℕ) : ℝ) ^ 3 * (2 * (4 * K)) ^ 1 * (X ^ n₁ * K)) / (4 * K) *
        ‖z - emb (toEuc (u ω))‖ ≤ (2 * K)⁻¹ := by
      have h1 : 4 * (((1 + 1 : ℕ) : ℝ) ^ 3 * (2 * (4 * K)) ^ 1 * (X ^ n₁ * K)) / (4 * K) =
          64 * X ^ n₁ * K := by field_simp; ring
      rw [h1]
      have hX9 : (512 : ℝ) ≤ X ^ 9 := by
        have : (2 : ℝ) ^ 9 ≤ X ^ 9 := pow_le_pow_left₀ (by norm_num) hX2 9
        norm_num at this ⊢; linarith
      have hK2 : K ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hK0.le hKX 2
      have hX3 : (512 : ℝ) * K ^ 2 * X ^ n₁ ≤ X ^ (n₁ + 12) := by
        calc (512 : ℝ) * K ^ 2 * X ^ n₁ ≤ X ^ 9 * X ^ 2 * X ^ n₁ := by gcongr
          _ = X ^ (n₁ + 11) := by ring
          _ ≤ X ^ (n₁ + 12) := pow_le_pow_right₀ hX1 (by omega)
      have hρX : 4 * ρ * (64 * X ^ n₁ * K) ≤ (2 * K)⁻¹ := by
        rw [hρdef, show 4 * (X ^ (n₁ + 12))⁻¹ * (64 * X ^ n₁ * K) =
          256 * X ^ n₁ * K / X ^ (n₁ + 12) by field_simp; ring, div_le_iff₀ (by positivity)]
        calc 256 * X ^ n₁ * K = (2 * K)⁻¹ * (512 * K ^ 2 * X ^ n₁) := by field_simp; ring
          _ ≤ (2 * K)⁻¹ * X ^ (n₁ + 12) := by gcongr
      calc 64 * X ^ n₁ * K * ‖z - emb (toEuc (u ω))‖ ≤ 64 * X ^ n₁ * K * (4 * ρ) := by
            gcongr
        _ = 4 * ρ * (64 * X ^ n₁ * K) := by ring
        _ ≤ (2 * K)⁻¹ := hρX
    have htri : ‖((eval (u ω) β : ℝ) : ℂ)‖ ≤ ‖cev β z‖ + ‖cev β z - ((eval (u ω) β : ℝ) : ℂ)‖ := by
      have := norm_add_le (cev β z) (((eval (u ω) β : ℝ) : ℂ) - cev β z)
      rw [norm_sub_rev] at this
      simpa using this
    rw [Complex.norm_real, Real.norm_eq_abs] at htri
    have hKinv : (2 * K)⁻¹ + (2 * K)⁻¹ = K⁻¹ := by field_simp; ring
    linarith [hlip.trans hstep]
  -- a point with the chart bounds
  obtain ⟨ω₀, hω₀⟩ := hgood.exists
  have hR0 : cev β (emb (toEuc (u ω₀))) ≠ 0 := by
    intro h
    have := hlow ω₀ hω₀ (emb (toEuc (u ω₀))) (mem_ball_self (by positivity))
    rw [h, norm_zero] at this
    exact absurd this (not_le.mpr (by positivity))
  refine ⟨ρ, relZero β N₀, fun _ z => cev N₀ z / cev β z ^ 2, ∅, ?_, hρ1,
    relZero_ne_zero β N₀ _ hR0, relZero_degree hβdeg hNdeg, MeasurableSet.empty, by simp, ?_⟩
  · rw [hρdef]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hX1 (by omega))
  · filter_upwards [hgood] with ω hω _
    have hne : ∀ z ∈ ball (emb (toEuc (u ω))) (4 * ρ), cev β z ≠ 0 := by
      intro z hz h
      have := hlow ω hω z hz
      rw [h, norm_zero] at this
      exact absurd this (not_le.mpr (by positivity))
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro z hz
      have hb2 : DifferentiableAt ℂ (fun y => cev β y * cev β y) z :=
        (differentiable_cev β z).fun_mul (differentiable_cev β z)
      have hb2' : cev β z * cev β z ≠ 0 := mul_ne_zero (hne z hz) (hne z hz)
      have h2 : DifferentiableAt ℂ (fun y => cev N₀ y * (cev β y * cev β y)⁻¹) z :=
        (differentiable_cev N₀ z).fun_mul (hb2.fun_inv hb2')
      simpa only [div_eq_mul_inv, sq] using h2.differentiableWithinAt
    · intro z hz
      rw [eval_relZero]
      field_simp [hne z hz]
      ring
    · intro z hz
      have hzK := norm_le_of_mem_ball_center hK hω.1 hρ1 hz
      have hE0 : 0 ≤ X ^ n₄ * (3 * K ^ 7) := by positivity
      have h1 := norm_cev_le 4 N₀ hNdeg hE0 (by linarith) hcN z hzK
      have h2 := hlow ω hω z hz
      have h2' : 0 < ‖cev β z‖ := lt_of_lt_of_le (by positivity) h2
      rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
      have hsq : ((2 * K)⁻¹) ^ 2 ≤ ‖cev β z‖ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      have hK13 : K ^ 13 ≤ X ^ 13 := pow_le_pow_left₀ hK0.le hKX 13
      have hX19 : (384000 : ℝ) ≤ X ^ 19 := by
        have : (2 : ℝ) ^ 19 ≤ X ^ 19 := pow_le_pow_left₀ (by norm_num) hX2 19
        norm_num at this ⊢; linarith
      have hbound : ((4 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 4 * (X ^ n₄ * (3 * K ^ 7)) ≤
          X ^ (n₁ + n₄ + 60) * ((2 * K)⁻¹) ^ 2 := by
        rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        calc ((4 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 4 * (X ^ n₄ * (3 * K ^ 7)) * (2 * K) ^ 2 =
            384000 * K ^ 13 * X ^ n₄ := by push_cast; ring
          _ ≤ X ^ 19 * X ^ 13 * X ^ n₄ := by gcongr
          _ = X ^ (n₄ + 32) := by ring
          _ ≤ X ^ (n₁ + n₄ + 60) := pow_le_pow_right₀ hX1 (by omega)
      calc ‖cev N₀ z‖ ≤ ((4 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 4 * (X ^ n₄ * (3 * K ^ 7)) := h1
        _ ≤ X ^ (n₁ + n₄ + 60) * ((2 * K)⁻¹) ^ 2 := hbound
        _ ≤ X ^ (n₁ + n₄ + 60) * ‖cev β z‖ ^ 2 := by gcongr
    · intro x _
      beta_reduce
      rw [cev_emb, cev_emb]
      rw [show ((eval (fun i => x i) N₀ : ℝ) : ℂ) / ((eval (fun i => x i) β : ℝ) : ℂ) ^ 2 =
        (((eval (fun i => x i) N₀) / (eval (fun i => x i) β) ^ 2 : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_im _
    · have h := (hpt ω hω).2.2
      beta_reduce
      rw [cev_center, cev_center]
      rw [show ((eval (u ω) N₀ : ℝ) : ℂ) / ((eval (u ω) β : ℝ) : ℂ) ^ 2 =
        (((eval (u ω) N₀) / (eval (u ω) β) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
      have hK59 : K ^ 5 ≤ K ^ 9 := pow_le_pow_right₀ hK1 (by norm_num)
      have h3 : 2 * K ^ 5 * a ≤ 32 * K ^ 9 * a := by
        have := mul_le_mul_of_nonneg_right hK59 ha.le
        nlinarith [pow_pos hK0 5]
      linarith

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
