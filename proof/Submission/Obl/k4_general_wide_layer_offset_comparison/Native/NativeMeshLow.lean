-- Adapted from this LOT tree, obligation o254, branch x0898, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/NativeMeshLow.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0864, commit abc1113588ce6b9e412a59326ea88392111ccb7e,
   Submission/Obl/k4_finite_projected_horizontal_candidates/NativeMeshLow.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.NativeMeshSheets

/-!
# Native sheets from finite mesh caps: low curvature

Below curvature `1/(4K³a)` the discriminant `Δ` is at least `1/(2K²)` at the points, and the
native signal on the branch selected by the sign `σ` of `∂_w F` is
`M + σ B √Δ` (accepted o176). The complex sheet `lowSheet` uses the principal square root,
holomorphic where `Re Δ > 0`.

* If the coefficients of `B` are at most a power `T` of `K H`, then `M` is bounded at the points
  and everything is calibrated.
* Otherwise the thin slab `|B| ≤ b (KH)^(-c)` is discarded (`slab_mass`); off the slab the two
  branch values differ by `≳ b`, their product `N = M² - B² Δ` is `≲ b`, and
  `small_branch_bound` keeps the point's branch bounded on its whole ball.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

/-! ### The complex square root -/

theorem norm_csqrt_sq (x : ℂ) : ‖Complex.sqrt x‖ ^ 2 = ‖x‖ := by
  rw [← norm_pow, Submission.Obl.k4_stable_quadratic_hidden_sheets.sqrt_sq']

theorem norm_csqrt_le (x : ℂ) : ‖Complex.sqrt x‖ ≤ 1 + ‖x‖ := by
  have h := norm_csqrt_sq x
  by_contra hc
  rw [not_le] at hc
  have h0 : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith

theorem csqrt_ofReal {x : ℝ} (hx : 0 ≤ x) : Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
  rw [Complex.sqrt_of_nonneg (Complex.zero_le_real.mpr hx), Complex.ofReal_re]

/-! ### The low-curvature sheet -/

/-- The native sheet `M + σ B √Δ` of the branch `s`. -/
def lowSheet (F S : MvPolynomial (Fin 4) ℝ) (s : Bool) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  cev (erM F S) z + (bsign s : ℂ) * cev (erB F S) z * Complex.sqrt (cev (erDisc F) z)

theorem bsign_not (s : Bool) : bsign (!s) = -bsign s := by cases s <;> simp [bsign]

theorem cev_erN (F S : MvPolynomial (Fin 4) ℝ) (z : EuclideanSpace ℂ (Fin 3)) :
    cev (erN F S) z = cev (erM F S) z ^ 2 - cev (erB F S) z ^ 2 * cev (erDisc F) z := by
  simp [erN, cev, eval₂_sub, eval₂_pow, eval₂_mul]

theorem lowSheet_rel (F S : MvPolynomial (Fin 4) ℝ) (s : Bool) (z : EuclideanSpace ℂ (Fin 3)) :
    eval (Fin.snoc (fun i : Fin 3 => z i) (lowSheet F S s z)) (relQuad (erM F S) (erN F S)) = 0 := by
  rw [eval_relQuad, cev_erN]
  have hsq := Submission.Obl.k4_stable_quadratic_hidden_sheets.sqrt_sq' (cev (erDisc F) z)
  have hs2 : ((bsign s : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast bsign_sq s
  unfold lowSheet
  linear_combination (cev (erB F S) z ^ 2 * ((bsign s : ℝ) : ℂ) ^ 2) * hsq +
    (cev (erB F S) z ^ 2 * cev (erDisc F) z) * hs2

theorem lowSheet_mul (F S : MvPolynomial (Fin 4) ℝ) (s : Bool) (z : EuclideanSpace ℂ (Fin 3)) :
    lowSheet F S s z * lowSheet F S (!s) z = cev (erN F S) z := by
  rw [cev_erN]
  have hsq := Submission.Obl.k4_stable_quadratic_hidden_sheets.sqrt_sq' (cev (erDisc F) z)
  have hs2 : ((bsign s : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast bsign_sq s
  unfold lowSheet
  rw [bsign_not]
  push_cast
  linear_combination (-(cev (erB F S) z ^ 2 * ((bsign s : ℝ) : ℂ) ^ 2)) * hsq -
    (cev (erB F S) z ^ 2 * cev (erDisc F) z) * hs2

theorem lowSheet_sub (F S : MvPolynomial (Fin 4) ℝ) (s : Bool) (z : EuclideanSpace ℂ (Fin 3)) :
    lowSheet F S s z - lowSheet F S (!s) z =
      2 * (bsign s : ℂ) * cev (erB F S) z * Complex.sqrt (cev (erDisc F) z) := by
  unfold lowSheet
  rw [bsign_not]
  push_cast
  ring

theorem lowSheet_differentiableAt (F S : MvPolynomial (Fin 4) ℝ) (s : Bool)
    {z : EuclideanSpace ℂ (Fin 3)} (hz : 0 < (cev (erDisc F) z).re) :
    DifferentiableAt ℂ (lowSheet F S s) z := by
  have hslit : cev (erDisc F) z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl hz)
  have h1 : DifferentiableAt ℂ (fun y => Complex.sqrt (cev (erDisc F) y)) z :=
    DifferentiableAt.comp (g := Complex.sqrt) z (Complex.differentiableAt_sqrt hslit)
      (differentiable_cev (erDisc F) z)
  unfold lowSheet
  exact (differentiable_cev _ z).add
    (((differentiable_cev _ z).const_mul _).mul h1)

theorem lowSheet_emb (F S : MvPolynomial (Fin 4) ℝ) (s : Bool) (x : EuclideanSpace ℝ (Fin 3))
    (hx : 0 ≤ eval (fun i => x i) (erDisc F)) :
    lowSheet F S s (emb x) = ((eval (fun i => x i) (erM F S) + bsign s *
      eval (fun i => x i) (erB F S) * Real.sqrt (eval (fun i => x i) (erDisc F)) : ℝ) : ℂ) := by
  unfold lowSheet
  rw [cev_emb, cev_emb, cev_emb, csqrt_ofReal hx]
  push_cast
  ring

/-! ### Pointwise facts -/

set_option maxHeartbeats 1000000 in
theorem low_point {F S : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (hS : S.totalDegree ≤ 2) {K a : ℝ} (hK : 2 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1)
    (hκ : curvature F 3 ≠ 0) (hlow : |curvature F 3| < (4 * K ^ 3 * a)⁻¹)
    {u : Fin 3 → ℝ} {w : ℝ} (hc : NChart K a F S u w) :
    (2 * K ^ 2)⁻¹ ≤ eval u (erDisc F) ∧ eval u (erDisc F) ≤ 2 * K ^ 2 ∧
    |eval (Fin.snoc u w) S - (eval u (erM F S) + bsign (branch F u w) * eval u (erB F S) *
        Real.sqrt (eval u (erDisc F)))| ≤ 6 * K ^ 5 * a ∧
    |eval u (erM F S) + bsign (branch F u w) * eval u (erB F S) *
        Real.sqrt (eval u (erDisc F))| ≤ 7 * K ^ 5 := by
  obtain ⟨hu1, hF0, hFw0, hFw1, hcurv, hS0, hSw, hκ'⟩ := hc
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hD := erDisc_eval_point hF u w
  set d := eval (Fin.snoc u w) (pderiv 3 F) with hd
  set κ := curvature F 3 with hκdef
  -- the size of `2 κ F`
  have hκF : |2 * κ * eval (Fin.snoc u w) F| ≤ (2 * K ^ 2)⁻¹ := by
    rw [abs_mul, abs_mul, abs_two]
    calc 2 * |κ| * |eval (Fin.snoc u w) F| ≤ 2 * (4 * K ^ 3 * a)⁻¹ * (K * a) := by gcongr
      _ = (2 * K ^ 2)⁻¹ := by field_simp; ring
  have hd2 : K⁻¹ ^ 2 ≤ d ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hFw0 2
    rwa [sq_abs] at this
  have hd2' : d ^ 2 ≤ K ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hFw1 2
    rwa [sq_abs] at this
  have hinv : K⁻¹ ^ 2 = 2 * (2 * K ^ 2)⁻¹ := by field_simp; try ring
  have hΔlo : (2 * K ^ 2)⁻¹ ≤ eval u (erDisc F) := by
    rw [hD]
    have := le_abs_self (2 * κ * eval (Fin.snoc u w) F)
    linarith
  have hΔhi : eval u (erDisc F) ≤ 2 * K ^ 2 := by
    rw [hD]
    have := neg_abs_le (2 * κ * eval (Fin.snoc u w) F)
    have hsmall : (2 * K ^ 2)⁻¹ ≤ K ^ 2 := by
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      have : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK1
      calc (K ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
        _ ≤ 2 * K ^ 2 := by nlinarith
    linarith
  refine ⟨hΔlo, hΔhi, ?_⟩
  -- the exact root on the branch of the point
  set σ := bsign (branch F u w) with hσ
  have hσ2 : σ ^ 2 = 1 := bsign_sq _
  have hd0 : d ≠ 0 := by
    intro h; rw [h, abs_zero] at hFw0; exact absurd hFw0 (not_le.mpr (by positivity))
  have hσd : 0 < σ * d := bsign_branch_pos hd0
  set r := Real.sqrt (eval u (erDisc F)) with hr
  have hrpos : 0 < r := Real.sqrt_pos.2 (lt_of_lt_of_le (by positivity) hΔlo)
  have hr2 : r ^ 2 = eval u (erDisc F) := Real.sq_sqrt (le_trans (by positivity) hΔlo)
  set β := eval u (restrictBase (pderiv 3 F)) with hβ
  set φ := (σ * r - β) / κ with hφ
  have hFwφ : eval (Fin.snoc u φ) (pderiv 3 F) = σ * r := by
    rw [quad_deriv hF, hφ]; field_simp; ring
  have hroot : eval (Fin.snoc u φ) F = 0 := by
    have h1 := erDisc_eval_point hF u φ
    rw [hFwφ, mul_pow, hσ2, one_mul, hr2] at h1
    have h2 : 2 * κ * eval (Fin.snoc u φ) F = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero hκ)
    · exact h
  have hsign : 0 < eval (Fin.snoc u w) (pderiv 3 F) * eval (Fin.snoc u φ) (pderiv 3 F) := by
    rw [hFwφ, ← hd]
    have : d * (σ * r) = (σ * d) * r := by ring
    rw [this]; exact mul_pos hσd hrpos
  have hdist : |w - φ| ≤ 2 * K ^ 2 * a := abs_sub_root_le hF hK0 u w φ hroot hF0 hFw0 hsign
  have hval := (low_branch_value hF hS hκ u φ hroot).2
  rw [hFwφ] at hval
  have hsub := signal_sub_bound hS u w φ hSw hκ'
  have ha2 : a ^ 2 ≤ a := by nlinarith
  have hK35 : K ^ 3 ≤ K ^ 5 := pow_le_pow_right₀ hK1 (by norm_num)
  have herr : |eval (Fin.snoc u w) S - eval (Fin.snoc u φ) S| ≤ 6 * K ^ 5 * a := by
    refine hsub.trans ?_
    calc |w - φ| * (K + K * |w - φ|) ≤ (2 * K ^ 2 * a) * (K + K * (2 * K ^ 2 * a)) := by gcongr
      _ = 2 * K ^ 3 * a + 4 * K ^ 5 * a ^ 2 := by ring
      _ ≤ 2 * K ^ 5 * a + 4 * K ^ 5 * a := by gcongr
      _ = 6 * K ^ 5 * a := by ring
  have hS' : eval (Fin.snoc u φ) S = eval u (erM F S) + σ * eval u (erB F S) * r := by
    rw [hval]; ring
  rw [← hS']
  refine ⟨herr, ?_⟩
  have hK5 : K ≤ K ^ 5 := le_self_pow₀ hK1 (by norm_num)
  have h1 : |eval (Fin.snoc u φ) S| ≤ |eval (Fin.snoc u w) S| +
      |eval (Fin.snoc u w) S - eval (Fin.snoc u φ) S| := by
    have := abs_sub_abs_le_abs_sub (eval (Fin.snoc u φ) S) (eval (Fin.snoc u w) S)
    rw [abs_sub_comm (eval (Fin.snoc u φ) S)] at this
    linarith
  calc |eval (Fin.snoc u φ) S| ≤ |eval (Fin.snoc u w) S| +
        |eval (Fin.snoc u w) S - eval (Fin.snoc u φ) S| := h1
    _ ≤ K + 6 * K ^ 5 * a := add_le_add hS0 herr
    _ ≤ K ^ 5 + 6 * K ^ 5 * 1 := by gcongr
    _ = 7 * K ^ 5 := by ring

/-! ### The low-curvature pass -/

theorem sub_re_le (x y : ℂ) : x.re - ‖x - y‖ ≤ y.re := by
  have := Complex.abs_re_le_norm (x - y)
  rw [Complex.sub_re] at this
  have := le_abs_self (x.re - y.re)
  linarith

theorem bound_pow {K X c : ℝ} (i j m : ℕ) (hK0 : 0 ≤ K) (hKX : K ≤ X) (hX2 : 2 ≤ X)
    (hc0 : 0 ≤ c) (hc : c ≤ 2 ^ m) : c * K ^ i * X ^ j ≤ X ^ (m + i + j) := by
  have h1 : c ≤ X ^ m := hc.trans (pow_le_pow_left₀ (by norm_num) hX2 m)
  have h2 : K ^ i ≤ X ^ i := pow_le_pow_left₀ hK0 hKX i
  have hX0 : 0 ≤ X := by linarith
  calc c * K ^ i * X ^ j ≤ X ^ m * X ^ i * X ^ j := by gcongr
    _ = X ^ (m + i + j) := by ring

set_option maxHeartbeats 8000000 in
theorem pass_low :
    ∃ α β : ℕ, 1 ≤ β ∧ ∀ (A : ℕ) (K H a δ : ℝ), 2 ≤ K → 1 ≤ H → 0 < a → a ≤ 1 → 0 < δ →
      (K * H) ^ (α * A + β) * δ ≤ 1 →
      ∀ (F S : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      curvature F 3 ≠ 0 → |curvature F 3| < (4 * K ^ 3 * a)⁻¹ →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (lam : Measure Ω), IsProbabilityMeasure lam →
      ∀ (u : Ω → Fin 3 → ℝ) (w : Ω → ℝ), Measurable u →
      (∀ q : Fin 3 → ℤ, lam {ω | (fun i => ⌊u ω i / δ⌋) = q} ≤ ENNReal.ofReal (H * δ ^ 3)) →
      (∀ᵐ ω ∂lam, NChart K a F S (u ω) (w ω)) →
      PassResult (α * A + β) A K H a F S lam u w := by
  obtain ⟨n₂, hn₂, hcal₂⟩ := mesh_calibration 2
  obtain ⟨n₄, hn₄, hcal₄⟩ := mesh_calibration 4
  obtain ⟨n₁', hn₁', hslab₀⟩ := slab_mass
  refine ⟨5 * n₁', n₂ + n₄ + 5 * n₁' + 204, by omega, ?_⟩
  intro A K H a δ hK hH ha ha1 hδ hmesh F S hF hS hκ hlow Ω _ lam hprob u w hu hcap hgood
  obtain ⟨cs, hcs⟩ : ∃ cs : ℕ, cs = n₁' * (A + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨ns, hns'⟩ : ∃ ns : ℕ, ns = n₁' * (A + 1) := ⟨_, rfl⟩
  have hn_eq : 5 * n₁' * A + (n₂ + n₄ + 5 * n₁' + 204) = n₂ + n₄ + ns + 4 * cs + 200 := by
    rw [hcs, hns']; ring
  rw [hn_eq] at hmesh ⊢
  clear hn_eq
  have hslab := hslab₀ A
  clear hslab₀
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKH2 : 2 ≤ K * H := by nlinarith
  have hKHK : K ≤ K * H := by nlinarith
  obtain ⟨X, hXdef⟩ : ∃ X, X = K * H := ⟨_, rfl⟩
  rw [← hXdef] at hKH2 hKHK hmesh
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hXmono : ∀ i j : ℕ, i ≤ j → X ^ i ≤ X ^ j := fun i j h => pow_le_pow_right₀ hX1 h
  have hmeshk : ∀ k : ℕ, k ≤ n₂ + n₄ + ns + 4 * cs + 200 → (K * H) ^ k * δ ≤ 1 := by
    intro k hk
    rw [← hXdef]
    exact le_trans (mul_le_mul_of_nonneg_right (hXmono _ _ hk) hδ.le) hmesh
  have hΔdeg := erDisc_degree2 F hF
  have hMdeg := erM_degree2 F S hF hS
  have hBdeg := erB_degree1 F S hF hS
  have hNdeg := erN_degree F S hF hS
  have hpt := fun ω (hω : NChart K a F S (u ω) (w ω)) => low_point hF hS hK ha ha1 hκ hlow hω
  have hcenter : ∀ ω, NChart K a F S (u ω) (w ω) → ‖emb (toEuc (u ω))‖ ≤ 4 * K := by
    intro ω hω
    rw [norm_emb]; have := norm_toEuc_two hω.1; linarith
  -- calibration of the discriminant
  have hΔval : ∀ᵐ ω ∂lam, (∀ i, |u ω i| ≤ K) ∧ |eval (u ω) (erDisc F)| ≤ 2 * K ^ 2 := by
    filter_upwards [hgood] with ω hω
    refine ⟨hω.1, ?_⟩
    obtain ⟨h1, h2, -, -⟩ := hpt ω hω
    have h0 : 0 ≤ eval (u ω) (erDisc F) := le_trans (by positivity) h1
    rw [abs_of_nonneg h0]; exact h2
  have hcΔ : ∀ e, |(erDisc F).coeff e| ≤ X ^ n₂ * (2 * K ^ 2) := by
    have h := calib_prob (E := 2 * K ^ 2) hcal₂ hK hH hδ (by positivity) (hmeshk n₂ (by omega))
      lam u hcap (erDisc F) hΔdeg hΔval
    rw [← hXdef] at h; exact h
  -- the radius
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (X ^ (n₂ + cs + 30))⁻¹ := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hX1)
  have hρX : ρ * X ^ (n₂ + cs + 30) = 1 := by rw [hρdef]; exact inv_mul_cancel₀ (by positivity)
  -- the discriminant on the balls
  have hball : ∀ ω, NChart K a F S (u ω) (w ω) → ∀ z ∈ ball (emb (toEuc (u ω))) (4 * ρ),
      (4 * K ^ 2)⁻¹ ≤ (cev (erDisc F) z).re ∧ ‖cev (erDisc F) z‖ ≤ 864 * K ^ 4 * X ^ n₂ := by
    intro ω hω z hz
    have hzK := norm_le_of_mem_ball_center hK hω.1 hρ1 hz
    have hcK := hcenter ω hω
    have hE0 : 0 ≤ X ^ n₂ * (2 * K ^ 2) := by positivity
    constructor
    · have hlip := cev_lipschitz 2 (erDisc F) hΔdeg hE0 (by linarith) hcΔ z
        (emb (toEuc (u ω))) hzK hcK
      have hconst : 4 * (((2 + 1 : ℕ) : ℝ) ^ 3 * (2 * (4 * K)) ^ 2 * (X ^ n₂ * (2 * K ^ 2))) /
          (4 * K) = 3456 * K ^ 3 * X ^ n₂ := by push_cast; field_simp; ring
      rw [hconst, cev_center] at hlip
      rw [mem_ball, dist_eq_norm] at hz
      have h55 : 55296 * K ^ 5 * X ^ n₂ ≤ X ^ (n₂ + cs + 30) :=
        (bound_pow 5 n₂ 16 hK0.le hKHK hKH2 (by norm_num) (by norm_num)).trans
          (hXmono _ _ (by omega))
      have hsmall : ‖cev (erDisc F) z - ((eval (u ω) (erDisc F) : ℝ) : ℂ)‖ ≤ (4 * K ^ 2)⁻¹ := by
        refine hlip.trans ?_
        have h1 : 3456 * K ^ 3 * X ^ n₂ * ‖z - emb (toEuc (u ω))‖ ≤
            3456 * K ^ 3 * X ^ n₂ * (4 * ρ) := mul_le_mul_of_nonneg_left hz.le (by positivity)
        refine h1.trans ?_
        rw [← one_div, le_div_iff₀ (by positivity)]
        calc 3456 * K ^ 3 * X ^ n₂ * (4 * ρ) * (4 * K ^ 2) = (55296 * K ^ 5 * X ^ n₂) * ρ := by
              ring
          _ ≤ X ^ (n₂ + cs + 30) * ρ := mul_le_mul_of_nonneg_right h55 hρ0.le
          _ = 1 := by rw [mul_comm]; exact hρX
      obtain ⟨hlo, -, -, -⟩ := hpt ω hω
      have hre := sub_re_le (((eval (u ω) (erDisc F) : ℝ) : ℂ)) (cev (erDisc F) z)
      rw [Complex.ofReal_re, norm_sub_rev] at hre
      have hinv : (4 * K ^ 2)⁻¹ = (2 * K ^ 2)⁻¹ / 2 := by
        rw [show 4 * K ^ 2 = 2 * (2 * K ^ 2) by ring, mul_inv]; ring
      linarith
    · have h := norm_cev_le 2 (erDisc F) hΔdeg hE0 (by linarith) hcΔ z hzK
      calc ‖cev (erDisc F) z‖ ≤ ((2 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 2 * (X ^ n₂ * (2 * K ^ 2)) := h
        _ = 864 * K ^ 4 * X ^ n₂ := by push_cast; ring
  -- assembly from a sup bound
  have key : ∀ E : Set Ω, MeasurableSet E → lam E ≤ ENNReal.ofReal ((X ^ A)⁻¹) →
      (∀ ω, NChart K a F S (u ω) (w ω) → ω ∉ E → ∀ z ∈ ball (emb (toEuc (u ω))) (4 * ρ),
        ‖lowSheet F S (branch F (u ω) (w ω)) z‖ ≤ X ^ (n₂ + n₄ + ns + 4 * cs + 200)) →
      PassResult (n₂ + n₄ + ns + 4 * cs + 200) A K H a F S lam u w := by
    intro E hEm hEmass hsup
    refine ⟨ρ, relQuad (erM F S) (erN F S), lowSheet F S, E, ?_, hρ1, relQuad_ne_zero _ _,
      relQuad_degree hMdeg hNdeg, hEm, ?_, ?_⟩
    · rw [← hXdef, hρdef]; exact inv_anti₀ (by positivity) (hXmono _ _ (by omega))
    · rw [← hXdef]; exact hEmass
    · rw [← hXdef]
      filter_upwards [hgood] with ω hω hωE
      refine ⟨⟨?_, ?_, hsup ω hω hωE, ?_⟩, ?_⟩
      · intro z hz
        have hre := (hball ω hω z hz).1
        exact (lowSheet_differentiableAt F S _
          (lt_of_lt_of_le (by positivity) hre)).differentiableWithinAt
      · intro z _; exact lowSheet_rel F S _ z
      · intro x hx
        have hxb : emb x ∈ ball (emb (toEuc (u ω))) (4 * ρ) := by
          rw [mem_ball, dist_emb, dist_eq_norm]; exact hx
        have hre := (hball ω hω (emb x) hxb).1
        rw [cev_emb, Complex.ofReal_re] at hre
        rw [lowSheet_emb F S _ x (le_trans (by positivity) hre)]
        exact Complex.ofReal_im _
      · obtain ⟨hlo, -, herr, -⟩ := hpt ω hω
        have hx0 : 0 ≤ eval (fun i => (toEuc (u ω)) i) (erDisc F) := le_trans (by positivity) hlo
        rw [lowSheet_emb F S _ (toEuc (u ω)) hx0, Complex.ofReal_re]
        have hK59 : K ^ 5 ≤ K ^ 9 := pow_le_pow_right₀ hK1 (by norm_num)
        have h3 : 6 * K ^ 5 * a ≤ 32 * K ^ 9 * a := by
          have := mul_le_mul_of_nonneg_right hK59 ha.le
          nlinarith [pow_pos hK0 5]
        exact herr.trans h3
  -- values of `B` at the points
  have hBreal : ∀ E' : ℝ, 0 ≤ E' → (∀ e, |(erB F S).coeff e| ≤ E') → ∀ ω,
      NChart K a F S (u ω) (w ω) → |eval (u ω) (erB F S)| ≤ 16 * K * E' := by
    intro E' hE' hc ω hω
    have h := norm_cev_le (R := 2 * K) 1 (erB F S) hBdeg hE' (by linarith) hc
      (emb (toEuc (u ω))) (by rw [norm_emb]; exact norm_toEuc_two hω.1)
    rw [cev_center, Complex.norm_real, Real.norm_eq_abs] at h
    calc |eval (u ω) (erB F S)| ≤ ((1 + 1 : ℕ) : ℝ) ^ 3 * (2 * K) ^ 1 * E' := h
      _ = 16 * K * E' := by push_cast; ring
  have hsqrtΔ : ∀ ω, NChart K a F S (u ω) (w ω) → Real.sqrt (eval (u ω) (erDisc F)) ≤ 2 * K := by
    intro ω hω
    obtain ⟨-, h2, -, -⟩ := hpt ω hω
    calc Real.sqrt (eval (u ω) (erDisc F)) ≤ Real.sqrt ((2 * K) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * K := Real.sqrt_sq (by positivity)
  have hT1 : 1 ≤ X ^ (n₄ + 2 * cs + 45) := one_le_pow₀ hX1
  by_cases hBsmall : ∀ e, |(erB F S).coeff e| ≤ X ^ (n₄ + 2 * cs + 45)
  · -- `B` is calibrated: everything is bounded
    obtain ⟨T, hTdef⟩ : ∃ T, T = X ^ (n₄ + 2 * cs + 45) := ⟨_, rfl⟩
    rw [← hTdef] at hBsmall hT1
    have hT0 : 0 ≤ T := by linarith
    have hMval : ∀ᵐ ω ∂lam, (∀ i, |u ω i| ≤ K) ∧
        |eval (u ω) (erM F S)| ≤ 7 * K ^ 5 + 32 * K ^ 2 * T := by
      filter_upwards [hgood] with ω hω
      refine ⟨hω.1, ?_⟩
      obtain ⟨-, -, -, hV⟩ := hpt ω hω
      have hB := hBreal _ hT0 hBsmall ω hω
      have hr := hsqrtΔ ω hω
      have hr0 := Real.sqrt_nonneg (eval (u ω) (erDisc F))
      have habs : |bsign (branch F (u ω) (w ω)) * eval (u ω) (erB F S) *
          Real.sqrt (eval (u ω) (erDisc F))| ≤ 32 * K ^ 2 * T := by
        rw [abs_mul, abs_mul, abs_bsign, one_mul, abs_of_nonneg hr0]
        calc |eval (u ω) (erB F S)| * Real.sqrt (eval (u ω) (erDisc F)) ≤ (16 * K * T) * (2 * K) :=
              mul_le_mul hB hr hr0 (by positivity)
          _ = 32 * K ^ 2 * T := by ring
      have := abs_sub (eval (u ω) (erM F S) + bsign (branch F (u ω) (w ω)) *
        eval (u ω) (erB F S) * Real.sqrt (eval (u ω) (erDisc F)))
        (bsign (branch F (u ω) (w ω)) * eval (u ω) (erB F S) * Real.sqrt (eval (u ω) (erDisc F)))
      rw [add_sub_cancel_right] at this
      linarith
    have hcM : ∀ e, |(erM F S).coeff e| ≤ X ^ n₂ * (7 * K ^ 5 + 32 * K ^ 2 * T) := by
      have h := calib_prob (E := 7 * K ^ 5 + 32 * K ^ 2 * T) hcal₂ hK hH hδ (by positivity)
        (hmeshk n₂ (by omega)) lam u hcap (erM F S) hMdeg hMval
      rw [← hXdef] at h; exact h
    refine key ∅ MeasurableSet.empty (by simp) ?_
    intro ω hω _ z hz
    have hzK := norm_le_of_mem_ball_center hK hω.1 hρ1 hz
    have hM := norm_cev_le 2 (erM F S) hMdeg (by positivity) (by linarith) hcM z hzK
    have hB := norm_cev_le 1 (erB F S) hBdeg hT0 (by linarith) hBsmall z hzK
    have hΔ := (hball ω hω z hz).2
    have hsq := (norm_csqrt_le (cev (erDisc F) z)).trans
      (by linarith : 1 + ‖cev (erDisc F) z‖ ≤ 1 + 864 * K ^ 4 * X ^ n₂)
    have hs : ‖((bsign (branch F (u ω) (w ω)) : ℝ) : ℂ)‖ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_bsign]
    have hK7 : K ^ 5 ≤ K ^ 7 := pow_le_pow_right₀ hK1 (by norm_num)
    have hK27 : K ^ 2 ≤ K ^ 7 := pow_le_pow_right₀ hK1 (by norm_num)
    have hXn : 1 ≤ X ^ n₂ := one_le_pow₀ hX1
    have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK1
    have e1 : ((2 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 2 * (X ^ n₂ * (7 * K ^ 5 + 32 * K ^ 2 * T)) ≤
        16848 * K ^ 9 * X ^ (n₂ + (n₄ + 2 * cs + 45)) := by
      rw [pow_add, ← hTdef]
      have h7 : 7 * K ^ 5 + 32 * K ^ 2 * T ≤ 39 * K ^ 7 * T := by
        have a1 : 7 * K ^ 5 ≤ 7 * K ^ 7 * T := by
          have := mul_le_mul hK7 hT1 (by norm_num) (by positivity)
          nlinarith
        have a2 : 32 * K ^ 2 * T ≤ 32 * K ^ 7 * T := by gcongr
        linarith
      calc ((2 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 2 * (X ^ n₂ * (7 * K ^ 5 + 32 * K ^ 2 * T))
          ≤ ((2 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 2 * (X ^ n₂ * (39 * K ^ 7 * T)) := by gcongr
        _ = 16848 * K ^ 9 * (X ^ n₂ * T) := by push_cast; ring
    have e2 : ((1 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 1 * T * (1 + 864 * K ^ 4 * X ^ n₂) ≤
        27680 * K ^ 5 * X ^ (n₂ + (n₄ + 2 * cs + 45)) := by
      rw [pow_add, ← hTdef]
      have h1 : 1 + 864 * K ^ 4 * X ^ n₂ ≤ 865 * K ^ 4 * X ^ n₂ := by
        have := one_le_mul_of_one_le_of_one_le hK4 hXn
        nlinarith
      calc ((1 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 1 * T * (1 + 864 * K ^ 4 * X ^ n₂)
          ≤ ((1 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 1 * T * (865 * K ^ 4 * X ^ n₂) := by gcongr
        _ = 27680 * K ^ 5 * (X ^ n₂ * T) := by push_cast; ring
    have f1 := bound_pow 9 (n₂ + (n₄ + 2 * cs + 45)) 15 hK0.le hKHK hKH2 (by norm_num)
      (by norm_num : (16848 : ℝ) ≤ 2 ^ 15)
    have f2 := bound_pow 5 (n₂ + (n₄ + 2 * cs + 45)) 15 hK0.le hKHK hKH2 (by norm_num)
      (by norm_num : (27680 : ℝ) ≤ 2 ^ 15)
    unfold lowSheet
    calc ‖cev (erM F S) z + ((bsign (branch F (u ω) (w ω)) : ℝ) : ℂ) * cev (erB F S) z *
          Complex.sqrt (cev (erDisc F) z)‖
        ≤ ‖cev (erM F S) z‖ + ‖cev (erB F S) z‖ * ‖Complex.sqrt (cev (erDisc F) z)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, hs, one_mul]
      _ ≤ ((2 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 2 * (X ^ n₂ * (7 * K ^ 5 + 32 * K ^ 2 * T)) +
          ((1 + 1 : ℕ) : ℝ) ^ 3 * (4 * K) ^ 1 * T * (1 + 864 * K ^ 4 * X ^ n₂) := by
          gcongr
      _ ≤ X ^ (15 + 9 + (n₂ + (n₄ + 2 * cs + 45))) + X ^ (15 + 5 + (n₂ + (n₄ + 2 * cs + 45))) :=
          add_le_add (e1.trans f1) (e2.trans f2)
      _ ≤ X ^ (n₂ + n₄ + 2 * cs + 69) + X ^ (n₂ + n₄ + 2 * cs + 69) :=
          add_le_add (hXmono _ _ (by omega)) (hXmono _ _ (by omega))
      _ = 2 * X ^ (n₂ + n₄ + 2 * cs + 69) := by ring
      _ ≤ X * X ^ (n₂ + n₄ + 2 * cs + 69) := mul_le_mul_of_nonneg_right hKH2 (by positivity)
      _ = X ^ (n₂ + n₄ + 2 * cs + 70) := by ring
      _ ≤ X ^ (n₂ + n₄ + ns + 4 * cs + 200) := hXmono _ _ (by omega)
  · -- `B` is large: discard its thin slab
    rw [not_forall] at hBsmall
    obtain ⟨e₁, he₁⟩ := hBsmall
    rw [not_le] at he₁
    have he₁0 : (erB F S).coeff e₁ ≠ 0 := by
      intro h0; rw [h0, abs_zero] at he₁; linarith
    have hsupp : (erB F S).support.Nonempty := ⟨e₁, MvPolynomial.mem_support_iff.mpr he₁0⟩
    obtain ⟨b, hbdef⟩ : ∃ b, b = (erB F S).support.sup' hsupp (fun e => |(erB F S).coeff e|) :=
      ⟨_, rfl⟩
    have hbmax : ∀ e, |(erB F S).coeff e| ≤ b := by
      intro e
      by_cases he : e ∈ (erB F S).support
      · rw [hbdef]; exact Finset.le_sup' (fun e => |(erB F S).coeff e|) he
      · rw [MvPolynomial.notMem_support_iff.mp he, abs_zero, hbdef]
        exact le_trans (abs_nonneg _) (Finset.le_sup' (fun e => |(erB F S).coeff e|)
          (MvPolynomial.mem_support_iff.mpr he₁0))
    have hbex : ∃ e, b ≤ |(erB F S).coeff e| := by
      obtain ⟨e, -, he⟩ := Finset.exists_mem_eq_sup' hsupp (fun e => |(erB F S).coeff e|)
      exact ⟨e, by rw [hbdef, he]⟩
    have hbT : X ^ (n₄ + 2 * cs + 45) < b := lt_of_lt_of_le he₁ (hbmax e₁)
    have hb1 : 1 ≤ b := le_trans hT1 hbT.le
    have hb0 : 0 < b := by linarith
    have hEm : MeasurableSet
        {ω | (∀ i, |u ω i| ≤ K) ∧ |eval (u ω) (erB F S)| ≤ b * ((K * H) ^ cs)⁻¹} := by
      have h1 : MeasurableSet {ω | ∀ i, |u ω i| ≤ K} := by
        simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i =>
          measurableSet_le ((measurable_pi_apply i).comp hu).abs measurable_const
      have h2 : MeasurableSet {ω | |eval (u ω) (erB F S)| ≤ b * ((K * H) ^ cs)⁻¹} :=
        measurableSet_le ((MvPolynomial.continuous_eval _).measurable.comp hu).abs measurable_const
      exact h1.inter h2
    have hEmass := hslab K H δ b hK hH hδ hb0 (by rw [← hns']; exact hmeshk ns (by omega))
      Ω lam u hu hcap (erB F S) hBdeg hbex
    rw [← hcs] at hEmass
    rw [← hXdef] at hEmass hEm
    -- the product of the two branch values
    have hNval : ∀ᵐ ω ∂lam, (∀ i, |u ω i| ≤ K) ∧
        |eval (u ω) (erN F S)| ≤ 497 * K ^ 10 * b := by
      filter_upwards [hgood] with ω hω
      refine ⟨hω.1, ?_⟩
      obtain ⟨hlo, -, -, hV⟩ := hpt ω hω
      have hB := hBreal b hb0.le hbmax ω hω
      have hr := hsqrtΔ ω hω
      have hr0 := Real.sqrt_nonneg (eval (u ω) (erDisc F))
      have hr2 : Real.sqrt (eval (u ω) (erDisc F)) ^ 2 = eval (u ω) (erDisc F) :=
        Real.sq_sqrt (le_trans (by positivity) hlo)
      have hσ2 : bsign (branch F (u ω) (w ω)) ^ 2 = 1 := bsign_sq _
      obtain ⟨σ, hσ⟩ : ∃ σ, σ = bsign (branch F (u ω) (w ω)) := ⟨_, rfl⟩
      obtain ⟨r, hr'⟩ : ∃ r, r = Real.sqrt (eval (u ω) (erDisc F)) := ⟨_, rfl⟩
      rw [← hσ, ← hr'] at hV
      rw [← hσ] at hσ2
      rw [← hr'] at hr hr0 hr2
      have hNe : eval (u ω) (erN F S) =
          (eval (u ω) (erM F S) + σ * eval (u ω) (erB F S) * r) *
          ((eval (u ω) (erM F S) + σ * eval (u ω) (erB F S) * r) -
            2 * σ * eval (u ω) (erB F S) * r) := by
        simp only [erN, eval_sub, eval_pow, eval_mul]
        rw [← hr2]
        linear_combination (eval (u ω) (erB F S) ^ 2 * r ^ 2) * hσ2
      have hσB : |2 * σ * eval (u ω) (erB F S) * r| ≤ 64 * K ^ 2 * b := by
        rw [abs_mul, abs_mul, abs_mul, abs_two, hσ, abs_bsign, abs_of_nonneg hr0]
        calc 2 * 1 * |eval (u ω) (erB F S)| * r ≤ 2 * 1 * (16 * K * b) * (2 * K) := by gcongr
          _ = 64 * K ^ 2 * b := by ring
      rw [hNe, abs_mul]
      have hV' := (abs_sub _ _).trans (add_le_add hV hσB)
      have hK7 : K ^ 7 ≤ K ^ 10 := pow_le_pow_right₀ hK1 (by norm_num)
      have hK10 : 0 < K ^ 10 := by positivity
      calc |eval (u ω) (erM F S) + σ * eval (u ω) (erB F S) * r| *
            |eval (u ω) (erM F S) + σ * eval (u ω) (erB F S) * r -
              2 * σ * eval (u ω) (erB F S) * r|
          ≤ (7 * K ^ 5) * (7 * K ^ 5 + 64 * K ^ 2 * b) :=
            mul_le_mul hV hV' (abs_nonneg _) (by positivity)
        _ = 49 * K ^ 10 + 448 * K ^ 7 * b := by ring
        _ ≤ 49 * K ^ 10 * b + 448 * K ^ 10 * b := by
            have a1 : 49 * K ^ 10 ≤ 49 * K ^ 10 * b := by nlinarith
            have a2 : 448 * K ^ 7 * b ≤ 448 * K ^ 10 * b := by gcongr
            linarith
        _ = 497 * K ^ 10 * b := by ring
    have hcN : ∀ e, |(erN F S).coeff e| ≤ X ^ n₄ * (497 * K ^ 10 * b) := by
      have h := calib_prob (E := 497 * K ^ 10 * b) hcal₄ hK hH hδ (by positivity)
        (hmeshk n₄ (by omega)) lam u hcap (erN F S) hNdeg hNval
      rw [← hXdef] at h; exact h
    refine key _ hEm hEmass ?_
    intro ω hω hωE z hz
    have hcK := hcenter ω hω
    -- `B` is large on the ball
    have hBu : b * (X ^ cs)⁻¹ < |eval (u ω) (erB F S)| := by
      by_contra h
      exact hωE ⟨hω.1, not_lt.mp h⟩
    have hρ512 : 512 * X ^ cs * ρ ≤ 1 := by
      have h1 : 512 * X ^ cs ≤ X ^ (n₂ + cs + 30) := by
        have := bound_pow 0 cs 9 hK0.le hKHK hKH2 (by norm_num) (by norm_num : (512 : ℝ) ≤ 2 ^ 9)
        rw [pow_zero, mul_one] at this
        exact this.trans (hXmono _ _ (by omega))
      calc 512 * X ^ cs * ρ ≤ X ^ (n₂ + cs + 30) * ρ := mul_le_mul_of_nonneg_right h1 hρ0.le
        _ = 1 := by rw [mul_comm]; exact hρX
    have hBball : ∀ y ∈ ball (emb (toEuc (u ω))) (4 * ρ),
        b * (X ^ cs)⁻¹ / 2 ≤ ‖cev (erB F S) y‖ := by
      intro y hy
      have hyK := norm_le_of_mem_ball_center hK hω.1 hρ1 hy
      have hlip := cev_lipschitz 1 (erB F S) hBdeg hb0.le (by linarith) hbmax y
        (emb (toEuc (u ω))) hyK hcK
      rw [cev_center] at hlip
      rw [mem_ball, dist_eq_norm] at hy
      have hconst : 4 * (((1 + 1 : ℕ) : ℝ) ^ 3 * (2 * (4 * K)) ^ 1 * b) / (4 * K) = 64 * b := by
        push_cast; field_simp; ring
      rw [hconst] at hlip
      have hsmall : 64 * b * ‖y - emb (toEuc (u ω))‖ ≤ b * (X ^ cs)⁻¹ / 2 := by
        have h1 : 64 * b * ‖y - emb (toEuc (u ω))‖ ≤ 64 * b * (4 * ρ) :=
          mul_le_mul_of_nonneg_left hy.le (by positivity)
        refine h1.trans ?_
        have hkey : 64 * b * (4 * ρ) * (2 * X ^ cs) ≤ b := by
          calc 64 * b * (4 * ρ) * (2 * X ^ cs) = b * (512 * X ^ cs * ρ) := by ring
            _ ≤ b * 1 := mul_le_mul_of_nonneg_left hρ512 hb0.le
            _ = b := by ring
        rw [show b * (X ^ cs)⁻¹ / 2 = b / (2 * X ^ cs) by field_simp, le_div_iff₀ (by positivity)]
        exact hkey
      have htri : ‖((eval (u ω) (erB F S) : ℝ) : ℂ)‖ ≤
          ‖cev (erB F S) y‖ + ‖cev (erB F S) y - ((eval (u ω) (erB F S) : ℝ) : ℂ)‖ := by
        have := norm_add_le (cev (erB F S) y) (((eval (u ω) (erB F S) : ℝ) : ℂ) - cev (erB F S) y)
        rw [norm_sub_rev] at this
        simpa using this
      rw [Complex.norm_real, Real.norm_eq_abs] at htri
      have hhalf : b * (X ^ cs)⁻¹ = b * (X ^ cs)⁻¹ / 2 + b * (X ^ cs)⁻¹ / 2 := by ring
      linarith [hlip.trans hsmall]
    -- the square root of the discriminant is bounded below
    have hsqrt : ∀ y ∈ ball (emb (toEuc (u ω))) (4 * ρ),
        (2 * K)⁻¹ ≤ ‖Complex.sqrt (cev (erDisc F) y)‖ := by
      intro y hy
      have hre := (hball ω hω y hy).1
      have h1 : (4 * K ^ 2)⁻¹ ≤ ‖cev (erDisc F) y‖ := hre.trans (Complex.re_le_norm _)
      have h2 := norm_csqrt_sq (cev (erDisc F) y)
      have he : ((2 * K)⁻¹) ^ 2 = (4 * K ^ 2)⁻¹ := by
        rw [inv_pow, mul_pow]; norm_num
      have h3 : ((2 * K)⁻¹) ^ 2 ≤ ‖Complex.sqrt (cev (erDisc F) y)‖ ^ 2 := by
        rw [h2, he]; exact h1
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp h3
    -- the two branches
    have hcont : ∀ t : Bool, ContinuousOn (lowSheet F S t) (ball (emb (toEuc (u ω))) (4 * ρ)) := by
      intro t y hy
      have hre := (hball ω hω y hy).1
      exact (lowSheet_differentiableAt F S t
        (lt_of_lt_of_le (by positivity) hre)).continuousAt.continuousWithinAt
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = b * (X ^ cs)⁻¹ * (2 * K)⁻¹ := ⟨_, rfl⟩
    have hL : 0 < L := by rw [hLdef]; positivity
    have hdiff : ∀ y ∈ ball (emb (toEuc (u ω))) (4 * ρ),
        L ≤ ‖lowSheet F S (branch F (u ω) (w ω)) y - lowSheet F S (!branch F (u ω) (w ω)) y‖ := by
      intro y hy
      have h2n : ‖(2 : ℂ)‖ = 2 := by simp
      rw [lowSheet_sub, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_bsign, h2n]
      have h1 := hBball y hy
      have h2 := hsqrt y hy
      calc L = 2 * 1 * (b * (X ^ cs)⁻¹ / 2) * (2 * K)⁻¹ := by rw [hLdef]; ring
        _ ≤ 2 * 1 * ‖cev (erB F S) y‖ * ‖Complex.sqrt (cev (erDisc F) y)‖ := by gcongr
    obtain ⟨VN, hVN⟩ : ∃ VN : ℝ, VN = 15904000 * K ^ 14 * X ^ n₄ * b := ⟨_, rfl⟩
    have hNb : ∀ y ∈ ball (emb (toEuc (u ω))) (4 * ρ), ‖cev (erN F S) y‖ ≤ VN := by
      intro y hy
      have h := norm_cev_le 4 (erN F S) hNdeg (by positivity) (by linarith) hcN y
        (norm_le_of_mem_ball_center hK hω.1 hρ1 hy)
      refine h.trans (le_of_eq ?_)
      rw [hVN]; push_cast; ring
    have hXc0 : 0 < X ^ cs := by positivity
    have hVNL : VN < L ^ 2 / 4 := by
      have hbig : 254464000 * K ^ 16 * (X ^ n₄ * X ^ cs * X ^ cs) < b := by
        have h1 := bound_pow 16 (n₄ + 2 * cs) 28 hK0.le hKHK hKH2 (by norm_num)
          (by norm_num : (254464000 : ℝ) ≤ 2 ^ 28)
        have h2 : X ^ (28 + 16 + (n₄ + 2 * cs)) < X ^ (n₄ + 2 * cs + 45) :=
          pow_lt_pow_right₀ (by linarith) (by omega)
        have h3 : X ^ n₄ * X ^ cs * X ^ cs = X ^ (n₄ + 2 * cs) := by ring
        rw [h3]
        linarith
      rw [hVN, hLdef]
      have hpos : 0 < X ^ n₄ := by positivity
      rw [show (b * (X ^ cs)⁻¹ * (2 * K)⁻¹) ^ 2 / 4 = b ^ 2 / (16 * K ^ 2 * (X ^ cs) ^ 2) by
        field_simp; ring, lt_div_iff₀ (by positivity)]
      have hK16 : 0 < K ^ 16 := by positivity
      calc 15904000 * K ^ 14 * X ^ n₄ * b * (16 * K ^ 2 * (X ^ cs) ^ 2)
          = (254464000 * K ^ 16 * (X ^ n₄ * X ^ cs * X ^ cs)) * b := by ring
        _ < b * b := mul_lt_mul_of_pos_right hbig hb0
        _ = b ^ 2 := by ring
    have hz₀ : emb (toEuc (u ω)) ∈ ball (emb (toEuc (u ω))) (4 * ρ) :=
      mem_ball_self (by positivity)
    have hsmall0 : ‖lowSheet F S (branch F (u ω) (w ω)) (emb (toEuc (u ω)))‖ < L / 2 := by
      obtain ⟨hlo, -, -, hV⟩ := hpt ω hω
      have hx0 : 0 ≤ eval (fun i => (toEuc (u ω)) i) (erDisc F) := le_trans (by positivity) hlo
      rw [lowSheet_emb F S _ (toEuc (u ω)) hx0, Complex.norm_real, Real.norm_eq_abs]
      refine lt_of_le_of_lt hV ?_
      have h28 : 28 * K ^ 6 * X ^ cs < b := by
        have h1 := bound_pow 6 cs 5 hK0.le hKHK hKH2 (by norm_num)
          (by norm_num : (28 : ℝ) ≤ 2 ^ 5)
        have h2 : X ^ (5 + 6 + cs) < X ^ (n₄ + 2 * cs + 45) :=
          pow_lt_pow_right₀ (by linarith) (by omega)
        linarith
      rw [hLdef, show b * (X ^ cs)⁻¹ * (2 * K)⁻¹ / 2 = b / (4 * K * X ^ cs) by field_simp; ring,
        lt_div_iff₀ (by positivity)]
      calc 7 * K ^ 5 * (4 * K * X ^ cs) = 28 * K ^ 6 * X ^ cs := by ring
        _ < b := h28
    have hbound := small_branch_bound hL (hcont _) (hcont _)
      (fun y _ => lowSheet_mul F S (branch F (u ω) (w ω)) y) hNb hVNL hdiff _ hz₀ hsmall0 z hz
    refine hbound.trans ?_
    rw [hVN, hLdef]
    rw [show 2 * (15904000 * K ^ 14 * X ^ n₄ * b) / (b * (X ^ cs)⁻¹ * (2 * K)⁻¹) =
        63616000 * K ^ 15 * (X ^ n₄ * X ^ cs) by field_simp; ring]
    have h1 := bound_pow 15 (n₄ + cs) 26 hK0.le hKHK hKH2 (by norm_num)
      (by norm_num : (63616000 : ℝ) ≤ 2 ^ 26)
    rw [show X ^ n₄ * X ^ cs = X ^ (n₄ + cs) by ring]
    exact h1.trans (hXmono _ _ (by omega))


/-! ### One pass -/

/-- **One native pass from finite mesh caps.** For a probability law of points with mesh caps
`H δ³` at a mesh `δ ≤ (K H)^(-n)` and the chart bounds `NChart`, every point outside mass
`(K H)^(-A)` has, on its branch, a native sheet on the complex ball of radius `4ρ`,
`ρ ≥ (K H)^(-n)`, bounded by `(K H)^n`, real on the real points, a root of a nonzero relation
of degree `≤ 4`, and within `32 K⁹ a` of the native value. -/
theorem native_sheets_pass :
    ∃ α β : ℕ, 1 ≤ β ∧ ∀ (A : ℕ) (K H a δ : ℝ), 2 ≤ K → 1 ≤ H → 0 < a → a ≤ 1 → 0 < δ →
      (K * H) ^ (α * A + β) * δ ≤ 1 →
      ∀ (F S : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (lam : Measure Ω), IsProbabilityMeasure lam →
      ∀ (u : Ω → Fin 3 → ℝ) (w : Ω → ℝ), Measurable u →
      (∀ q : Fin 3 → ℤ, lam {ω | (fun i => ⌊u ω i / δ⌋) = q} ≤ ENNReal.ofReal (H * δ ^ 3)) →
      (∀ᵐ ω ∂lam, NChart K a F S (u ω) (w ω)) →
      PassResult (α * A + β) A K H a F S lam u w := by
  obtain ⟨nh, hnh, hhigh⟩ := pass_high
  obtain ⟨nz, hnz, hzero⟩ := pass_zero
  obtain ⟨αl, βl, hβl, hlow⟩ := pass_low
  refine ⟨αl, nh + nz + βl, by omega, ?_⟩
  intro A K H a δ hK hH ha ha1 hδ hmesh F S hF hS Ω _ lam hprob u w hu hcap hgood
  have hX1 : 1 ≤ K * H := by nlinarith
  have hm : ∀ k, k ≤ αl * A + (nh + nz + βl) → (K * H) ^ k * δ ≤ 1 := fun k hk =>
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hX1 hk) hδ.le) hmesh
  have hle : ∀ k, k ≤ nh + nz + βl → k ≤ αl * A + (nh + nz + βl) := fun k hk =>
    hk.trans (Nat.le_add_left _ _)
  by_cases hc : (4 * K ^ 3 * a)⁻¹ ≤ |curvature F 3|
  · exact (hhigh A K H a δ hK hH ha ha1 hδ (hm nh (hle _ (by omega))) F S hF hS hc Ω lam hprob
      u w hu hcap hgood).mono hX1 (hle _ (by omega))
  · rw [not_le] at hc
    by_cases h0 : curvature F 3 = 0
    · exact (hzero A K H a δ hK hH ha ha1 hδ (hm nz (hle _ (by omega))) F S hF hS h0 Ω lam
        hprob u w hu hcap hgood).mono hX1 (hle _ (by omega))
    · exact (hlow A K H a δ hK hH ha ha1 hδ (hm _ (Nat.add_le_add_left (by omega) _)) F S hF hS
        h0 hc Ω lam hprob u w hu hcap hgood).mono hX1 (Nat.add_le_add_left (by omega) _)

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
