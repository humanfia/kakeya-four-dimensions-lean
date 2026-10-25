import Submission.Obl.k4_scalar_candidate_original_return.Core.PlankBasic

/-!
# Normalized candidate graphs are bounded on the whole plank square

The covered incidences of a candidate charge many base cells (cell masses are capped by the
tangent non-concentration, the candidate carries its floor), on each charged cell the
normalized graph difference is `O(K N^{θ c₀})`, and fixed-degree Remez plus extrapolation give
a bound `N^{εm c₀}` on the square of half-width `1` in matching coordinates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set MvPolynomial

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid) (π : CmpParams) (k : ℕ) (ℓ : Fin (a.ct k))
  (i : Fin (a.ls k ℓ).n)
include ha

omit ha in
private theorem abs_sub_lt_of_floor_div_eq {w b c : ℝ} (hw : 0 < w)
    (h : ⌊b / w⌋ = ⌊c / w⌋) : |b - c| < w := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  have heq : b / w - c / w = (b - c) / w := by ring
  rw [heq, abs_div, abs_of_pos hw, div_lt_one hw] at h1
  exact h1

/-- Coefficient-bounded candidates vary by at most `N^{-s'}/8` across a base cell met by
the plank (base points with `|t| ≤ 2`, `|y| ≤ 4K`). -/
theorem cand_cell_variation (s : ℝ) (hP : a.PlankHyp π k ℓ i s)
    (m : Fin (a.ncand π k ℓ i)) (u u' : Fin 2 → ℝ)
    (hu : ∀ e, |u e| ≤ 4 * a.rK k) (hu' : ∀ e, |u' e| ≤ 4 * a.rK k)
    (hq : ∀ e, ⌊u e / a.tangent k ^ (-π.r)⌋ = ⌊u' e / a.tangent k ^ (-π.r)⌋) :
    |eval u (a.cand π k ℓ i m) - eval u' (a.cand π k ℓ i m)| ≤ a.tangent k ^ (-π.s') / 8 := by
  obtain ⟨hs0, hc0, hθ, hθε, hεm, hεm1⟩ := hP.par_pos
  have hN2 := hP.N_ge
  have hK1 := hP.K_ge
  have hKs := hP.K_small
  have hNl := hP.N_large
  have hNpos : 0 < a.tangent k := by linarith
  have hN1 : 1 ≤ a.tangent k := by linarith
  have hw : 0 < a.tangent k ^ (-π.r) := Real.rpow_pos_of_pos hNpos _
  have hd : ∀ e, |u e - u' e| ≤ a.tangent k ^ (-π.r) := fun e =>
    (abs_sub_lt_of_floor_div_eq hw (hq e)).le
  have hlip := Cells.quad_lipschitz (a.cand π k ℓ i m) (cand_totalDegree ha π k ℓ i m)
    (cand_coeff ha π k ℓ i m) u u' hu hu'
  have hR0 : 0 < a.tangent k ^ (π.σ.R : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hsum : |u 0 - u' 0| + |u 1 - u' 1| ≤ 2 * a.tangent k ^ (-π.r) := by
    linarith [hd 0, hd 1]
  have hfac : 0 ≤ 10 * a.tangent k ^ (π.σ.R : ℝ) * (1 + 4 * a.rK k) := by positivity
  have h1 : 10 * a.tangent k ^ (π.σ.R : ℝ) * (1 + 4 * a.rK k) *
      (|u 0 - u' 0| + |u 1 - u' 1|) ≤
      100 * a.rK k * (a.tangent k ^ (π.σ.R : ℝ) * a.tangent k ^ (-π.r)) := by
    calc _ ≤ 10 * a.tangent k ^ (π.σ.R : ℝ) * (1 + 4 * a.rK k) *
          (2 * a.tangent k ^ (-π.r)) := mul_le_mul_of_nonneg_left hsum hfac
      _ ≤ _ := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 20 * a.rK k - 20)
          (mul_nonneg hR0.le hw.le)]
  have hθc : 0 < π.θ * π.σ.c₀ := mul_pos hθ hc0
  have hk0 : 0 < kap0 π := by unfold kap0; positivity
  have h800 : 800 * a.rK k ≤ a.tangent k ^ kap0 π * a.tangent k ^ kap0 π := by
    have h800' : (800 : ℝ) ≤ a.tangent k ^ kap0 π := le_trans (by norm_num) hNl
    exact mul_le_mul h800' hKs (by linarith) (by linarith)
  have hexp : kap0 π + kap0 π + ((π.σ.R : ℝ) + -π.r) ≤ -π.s' := by
    unfold kap0 CmpParams.r CmpParams.s'
    linarith
  have h2 : 800 * a.rK k * (a.tangent k ^ (π.σ.R : ℝ) * a.tangent k ^ (-π.r)) ≤
      a.tangent k ^ (-π.s') := by
    calc 800 * a.rK k * (a.tangent k ^ (π.σ.R : ℝ) * a.tangent k ^ (-π.r))
        ≤ (a.tangent k ^ kap0 π * a.tangent k ^ kap0 π) *
            (a.tangent k ^ (π.σ.R : ℝ) * a.tangent k ^ (-π.r)) :=
          mul_le_mul_of_nonneg_right h800 (mul_nonneg hR0.le hw.le)
      _ = a.tangent k ^ (kap0 π + kap0 π + ((π.σ.R : ℝ) + -π.r)) := by
          rw [Real.rpow_add hNpos, Real.rpow_add hNpos, Real.rpow_add hNpos]
      _ ≤ a.tangent k ^ (-π.s') := Real.rpow_le_rpow_of_exponent_le hN1 hexp
  exact hlip.trans (h1.trans (by linarith))


omit ha in
private theorem zeta_sub_zero (u u' : Fin 2 → ℝ) :
    a.zeta k ℓ i u 0 - a.zeta k ℓ i u' 0 = (2 : ℝ) ^ (a.ls k ℓ).T * (u 0 - u' 0) / 3 := by
  simp only [zeta, Fin.isValue, Matrix.cons_val_zero]
  ring

private theorem zeta_sub_one (u u' : Fin 2 → ℝ) :
    a.zeta k ℓ i u 1 - a.zeta k ℓ i u' 1 =
      (2 : ℝ) ^ (a.ls k ℓ).T * ((u 1 - u' 1) - (u 0 - u' 0) * (a.ls k ℓ).v i) /
        (4 * a.rK k) := by
  have hK : a.rK k ≠ 0 := (lt_of_lt_of_le one_pos (ha.tangent_input.2.2.1.1 k)).ne'
  simp only [zeta, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Normalized displacement of two base points at coordinate distance `≤ w`. -/
private theorem zeta_disp (hv : |(a.ls k ℓ).v i| ≤ a.rK k) {w : ℝ} (u u' : Fin 2 → ℝ)
    (hd : ∀ e, |u e - u' e| ≤ w) :
    |a.zeta k ℓ i u 0 - a.zeta k ℓ i u' 0| + |a.zeta k ℓ i u 1 - a.zeta k ℓ i u' 1| ≤
      (2 : ℝ) ^ (a.ls k ℓ).T * w := by
  have hK1 : 1 ≤ a.rK k := ha.tangent_input.2.2.1.1 k
  have hKpos : 0 < a.rK k := by linarith
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  have hw : 0 ≤ w := (abs_nonneg _).trans (hd 0)
  rw [zeta_sub_zero, zeta_sub_one ha]
  have h0 : |(2 : ℝ) ^ (a.ls k ℓ).T * (u 0 - u' 0) / 3| ≤ (2 : ℝ) ^ (a.ls k ℓ).T * w / 3 := by
    rw [abs_div, abs_mul, abs_of_pos hT, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hd 0) hT.le) (by norm_num)
  have hnum : |(u 1 - u' 1) - (u 0 - u' 0) * (a.ls k ℓ).v i| ≤ w + w * a.rK k := by
    calc |(u 1 - u' 1) - (u 0 - u' 0) * (a.ls k ℓ).v i|
        ≤ |u 1 - u' 1| + |(u 0 - u' 0) * (a.ls k ℓ).v i| := abs_sub _ _
      _ = |u 1 - u' 1| + |u 0 - u' 0| * |(a.ls k ℓ).v i| := by rw [abs_mul]
      _ ≤ w + w * a.rK k := by
          have := mul_le_mul (hd 0) hv (abs_nonneg _) hw
          linarith [hd 1]
  have h1 : |(2 : ℝ) ^ (a.ls k ℓ).T * ((u 1 - u' 1) - (u 0 - u' 0) * (a.ls k ℓ).v i) /
      (4 * a.rK k)| ≤ (2 : ℝ) ^ (a.ls k ℓ).T * w / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hT, abs_of_pos (by positivity : (0 : ℝ) < 4 * a.rK k),
      div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hnum hT.le
    nlinarith [mul_nonneg hT.le hw]
  have : (2 : ℝ) ^ (a.ls k ℓ).T * w / 3 + (2 : ℝ) ^ (a.ls k ℓ).T * w / 2 ≤
      (2 : ℝ) ^ (a.ls k ℓ).T * w := by nlinarith [mul_nonneg hT.le hw]
  linarith

/-- The plank's own polynomial varies by at most `N^{-s'}/8` across a base cell whose
normalized image lies in `[-3,4]²`. -/
theorem poly_cell_variation (s : ℝ) (hP : a.PlankHyp π k ℓ i s) (u u' : Fin 2 → ℝ)
    (hu : ∀ e, a.zeta k ℓ i u e ∈ Set.Icc (-3 : ℝ) 4)
    (hu' : ∀ e, a.zeta k ℓ i u' e ∈ Set.Icc (-3 : ℝ) 4)
    (hq : ∀ e, ⌊u e / a.tangent k ^ (-π.r)⌋ = ⌊u' e / a.tangent k ^ (-π.r)⌋) :
    |eval u ((a.ls k ℓ).poly i) - eval u' ((a.ls k ℓ).poly i)| ≤ a.tangent k ^ (-π.s') / 8 := by
  obtain ⟨hs0, hc0, hθ, hθε, hεm, hεm1⟩ := hP.par_pos
  obtain ⟨hκ0, hκ1⟩ := hP.κ_range
  have hN2 := hP.N_ge
  have hK1 := hP.K_ge
  have hKs := hP.K_small
  have hNl := hP.N_large
  have hTup := hP.T_upper
  have hsw := hP.s_win
  have hNpos : 0 < a.tangent k := by linarith
  have hN1 : 1 ≤ a.tangent k := by linarith
  have hKpos : 0 < a.rK k := by linarith
  have hw : 0 < a.tangent k ^ (-π.r) := Real.rpow_pos_of_pos hNpos _
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  have hd : ∀ e, |u e - u' e| ≤ a.tangent k ^ (-π.r) := fun e =>
    (abs_sub_lt_of_floor_div_eq hw (hq e)).le
  have hv : |(a.ls k ℓ).v i| ≤ a.rK k := by
    have := hP.uv_le
    linarith [abs_nonneg ((a.ls k ℓ).u i)]
  -- the normalized fit polynomial
  have hFdeg : (a.Fzeta k ℓ i).totalDegree ≤ 2 :=
    (Normalize.affSubst_totalDegree_le _ _ _).trans (poly_totalDegree ha k ℓ i)
  -- bound on the tangent-input strip
  have hbox : ∀ ζ : Fin 2 → ℝ, ζ 0 ∈ Set.Icc (1 / 3 : ℝ) (1 / 3 + 1 / 3) →
      ζ 1 ∈ Set.Icc (1 / 2 - 1 / (2 * a.rK k)) (1 / 2 - 1 / (2 * a.rK k) + 1 / a.rK k) →
      |eval ζ (a.Fzeta k ℓ i)| ≤ a.rK k := by
    intro ζ h0 h1
    rw [eval_Fzeta ha]
    set t : ℝ := a.tStart k ℓ i + (3 * ζ 0 - 1) / (2 : ℝ) ^ (a.ls k ℓ).T with ht
    set w : ℝ := a.rK k * (4 * ζ 1 - 2) with hwdef
    have hpsi : a.psi k ℓ i ζ = ![t, (a.ls k ℓ).u i + t * (a.ls k ℓ).v i +
        w / (2 : ℝ) ^ (a.ls k ℓ).T] := by
      funext e
      fin_cases e
      · simp only [psi, psiA, psib, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, ht]
        field_simp
        ring
      · simp only [psi, psiA, psib, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, ht, hwdef]
        field_simp
        ring
    rw [hpsi]
    apply hP.F_bound
    · -- time in the block
      obtain ⟨h0a, h0b⟩ := h0
      simp only [I, tStart] at ht ⊢
      constructor
      · rw [ht]
        have : 0 ≤ (3 * ζ 0 - 1) / (2 : ℝ) ^ (a.ls k ℓ).T := div_nonneg (by linarith) hT.le
        linarith
      · rw [ht, add_div]
        have : (3 * ζ 0 - 1) / (2 : ℝ) ^ (a.ls k ℓ).T ≤ 1 / (2 : ℝ) ^ (a.ls k ℓ).T :=
          div_le_div_of_nonneg_right (by linarith) hT.le
        linarith
    · obtain ⟨h1a, h1b⟩ := h1
      have hK2 : 0 < 2 * a.rK k := by linarith
      have e1 : 1 / (2 * a.rK k) * a.rK k = 1 / 2 := by field_simp
      have e2 : 1 / a.rK k * a.rK k = 1 := by field_simp
      constructor
      · rw [hwdef]; nlinarith
      · rw [hwdef]; nlinarith
  have hα₁ : 0 ≤ 1 / 2 - 1 / (2 * a.rK k) := by
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hα₁ℓ : 1 / 2 - 1 / (2 * a.rK k) + 1 / a.rK k ≤ 1 := by
    have : 1 / a.rK k - 1 / (2 * a.rK k) = 1 / (2 * a.rK k) := by field_simp; ring
    have h2 : 1 / (2 * a.rK k) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    linarith
  have hext := Normalize.quad2d_extrap (a.Fzeta k ℓ i) hFdeg (by norm_num : (0 : ℝ) < 1 / 3)
    (by positivity : (0 : ℝ) < 1 / a.rK k) (by norm_num : (0 : ℝ) ≤ 1 / 3) hα₁
    (by norm_num) hα₁ℓ hbox
  have hlip := Normalize.quad_lipschitz_of_bound (a.Fzeta k ℓ i) hFdeg hext
    (a.zeta k ℓ i u) (a.zeta k ℓ i u') hu hu'
  rw [eval_Fzeta ha, eval_Fzeta ha, psi_zeta ha, psi_zeta ha] at hlip
  have hdisp := zeta_disp ha k ℓ i hv u u' hd
  -- the constant
  have hB : 10 ^ 6 / ((1 / 3 : ℝ) ^ 2 * (1 / a.rK k) ^ 2) * a.rK k = 9 * 10 ^ 6 * a.rK k ^ 3 := by
    field_simp
    ring
  rw [hB] at hlip
  have hθc : 0 < π.θ * π.σ.c₀ := mul_pos hθ hc0
  have hs_pos : 0 ≤ s := by
    have := hsw.2
    rw [abs_le] at this
    linarith
  have hκs : a.κ * s ≤ 3 * π.σ.s₀ / 2 := by
    have := hsw.2
    rw [abs_le] at this
    nlinarith
  have hNκ : a.tangent k ^ (a.κ * s) ≤ a.tangent k ^ (3 * π.σ.s₀ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hκs
  -- 1000 * 9e6 K^3 * 2^T * w ≤ N^{-s'}/8
  have hfinal : 1000 * (9 * 10 ^ 6 * a.rK k ^ 3) * ((2 : ℝ) ^ (a.ls k ℓ).T * a.tangent k ^ (-π.r)) ≤
      a.tangent k ^ (-π.s') / 8 := by
    have hK4 : (72 * 10 ^ 9 : ℝ) * a.rK k ^ 4 ≤ a.tangent k ^ (5 * kap0 π) := by
      have hc : (72 * 10 ^ 9 : ℝ) ≤ a.tangent k ^ kap0 π := le_trans (by norm_num) hNl
      have hK4' : a.rK k ^ 4 ≤ (a.tangent k ^ kap0 π) ^ 4 := pow_le_pow_left₀ (by linarith) hKs 4
      have heq : a.tangent k ^ (5 * kap0 π) = a.tangent k ^ kap0 π * (a.tangent k ^ kap0 π) ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
        ring_nf
      rw [heq]
      exact mul_le_mul hc hK4' (by positivity) (by positivity)
    have hexp : 5 * kap0 π + 3 * π.σ.s₀ / 2 + -π.r ≤ -π.s' := by
      unfold kap0 CmpParams.r CmpParams.s'
      have : (0 : ℝ) ≤ (π.σ.R : ℝ) := Nat.cast_nonneg _
      linarith
    have h2T : (2 : ℝ) ^ (a.ls k ℓ).T ≤ a.rK k * a.tangent k ^ (3 * π.σ.s₀ / 2) :=
      hTup.trans (mul_le_mul_of_nonneg_left hNκ hKpos.le)
    calc 1000 * (9 * 10 ^ 6 * a.rK k ^ 3) * ((2 : ℝ) ^ (a.ls k ℓ).T * a.tangent k ^ (-π.r))
        ≤ 1000 * (9 * 10 ^ 6 * a.rK k ^ 3) *
            ((a.rK k * a.tangent k ^ (3 * π.σ.s₀ / 2)) * a.tangent k ^ (-π.r)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h2T hw.le
      _ = ((72 * 10 ^ 9 : ℝ) * a.rK k ^ 4) *
            (a.tangent k ^ (3 * π.σ.s₀ / 2) * a.tangent k ^ (-π.r)) / 8 := by ring
      _ ≤ a.tangent k ^ (5 * kap0 π) *
            (a.tangent k ^ (3 * π.σ.s₀ / 2) * a.tangent k ^ (-π.r)) / 8 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hK4 (by positivity)
      _ = a.tangent k ^ (5 * kap0 π + 3 * π.σ.s₀ / 2 + -π.r) / 8 := by
          rw [Real.rpow_add hNpos, Real.rpow_add hNpos, mul_assoc]
      _ ≤ a.tangent k ^ (-π.s') / 8 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
  calc |eval u ((a.ls k ℓ).poly i) - eval u' ((a.ls k ℓ).poly i)|
      ≤ 1000 * (9 * 10 ^ 6 * a.rK k ^ 3) *
          (|a.zeta k ℓ i u 0 - a.zeta k ℓ i u' 0| + |a.zeta k ℓ i u 1 - a.zeta k ℓ i u' 1|) :=
        hlip
    _ ≤ 1000 * (9 * 10 ^ 6 * a.rK k ^ 3) *
          ((2 : ℝ) ^ (a.ls k ℓ).T * a.tangent k ^ (-π.r)) :=
        mul_le_mul_of_nonneg_left hdisp (by positivity)
    _ ≤ a.tangent k ^ (-π.s') / 8 := hfinal


omit ha in
private theorem mem_I_unit {T : ℕ} {j : Fin (2 ^ T)} {t : ℝ} (ht : t ∈ I T j) :
    0 ≤ t ∧ t ≤ 1 := by
  obtain ⟨h0, h1⟩ := ht
  have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hj : ((j : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
    have := Nat.succ_le_of_lt j.isLt
    exact_mod_cast this
  constructor
  · exact le_trans (div_nonneg (Nat.cast_nonneg _) hT.le) h0
  · exact h1.trans ((div_le_one hT).mpr hj)

omit ha in
private theorem baseBox_eq_pi {N r : ℝ} (hN : 0 < N) (q : Fin 2 → ℤ) :
    baseBox N r q = Set.univ.pi (fun e : Fin 2 =>
      Set.Ico ((q e : ℝ) * N ^ (-r)) (((q e : ℝ) + 1) * N ^ (-r))) := by
  have hw : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN _
  ext u
  simp only [baseBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico]
  refine forall_congr' fun e => ?_
  rw [Int.floor_eq_iff, le_div_iff₀ hw, div_lt_iff₀ hw]

omit ha in
private theorem baseBox_measurable {N r : ℝ} (hN : 0 < N) (q : Fin 2 → ℤ) :
    MeasurableSet (baseBox N r q) := by
  rw [baseBox_eq_pi hN]
  exact MeasurableSet.univ_pi (fun e => measurableSet_Ico)

omit ha in
private theorem volume_baseBox {N r : ℝ} (hN : 0 < N) (q : Fin 2 → ℤ) :
    volume (baseBox N r q) = ENNReal.ofReal (N ^ (-r) * N ^ (-r)) := by
  have hw : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN _
  rw [baseBox_eq_pi hN, Real.volume_pi_Ico, Fin.prod_univ_two,
    ← ENNReal.ofReal_mul (by nlinarith)]
  congr 1
  ring

omit ha in
private theorem baseBox_disjoint (N r : ℝ) :
    Pairwise (fun q q' : Fin 2 → ℤ => Disjoint (baseBox N r q) (baseBox N r q')) := by
  intro q q' hne
  rw [Set.disjoint_left]
  intro u hu hu'
  apply hne
  funext e
  exact (hu e).symm.trans (hu' e)

omit ha in
private theorem psi_measurable : Measurable (a.psi k ℓ i) := by
  apply Measurable.of_eval
  intro e
  simp only [psi]
  fun_prop

private theorem psi_volume_preimage (B : Set (Fin 2 → ℝ)) :
    volume (a.psi k ℓ i ⁻¹' B) =
      ENNReal.ofReal (((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 / (12 * a.rK k)) * volume B := by
  have hK : 0 < a.rK k := lt_of_lt_of_le one_pos (ha.tangent_input.2.2.1.1 k)
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun e j => a.psiA k ℓ i e j)
  let L := Matrix.toLin' M
  have hpsi : ∀ ζ, a.psi k ℓ i ζ = L ζ + a.psib k ℓ i := by
    intro ζ
    funext e
    fin_cases e <;>
      simp [L, M, Matrix.toLin'_apply, psi]
  have hdet : LinearMap.det L = 12 * a.rK k / ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 := by
    simp only [L, LinearMap.det_toLin', Matrix.det_fin_two, M, Matrix.of_apply, psiA,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; positivity
  have hpre : a.psi k ℓ i ⁻¹' B = L ⁻¹' ((fun u => u + a.psib k ℓ i) ⁻¹' B) := by
    ext ζ
    simp only [Set.mem_preimage, hpsi]
  rw [hpre, MeasureTheory.Measure.addHaar_preimage_linearMap volume hdet0,
    measure_preimage_add_right, hdet, inv_div, abs_of_pos (by positivity)]


omit ha in
private theorem mass_ratio_bound {N K d s s₀ c₀ θ r s' T2 : ℝ} (hN1 : 1 ≤ N) (hK1 : 1 ≤ K)
    (hT2 : 0 < T2) (hd0 : 0 ≤ d) (hd1 : d < 1) (hθc : 0 < θ * c₀)
    (hs : |s - s₀| ≤ θ * c₀ / 4) (hs' : s' = s₀ + c₀ - θ * c₀) :
    N ^ (-(3 * (θ * c₀))) / (60 * K ^ 3) * (5 * K * N ^ (-2 * r - d * s')) ≤
      (N ^ (-d * c₀ - θ * c₀) / T2 * (N ^ (-d * s) / (K * T2))) *
        (T2 ^ 2 / (12 * K) * (N ^ (-r) * N ^ (-r))) := by
  have hNpos : 0 < N := by linarith
  have hKpos : 0 < K := by linarith
  have h1 : d * (s - s₀) ≤ θ * c₀ / 4 := by
    calc d * (s - s₀) ≤ d * |s - s₀| := mul_le_mul_of_nonneg_left (le_abs_self _) hd0
      _ ≤ 1 * |s - s₀| := mul_le_mul_of_nonneg_right hd1.le (abs_nonneg _)
      _ ≤ θ * c₀ / 4 := by linarith
  have h2 : d * (θ * c₀) ≤ θ * c₀ := by nlinarith
  have hexp : -(3 * (θ * c₀)) + (-2 * r - d * s') ≤
      -d * c₀ - θ * c₀ + -d * s + (-r + -r) := by
    rw [hs']
    linarith
  have key : N ^ (-(3 * (θ * c₀))) * N ^ (-2 * r - d * s') ≤
      N ^ (-d * c₀ - θ * c₀) * N ^ (-d * s) * (N ^ (-r) * N ^ (-r)) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos,
      ← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have hL : N ^ (-(3 * (θ * c₀))) / (60 * K ^ 3) * (5 * K * N ^ (-2 * r - d * s')) =
      N ^ (-(3 * (θ * c₀))) * N ^ (-2 * r - d * s') / (12 * K ^ 2) := by
    field_simp
    ring
  have hR : (N ^ (-d * c₀ - θ * c₀) / T2 * (N ^ (-d * s) / (K * T2))) *
        (T2 ^ 2 / (12 * K) * (N ^ (-r) * N ^ (-r))) =
      N ^ (-d * c₀ - θ * c₀) * N ^ (-d * s) * (N ^ (-r) * N ^ (-r)) / (12 * K ^ 2) := by
    field_simp
  rw [hL, hR]
  exact div_le_div_of_nonneg_right key (by positivity)

omit ha in
private theorem final_numeric {N K xx εc kap : ℝ} (hN1 : 1 ≤ N) (hK1 : 1 ≤ K) (hx : 0 < xx)
    (hKs : K ≤ N ^ kap) (hNl : (10 : ℝ) ^ 30 ≤ N ^ kap) (hkap : 14 * kap + 13 * xx ≤ εc) :
    10 ^ 6 * ((48 / (N ^ (-(3 * xx)) / (60 * K ^ 3))) ^ 4 * (3 * K * N ^ xx)) ≤ N ^ εc := by
  have hNpos : 0 < N := by linarith
  have hKpos : 0 < K := by linarith
  have hA1 : 1 ≤ N ^ xx := Real.one_le_rpow hN1 hx.le
  have hApos : 0 < N ^ xx := by linarith
  have hBpos : 0 < N ^ kap := by linarith
  have h3 : N ^ (-(3 * xx)) = ((N ^ xx) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hNpos.le, show 3 * xx = xx * ((3 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul hNpos.le, Real.rpow_natCast]
  have hε : (N ^ kap) ^ 14 * (N ^ xx) ^ 13 ≤ N ^ εc := by
    have heq : (N ^ kap) ^ 14 * (N ^ xx) ^ 13 = N ^ (14 * kap + 13 * xx) := by
      rw [Real.rpow_add hNpos, show 14 * kap = kap * ((14 : ℕ) : ℝ) by push_cast; ring,
        show 13 * xx = xx * ((13 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul hNpos.le, Real.rpow_mul hNpos.le, Real.rpow_natCast, Real.rpow_natCast]
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hkap
  have hclosed : (10 : ℝ) ^ 6 * ((48 / (((N ^ xx) ^ 3)⁻¹ / (60 * K ^ 3))) ^ 4 *
      (3 * K * N ^ xx)) = (10 ^ 6 * 2880 ^ 4 * 3) * K ^ 13 * (N ^ xx) ^ 13 := by
    field_simp
    ring
  rw [h3, hclosed]
  have hK13 : K ^ 13 ≤ (N ^ kap) ^ 13 := pow_le_pow_left₀ hKpos.le hKs 13
  calc (10 ^ 6 * 2880 ^ 4 * 3 : ℝ) * K ^ 13 * (N ^ xx) ^ 13
      ≤ 10 ^ 30 * (N ^ kap) ^ 13 * (N ^ xx) ^ 13 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (by norm_num) hK13 (by positivity) (by norm_num)
    _ ≤ N ^ kap * (N ^ kap) ^ 13 * (N ^ xx) ^ 13 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hNl (by positivity)
    _ = (N ^ kap) ^ 14 * (N ^ xx) ^ 13 := by ring
    _ ≤ N ^ εc := hε


/-- Each candidate's normalized graph difference is at most `N^{εm c₀}` on the square of
half-width `1` in matching coordinates. -/
theorem Gz_bound (s : ℝ) (hP : a.PlankHyp π k ℓ i s) (m : Fin (a.ncand π k ℓ i)) :
    ∀ z ∈ MatchApply.sq 1, |eval z (a.Gz π k ℓ i m)| ≤ a.tangent k ^ (π.εm * π.σ.c₀) := by
  classical
  obtain ⟨hs0, hc0, hθ, hθε, hεm, hεm1⟩ := hP.par_pos
  obtain ⟨hd0, hd1⟩ := hP.d_range
  obtain ⟨hκ0, hκ1⟩ := hP.κ_range
  have hN2 := hP.N_ge
  have hK1 := hP.K_ge
  have hKs := hP.K_small
  have hNl := hP.N_large
  have hTup := hP.T_upper
  have hsw := hP.s_win
  have hNpos : 0 < a.tangent k := by linarith
  have hN1 : 1 ≤ a.tangent k := by linarith
  have hKpos : 0 < a.rK k := by linarith
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  have hT1 : (1 : ℝ) ≤ (2 : ℝ) ^ (a.ls k ℓ).T := one_le_pow₀ (by norm_num)
  have hθc : 0 < π.θ * π.σ.c₀ := mul_pos hθ hc0
  have hθcle : π.θ * π.σ.c₀ ≤ π.σ.c₀ := by nlinarith
  have hw : 0 < a.tangent k ^ (-π.r) := Real.rpow_pos_of_pos hNpos _
  have hr0 : 0 ≤ π.r := by unfold CmpParams.r; positivity
  have hw1 : a.tangent k ^ (-π.r) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hv : |(a.ls k ℓ).v i| ≤ a.rK k := by
    have := hP.uv_le; linarith [abs_nonneg ((a.ls k ℓ).u i)]
  have huv := hP.uv_le
  have hfitTol : a.fitTol π.θ π.σ k = a.tangent k ^ (-π.s') := by
    unfold fitTol CmpParams.s'; congr 1; ring
  have hs_win2 := hsw.2
  rw [abs_le] at hs_win2
  have hs_win1 := hsw.1
  have hκs : a.κ * s ≤ 3 * π.σ.s₀ / 2 := by nlinarith
  -- base cells are tiny in normalized coordinates
  have h2Tw : (2 : ℝ) ^ (a.ls k ℓ).T * a.tangent k ^ (-π.r) ≤ 1 / 4 := by
    have h2T : (2 : ℝ) ^ (a.ls k ℓ).T ≤
        a.tangent k ^ kap0 π * a.tangent k ^ (3 * π.σ.s₀ / 2) :=
      hTup.trans (mul_le_mul hKs (Real.rpow_le_rpow_of_exponent_le hN1 hκs) (by positivity)
        (by positivity))
    have hexp : kap0 π + 3 * π.σ.s₀ / 2 + -π.r ≤ -2 := by
      unfold kap0 CmpParams.r
      have : (0 : ℝ) ≤ (π.σ.R : ℝ) := Nat.cast_nonneg _
      linarith
    have hN2' : a.tangent k ^ (-2 : ℝ) ≤ 1 / 4 := by
      rw [Real.rpow_neg hNpos.le, Real.rpow_two, inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc (2 : ℝ) ^ (a.ls k ℓ).T * a.tangent k ^ (-π.r)
        ≤ (a.tangent k ^ kap0 π * a.tangent k ^ (3 * π.σ.s₀ / 2)) * a.tangent k ^ (-π.r) :=
          mul_le_mul_of_nonneg_right h2T hw.le
      _ = a.tangent k ^ (kap0 π + 3 * π.σ.s₀ / 2 + -π.r) := by
          rw [Real.rpow_add hNpos, Real.rpow_add hNpos]
      _ ≤ a.tangent k ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hexp
      _ ≤ 1 / 4 := hN2'
  -- facts on the covered incidences
  have hpt : ∀ p ∈ a.cvd π k ℓ i m,
      p.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i) ∧ p.1 ∈ (a.ls k ℓ).prior i ∧
      |x p.1 p.2 - eval (Cells.base p) (a.cand π k ℓ i m)| ≤ a.tangent k ^ (-π.s') ∧
      (∀ e, |Cells.base p e| ≤ 2 * a.rK k) := by
    rintro p ⟨hp1, hp2⟩
    have hprior := asg_subset_prior ha π k ℓ i m hp1
    refine ⟨hp2, hprior, ?_, ?_⟩
    · have := asg_fit ha π k ℓ i m p.1 hp1 p.2 hp2
      rw [hfitTol] at this
      exact this
    · obtain ⟨ht0, ht1⟩ := mem_I_unit hp2
      have hy := (hP.fit p.1 hprior p.2 hp2).1
      have hKT : a.rK k / (2 : ℝ) ^ (a.ls k ℓ).T ≤ a.rK k := div_le_self hKpos.le hT1
      have htv : |p.2 * (a.ls k ℓ).v i| ≤ |(a.ls k ℓ).v i| := by
        rw [abs_mul, abs_of_nonneg ht0]
        nlinarith [abs_nonneg ((a.ls k ℓ).v i)]
      intro e
      fin_cases e
      · simp only [Cells.base, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [abs_of_nonneg ht0]
        linarith
      · simp only [Cells.base, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        calc |y p.1 p.2| = |(y p.1 p.2 - (a.ls k ℓ).u i - p.2 * (a.ls k ℓ).v i) +
              (a.ls k ℓ).u i + p.2 * (a.ls k ℓ).v i| := by ring_nf
          _ ≤ |y p.1 p.2 - (a.ls k ℓ).u i - p.2 * (a.ls k ℓ).v i| + |(a.ls k ℓ).u i| +
              |p.2 * (a.ls k ℓ).v i| := abs_add_three _ _ _
          _ ≤ 2 * a.rK k := by linarith
  -- cell masses
  have hβ : ∀ q : Fin 2 → ℤ, a.ρ k ((a.ls k ℓ).world i)
      (a.cvd π k ℓ i m ∩ {p | baseBin (a.tangent k) π.r p = q}) ≤
      ENNReal.ofReal (5 * a.rK k * a.tangent k ^ (-2 * π.r - a.rd * π.s')) := by
    intro q
    refine Cells.cell_mass_le (a.ρ k ((a.ls k ℓ).world i)) (by linarith : (1 : ℝ) < a.tangent k)
      (Real.rpow_pos_of_pos hNpos _).le le_rfl hP.noncon (a.cand π k ℓ i m) (a.cvd π k ℓ i m)
      (fun p hp => (hpt p hp).2.2.1) ?_ q
    intro p hp p' hp' hbb
    have h := cand_cell_variation ha π k ℓ i s hP m (Cells.base p) (Cells.base p')
      (fun e => ((hpt p hp).2.2.2 e).trans (by linarith))
      (fun e => ((hpt p' hp').2.2.2 e).trans (by linarith))
      (fun e => congrFun hbb e)
    have : 0 ≤ a.tangent k ^ (-π.s') := (Real.rpow_pos_of_pos hNpos _).le
    linarith
  -- normalized images of base cells
  have hcov : a.cvd π k ℓ i m ⊆ ⋃ q, {p : Inc | baseBin (a.tangent k) π.r p = q} :=
    fun p _ => mem_iUnion.2 ⟨_, rfl⟩
  have himg : ∀ q, MeasurableSet (a.psi k ℓ i ⁻¹' baseBox (a.tangent k) π.r q) :=
    fun q => psi_measurable k ℓ i (baseBox_measurable hNpos q)
  have hdisj : Pairwise (fun q q' => Disjoint (a.psi k ℓ i ⁻¹' baseBox (a.tangent k) π.r q)
      (a.psi k ℓ i ⁻¹' baseBox (a.tangent k) π.r q')) :=
    fun q q' hne => (baseBox_disjoint (a.tangent k) π.r hne).preimage _
  have hvol : ∀ q, ENNReal.ofReal (((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 / (12 * a.rK k)) *
      ENNReal.ofReal (a.tangent k ^ (-π.r) * a.tangent k ^ (-π.r)) ≤
      volume (a.psi k ℓ i ⁻¹' baseBox (a.tangent k) π.r q) := by
    intro q
    rw [psi_volume_preimage ha k ℓ i, volume_baseBox hNpos]
  have hmain := Cells.volume_charged_cells (a.ρ k ((a.ls k ℓ).world i)) (a.cvd π k ℓ i m)
    (fun q => {p : Inc | baseBin (a.tangent k) π.r p = q}) hcov _ hβ
    (fun q => a.psi k ℓ i ⁻¹' baseBox (a.tangent k) π.r q) himg hdisj _ hvol
  -- charged cells: normalized images in the unit square, small graph difference
  have hcharged : ∀ ζ ∈ ⋃ (q : Fin 2 → ℤ) (_ : a.ρ k ((a.ls k ℓ).world i)
        (a.cvd π k ℓ i m ∩ {p : Inc | baseBin (a.tangent k) π.r p = q}) ≠ 0),
        a.psi k ℓ i ⁻¹' baseBox (a.tangent k) π.r q,
      ζ ∈ Set.Icc (0 : Fin 2 → ℝ) 1 ∧
        |eval ζ (a.Gzeta π k ℓ i m)| ≤ 3 * a.rK k * a.tangent k ^ (π.θ * π.σ.c₀) := by
    intro ζ hζ
    simp only [mem_iUnion] at hζ
    obtain ⟨q, hq, hζq⟩ := hζ
    obtain ⟨p, hpC, hpq⟩ := nonempty_of_measure_ne_zero hq
    obtain ⟨hpt2, hpprior, hpx, hpb⟩ := hpt p hpC
    have hfitp := hP.fit p.1 hpprior p.2 hpt2
    have hsame : ∀ e, ⌊a.psi k ℓ i ζ e / a.tangent k ^ (-π.r)⌋ =
        ⌊Cells.base p e / a.tangent k ^ (-π.r)⌋ := fun e =>
      (hζq e).trans (congrFun hpq e).symm
    have hdiff : ∀ e, |a.psi k ℓ i ζ e - Cells.base p e| ≤ a.tangent k ^ (-π.r) := fun e =>
      (abs_sub_lt_of_floor_div_eq hw (hsame e)).le
    have hz₁ := zeta_mem_of_fit ha k ℓ i p.1 p.2 hpt2 hfitp.1
    have hdisp := zeta_disp ha k ℓ i hv (a.psi k ℓ i ζ) (Cells.base p) hdiff
    rw [zeta_psi ha k ℓ i ζ] at hdisp
    have hb0 : a.zeta k ℓ i (Cells.base p) 0 ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := hz₁.1
    have hb1 : a.zeta k ℓ i (Cells.base p) 1 ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := hz₁.2
    have hd0' := abs_le.mp (le_trans (le_add_of_nonneg_right (abs_nonneg _)) hdisp)
    have hd1' := abs_le.mp (le_trans (le_add_of_nonneg_left (abs_nonneg _)) hdisp)
    have hζ0 : 0 ≤ ζ 0 ∧ ζ 0 ≤ 1 := by
      obtain ⟨h1, h2⟩ := hb0
      constructor <;> linarith [hd0'.1, hd0'.2]
    have hζ1 : 0 ≤ ζ 1 ∧ ζ 1 ≤ 1 := by
      obtain ⟨h1, h2⟩ := hb1
      constructor <;> linarith [hd1'.1, hd1'.2]
    refine ⟨⟨fun e => ?_, fun e => ?_⟩, ?_⟩
    · fin_cases e
      · exact hζ0.1
      · exact hζ1.1
    · fin_cases e
      · exact hζ0.2
      · exact hζ1.2
    -- the bound
    rw [eval_Gzeta ha π k ℓ i m ζ]
    have hcv := cand_cell_variation ha π k ℓ i s hP m (a.psi k ℓ i ζ) (Cells.base p)
      (fun e => by
        have h1 := hdiff e
        have h2 := hpb e
        have h3 := abs_sub_abs_le_abs_sub (a.psi k ℓ i ζ e) (Cells.base p e)
        linarith)
      (fun e => (hpb e).trans (by linarith)) hsame
    have hpv := poly_cell_variation ha π k ℓ i s hP (Cells.base p) (a.psi k ℓ i ζ)
      (Fin.forall_fin_two.2 ⟨⟨by linarith [hb0.1], by linarith [hb0.2]⟩,
        ⟨by linarith [hb1.1], by linarith [hb1.2]⟩⟩)
      (by
        rw [zeta_psi ha k ℓ i ζ]
        exact Fin.forall_fin_two.2 ⟨⟨by linarith [hζ0.1], by linarith [hζ0.2]⟩,
          ⟨by linarith [hζ1.1], by linarith [hζ1.2]⟩⟩)
      (fun e => (hsame e).symm)
    have hFfit : |x p.1 p.2 - eval (Cells.base p) ((a.ls k ℓ).poly i)| ≤
        a.rK k * a.tangent k ^ (-s) := hfitp.2
    have hdiffPF : |eval (a.psi k ℓ i ζ) (a.cand π k ℓ i m) -
        eval (a.psi k ℓ i ζ) ((a.ls k ℓ).poly i)| ≤
        5 / 4 * a.tangent k ^ (-π.s') + a.rK k * a.tangent k ^ (-s) := by
      have e1 : eval (a.psi k ℓ i ζ) (a.cand π k ℓ i m) -
          eval (a.psi k ℓ i ζ) ((a.ls k ℓ).poly i) =
          (eval (a.psi k ℓ i ζ) (a.cand π k ℓ i m) - eval (Cells.base p) (a.cand π k ℓ i m)) -
          (x p.1 p.2 - eval (Cells.base p) (a.cand π k ℓ i m)) +
          (x p.1 p.2 - eval (Cells.base p) ((a.ls k ℓ).poly i)) +
          (eval (Cells.base p) ((a.ls k ℓ).poly i) - eval (a.psi k ℓ i ζ) ((a.ls k ℓ).poly i)) := by
        ring
      rw [e1]
      have hA := abs_le.mp hcv
      have hB := abs_le.mp hpx
      have hC := abs_le.mp hFfit
      have hD := abs_le.mp hpv
      rw [abs_le]
      constructor <;> linarith
    have hNs : 0 ≤ a.tangent k ^ π.σ.s₀ := (Real.rpow_pos_of_pos hNpos _).le
    have hA1 : 1 ≤ a.tangent k ^ (π.θ * π.σ.c₀) := Real.one_le_rpow hN1 hθc.le
    have he1 : a.tangent k ^ π.σ.s₀ * a.tangent k ^ (-π.s') ≤ 1 := by
      rw [← Real.rpow_add hNpos]
      apply Real.rpow_le_one_of_one_le_of_nonpos hN1
      unfold CmpParams.s'
      linarith
    have he2 : a.tangent k ^ π.σ.s₀ * a.tangent k ^ (-s) ≤ a.tangent k ^ (π.θ * π.σ.c₀) := by
      rw [← Real.rpow_add hNpos]
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have := abs_le.mp hs_win1
      linarith
    rw [abs_mul, abs_of_nonneg hNs]
    calc a.tangent k ^ π.σ.s₀ * |eval (a.psi k ℓ i ζ) (a.cand π k ℓ i m) -
          eval (a.psi k ℓ i ζ) ((a.ls k ℓ).poly i)|
        ≤ a.tangent k ^ π.σ.s₀ * (5 / 4 * a.tangent k ^ (-π.s') + a.rK k * a.tangent k ^ (-s)) :=
          mul_le_mul_of_nonneg_left hdiffPF hNs
      _ = 5 / 4 * (a.tangent k ^ π.σ.s₀ * a.tangent k ^ (-π.s')) +
            a.rK k * (a.tangent k ^ π.σ.s₀ * a.tangent k ^ (-s)) := by ring
      _ ≤ 5 / 4 * 1 + a.rK k * a.tangent k ^ (π.θ * π.σ.c₀) := by
          gcongr
      _ ≤ 3 * a.rK k * a.tangent k ^ (π.θ * π.σ.c₀) := by
          have hKA : 1 ≤ a.rK k * a.tangent k ^ (π.θ * π.σ.c₀) :=
            one_le_mul_of_one_le_of_one_le hK1 hA1
          linarith
  -- mass of the charged set
  have hthr := cvd_mass ha π k ℓ i m
  have hνprob := hP.nu_prob
  have hνfin : ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i) ≠ ⊤ :=
    measure_ne_top _ _
  have hνlow : a.tangent k ^ (-a.rd * s) / (a.rK k * (2 : ℝ) ^ (a.ls k ℓ).T) ≤
      (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hνfin).1 hP.nu_lower
  have hthrLow : a.tangent k ^ (-a.rd * π.σ.c₀ - π.θ * π.σ.c₀) / (2 : ℝ) ^ (a.ls k ℓ).T *
      (a.tangent k ^ (-a.rd * s) / (a.rK k * (2 : ℝ) ^ (a.ls k ℓ).T)) ≤
      a.thr π.θ π.σ k ℓ i := by
    unfold thr
    exact mul_le_mul_of_nonneg_left hνlow (by positivity)
  have hthrLow0 : 0 ≤ a.tangent k ^ (-a.rd * π.σ.c₀ - π.θ * π.σ.c₀) / (2 : ℝ) ^ (a.ls k ℓ).T *
      (a.tangent k ^ (-a.rd * s) / (a.rK k * (2 : ℝ) ^ (a.ls k ℓ).T)) := by positivity
  have hβR : 0 < 5 * a.rK k * a.tangent k ^ (-2 * π.r - a.rd * π.s') := by positivity
  have hmass : ENNReal.ofReal (a.tangent k ^ (-(3 * (π.θ * π.σ.c₀))) / (60 * a.rK k ^ 3)) ≤
      volume (⋃ (q : Fin 2 → ℤ) (_ : a.ρ k ((a.ls k ℓ).world i)
        (a.cvd π k ℓ i m ∩ {p : Inc | baseBin (a.tangent k) π.r p = q}) ≠ 0),
        a.psi k ℓ i ⁻¹' baseBox (a.tangent k) π.r q) := by
    have h1 : ENNReal.ofReal ((a.tangent k ^ (-a.rd * π.σ.c₀ - π.θ * π.σ.c₀) /
          (2 : ℝ) ^ (a.ls k ℓ).T *
          (a.tangent k ^ (-a.rd * s) / (a.rK k * (2 : ℝ) ^ (a.ls k ℓ).T))) *
          (((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 / (12 * a.rK k) *
            (a.tangent k ^ (-π.r) * a.tangent k ^ (-π.r)))) ≤
        ENNReal.ofReal (5 * a.rK k * a.tangent k ^ (-2 * π.r - a.rd * π.s')) *
          volume (⋃ (q : Fin 2 → ℤ) (_ : a.ρ k ((a.ls k ℓ).world i)
            (a.cvd π k ℓ i m ∩ {p : Inc | baseBin (a.tangent k) π.r p = q}) ≠ 0),
            a.psi k ℓ i ⁻¹' baseBox (a.tangent k) π.r q) := by
      rw [ENNReal.ofReal_mul hthrLow0,
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 / (12 * a.rK k) by
          positivity)]
      refine le_trans ?_ hmain
      gcongr
      exact (ENNReal.ofReal_le_ofReal hthrLow).trans hthr
    have h2 := ENNReal.div_le_of_le_mul (h1.trans_eq (mul_comm _ _))
    rw [← ENNReal.ofReal_div_of_pos hβR] at h2
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h2
    rw [le_div_iff₀ hβR]
    exact mass_ratio_bound hN1 hK1 hT hd0 hd1 hθc hs_win1 rfl
  -- Remez, extrapolation and the numerical conclusion
  have hη0 : 0 < a.tangent k ^ (-(3 * (π.θ * π.σ.c₀))) / (60 * a.rK k ^ 3) := by positivity
  have hη1 : a.tangent k ^ (-(3 * (π.θ * π.σ.c₀))) / (60 * a.rK k ^ 3) ≤ 1 := by
    have h1 : a.tangent k ^ (-(3 * (π.θ * π.σ.c₀))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have hK3 : 1 ≤ a.rK k ^ 3 := one_le_pow₀ hK1
    rw [div_le_one (by positivity)]
    linarith
  have hremez := QuadBounds.quad_remez (a.Gzeta π k ℓ i m) (Gzeta_totalDegree ha π k ℓ i m)
    _ hη0 hη1 (by positivity) (fun ζ hζ => (hcharged ζ hζ).1) hmass
    (fun ζ hζ => (hcharged ζ hζ).2)
  have hext := QuadBounds.quad_extrapolate (a.Gzeta π k ℓ i m)
    (Gzeta_totalDegree ha π k ℓ i m) hremez
  have hkap : 14 * kap0 π + 13 * (π.θ * π.σ.c₀) ≤ π.εm * π.σ.c₀ := by
    unfold kap0
    have h1 := mul_le_mul_of_nonneg_right hθε hc0.le
    have hY : 0 < π.εm * π.σ.c₀ := mul_pos hεm hc0
    have h2 : π.εm / 16 * π.σ.c₀ = π.εm * π.σ.c₀ / 16 := by ring
    rw [h2] at h1
    linarith
  have hfin := final_numeric hN1 hK1 hθc hKs hNl hkap
  intro z hz
  rw [eval_Gz ha π k ℓ i m z]
  refine (hext _ ?_).trans hfin
  intro e
  have := abs_le.mp (hz e)
  constructor <;> linarith

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
