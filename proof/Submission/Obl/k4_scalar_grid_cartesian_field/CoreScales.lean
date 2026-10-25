import Submission.Obl.k4_scalar_grid_cartesian_field.Growth

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Filter

/-- A fixed degree can be chosen before taking the asymptotic limit. -/
theorem exists_qualification_degree {κ : ℝ} (hκ : 0 < κ) :
    ∃ M : ℕ, 2 ≤ M ∧ 2 ≤ κ * (M : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (2 / κ)
  refine ⟨max 2 m, le_max_left _ _, ?_⟩
  have hm' : 2 / κ ≤ (max 2 m : ℕ) := hm.trans (by exact_mod_cast le_max_right 2 m)
  have h := (div_le_iff₀ hκ).mp hm'
  nlinarith

/-- Subpower packet losses place the physical horizon between two fixed powers. -/
theorem horizon_power_bounds {N K κ h : ℝ} (hN : 2 ≤ N) (hK : 0 < K)
    (hκ : κ ≤ 1) (hK₁ : K ≤ N ^ ((1 : ℝ) / 6)) (hKκ : K ≤ N ^ (κ / 2))
    (hlo : N ^ (-κ) / K ≤ h) (hhi : h ≤ K * N ^ (-κ)) :
    N ^ (-(7 : ℝ) / 6) ≤ h ∧ h ≤ N ^ (-κ / 2) := by
  have hNp : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  constructor
  · calc
      _ = N ^ (-1 : ℝ) / N ^ ((1 : ℝ) / 6) := by
        rw [← Real.rpow_sub hNp]
        congr 1
        norm_num
      _ ≤ N ^ (-κ) / K := by
        apply div_le_div₀ (Real.rpow_nonneg hNp.le _)
          (Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)) hK hK₁
      _ ≤ _ := hlo
  · calc
      _ ≤ K * N ^ (-κ) := hhi
      _ ≤ N ^ (κ / 2) * N ^ (-κ) := mul_le_mul_of_nonneg_right hKκ (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring

/-- The target derivative error is itself one of the fixed compact-range graph scales. -/
theorem field_error_exponent {N h : ℝ} (hN : 2 ≤ N) (hh : 0 < h) (hhone : h ≤ 1)
    (hlo : N ^ (-(7 : ℝ) / 6) ≤ h) :
    ∃ rT : ℝ, (1 : ℝ) / 8 ≤ rT ∧ rT ≤ 1 ∧
      N ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4) = N ^ (-rT) := by
  have hNp : 0 < N := by linarith
  have hN₁ : 1 < N := by linarith
  let εT := N ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4)
  have hεpos : 0 < εT := by dsimp [εT]; positivity
  have hεlo : N ^ (-1 : ℝ) ≤ εT := by
    apply le_mul_of_one_le_right (Real.rpow_nonneg hNp.le _)
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hhone (by norm_num)
  have hεhi : εT ≤ N ^ (-(1 : ℝ) / 8) := by
    calc
      _ ≤ N ^ (-1 : ℝ) * (N ^ (-(7 : ℝ) / 6)) ^ (-(3 : ℝ) / 4) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hNp.le _)
        exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNp _) hlo (by norm_num)
      _ = _ := by
        rw [← Real.rpow_mul hNp.le, ← Real.rpow_add hNp]
        congr 1
        norm_num
  let rT := -Real.logb N εT
  refine ⟨rT, ?_, ?_, ?_⟩
  · have hx := (Real.logb_le_iff_le_rpow hN₁ hεpos).mpr hεhi
    dsimp [rT]
    linarith
  · have hx := (Real.le_logb_iff_rpow_le hN₁ hεpos).mpr hεlo
    dsimp [rT]
    linarith
  · dsimp [rT]
    rw [neg_neg, Real.rpow_logb hNp hN₁.ne' hεpos]

noncomputable def fieldError (N h : ℝ) : ℝ := N ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4)

/-- The fixed numerical scale conditions of the Cartesian core. -/
structure CorePrecision (N Λ h : ℝ) (M : ℕ) (B : ℝ) : Prop where
  fit : h ^ M ≤ fieldError N h
  graph : Λ * N ^ (-40 : ℝ) ≤ fieldError N h
  layer : Λ ^ 2 * N ^ (-1 : ℝ) ≤ fieldError N h
  base : Λ ^ 4 * N ^ (-10 : ℝ) ≤ fieldError N h
  velocity : Λ ^ 2 * N ^ (-20 : ℝ) ≤ N ^ (-10 : ℝ)
  fine : Λ ^ 4 * N ^ (-B) ≤ N ^ (-10 : ℝ) * h

/-- All fixed core precisions follow from positive powers, uniformly over original horizons. -/
theorem core_precision_of_power_bounds {N Λ κ h B : ℝ} {M : ℕ}
    (hN : 2 ≤ N) (hΛ : 1 ≤ Λ) (hκ : 0 < κ) (hκM : 2 ≤ κ * (M : ℝ))
    (hh : 0 < h) (hhone : h ≤ 1) (hlo : N ^ (-(7 : ℝ) / 6) ≤ h)
    (hhi : h ≤ N ^ (-κ / 2)) (hΛ₄ : Λ ^ 4 ≤ N) (hΛ₂ : Λ ^ 2 ≤ N ^ (κ / 4))
    (hB : 50 ≤ B) : CorePrecision N Λ h M B := by
  have hNp : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hΛN : Λ ≤ N := by
    have hp : Λ ^ 1 ≤ Λ ^ 4 := pow_le_pow_right₀ hΛ (by norm_num)
    simpa only [pow_one] using hp.trans hΛ₄
  have hΛ₂N : Λ ^ 2 ≤ N := (pow_le_pow_right₀ hΛ (show 2 ≤ 4 by norm_num)).trans hΛ₄
  have hfactor : 1 ≤ h ^ (-(3 : ℝ) / 4) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hhone (by norm_num)
  have hδ : N ^ (-1 : ℝ) ≤ fieldError N h :=
    le_mul_of_one_le_right (Real.rpow_nonneg hNp.le _) hfactor
  have hmul (t : ℝ) : N * N ^ t = N ^ (1 + t) := by rw [Real.rpow_add hNp, Real.rpow_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ (N ^ (-κ / 2)) ^ M := pow_le_pow_left₀ hh.le hhi _
      _ = N ^ ((-κ / 2) * (M : ℝ)) := by rw [← Real.rpow_mul_natCast hNp.le]
      _ ≤ N ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN₁ (by nlinarith)
      _ ≤ _ := hδ
  · calc
      _ ≤ N * N ^ (-40 : ℝ) := mul_le_mul_of_nonneg_right hΛN (Real.rpow_nonneg hNp.le _)
      _ = N ^ (-39 : ℝ) := by rw [hmul]; norm_num
      _ ≤ N ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN₁ (by norm_num)
      _ ≤ _ := hδ
  · have hfac : N ^ (3 * κ / 8) ≤ h ^ (-(3 : ℝ) / 4) := by
      calc
        _ = (N ^ (-κ / 2)) ^ (-(3 : ℝ) / 4) := by
          rw [← Real.rpow_mul hNp.le]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos hh hhi (by norm_num)
    have hbound : Λ ^ 2 ≤ h ^ (-(3 : ℝ) / 4) := hΛ₂.trans
      ((Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)).trans hfac)
    calc
      _ ≤ h ^ (-(3 : ℝ) / 4) * N ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hNp.le _)
      _ = _ := by unfold fieldError; ring
  · calc
      _ ≤ N * N ^ (-10 : ℝ) := mul_le_mul_of_nonneg_right hΛ₄ (Real.rpow_nonneg hNp.le _)
      _ = N ^ (-9 : ℝ) := by rw [hmul]; norm_num
      _ ≤ N ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN₁ (by norm_num)
      _ ≤ _ := hδ
  · calc
      _ ≤ N * N ^ (-20 : ℝ) := mul_le_mul_of_nonneg_right hΛ₂N (Real.rpow_nonneg hNp.le _)
      _ = N ^ (-19 : ℝ) := by rw [hmul]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN₁ (by norm_num)
  · have hlo₂ : N ^ (-2 : ℝ) ≤ h :=
      (Real.rpow_le_rpow_of_exponent_le hN₁ (by norm_num : (-2 : ℝ) ≤ -7 / 6)).trans hlo
    calc
      _ ≤ N * N ^ (-B) := mul_le_mul_of_nonneg_right hΛ₄ (Real.rpow_nonneg hNp.le _)
      _ = N ^ (1 - B) := by simpa only [sub_eq_add_neg] using hmul (-B)
      _ ≤ N ^ (-12 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)
      _ = N ^ (-10 : ℝ) * N ^ (-2 : ℝ) := by rw [← Real.rpow_add hNp]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo₂ (Real.rpow_nonneg hNp.le _)

/-- Subpower losses satisfy all the fixed scale inequalities before any packet is selected. -/
theorem core_precision_eventually (data : Data) (hs : scaleHyp data)
    {Λ : ℕ → ℝ} (hΛ : subpower data Λ) {M : ℕ} (hM : 2 ≤ data.κ * (M : ℝ))
    {B : ℝ} (hB : 50 ≤ B) :
    ∀ᶠ k in atTop, ∀ h : ℝ, 0 < h → h ≤ 1 →
      data.N k ^ (-data.κ) / data.K k ≤ h → h ≤ data.K k * data.N k ^ (-data.κ) →
      CorePrecision (data.N k) (Λ k) h M B := by
  have hκ : 0 < data.κ := hs.2.2.2.2.2.1
  have hκone : data.κ ≤ 1 := hs.2.2.2.2.2.2.1
  have hK := hs.2.2.1
  have hΛ₄ := eventually_polynomial_subpower_le (fun k => by linarith [hs.1 k]) hs.2.1 hΛ
    (show (1 : ℝ) ≤ 1 from le_rfl) 4 (show (0 : ℝ) < 1 by norm_num)
  have hΛ₂ := eventually_polynomial_subpower_le (fun k => by linarith [hs.1 k]) hs.2.1 hΛ
    (show (1 : ℝ) ≤ 1 from le_rfl) 2 (show 0 < data.κ / 4 by positivity)
  filter_upwards [hK.2 (1 / 6) (by norm_num), hK.2 (data.κ / 2) (by positivity), hΛ₄, hΛ₂]
    with k hK₁ hKκ h₄ h₂
  intro h hh hhone hlo hhi
  obtain ⟨hpowerlo, hpowerhi⟩ := horizon_power_bounds (hs.1 k)
    (by linarith [hK.1 k] : 0 < data.K k) hκone hK₁ hKκ hlo hhi
  apply core_precision_of_power_bounds (hs.1 k) (hΛ.1 k) hκ hM hh hhone hpowerlo hpowerhi
    (by simpa only [one_mul, Real.rpow_one] using h₄) (by simpa only [one_mul] using h₂) hB

end Submission.Obl.k4_scalar_grid_cartesian_field
