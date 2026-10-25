import Submission.Obl.k4_horizontal_wide_interval_return.Core.LayerCompare
import Submission.Obl.k4_horizontal_wide_interval_return.Core.Datum

/-!
# The comparison numerics hold eventually

For the buffered exponents of the datum, the side conditions `CompareNumerics` of the layer
comparison hold for all large indices, with chart width `χ = N^-M`, strip width
`D = N^(-2κ s₀)`, horizontal defect `N^-e₀`, base cells `N^-(M+2τ)` and gain `N^(C_d u)`.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.Core

open MeasureTheory Set Filter

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem eventually_const_le_rpow {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) {c : ℝ} (hc : 0 < c)
    (C : ℝ) : ∀ᶠ k in atTop, C ≤ N k ^ c :=
  ((tendsto_rpow_atTop hc).comp hN).eventually (eventually_ge_atTop C)

theorem eventually_mul_rpow_le {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) {a b : ℝ} (hab : a < b)
    (C : ℝ) : ∀ᶠ k in atTop, C * N k ^ a ≤ N k ^ b := by
  filter_upwards [eventually_const_le_rpow hN (sub_pos.mpr hab) C,
    hN.eventually (eventually_gt_atTop 0)] with k hk hk0
  calc C * N k ^ a ≤ N k ^ (b - a) * N k ^ a :=
        mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hk0.le _)
    _ = N k ^ b := by rw [← Real.rpow_add hk0]; ring_nf

theorem rpow_le_rpow_of_ge {N : ℝ} (hN : 1 ≤ N) {a b : ℝ} (hab : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN hab

/-- The depth increments of the three layers. -/
theorem depth_sub_mem {s u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hvu : v < u) (h : Fin 3) :
    0 ≤ (![s, s + u, s + v] : Fin 3 → ℝ) h - s ∧ (![s, s + u, s + v] : Fin 3 → ℝ) h - s ≤ u := by
  fin_cases h
  · exact ⟨by simp, by simp; linarith⟩
  · exact ⟨by simp; linarith, by simp⟩
  · exact ⟨by simp; linarith, by simp; linarith⟩

theorem cell_alg_inv {x : ℝ} (hx : 4 ≤ x) : x⁻¹ ≤ 1 / 4 ∧ 0 < x⁻¹ ∧
    (1 + x) * (x⁻¹ * x⁻¹) ≤ 1 / 2 ∧ x⁻¹ * x⁻¹ ≤ 1 / 16 := by
  have hx0 : 0 < x := by linarith
  have h1 : x⁻¹ ≤ 1 / 4 := by rw [inv_le_comm₀ hx0 (by norm_num)]; simpa using hx
  have h0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have h2 : x⁻¹ * x⁻¹ ≤ 1 / 16 := by nlinarith
  have h3 : (1 + x) * (x⁻¹ * x⁻¹) = x⁻¹ * x⁻¹ + x⁻¹ := by field_simp
  refine ⟨h1, h0, ?_, h2⟩
  rw [h3]; linarith

theorem cell_alg_fit {x m D : ℝ} (hx : 4 ≤ x) (hm : 0 < m) (hD0 : 0 < D) (hD1 : D ≤ 1) :
    m * x⁻¹ * x⁻¹ + (1 + x) * (m * x⁻¹ * x⁻¹) / (4 * D) ≤ 2 * (m / D) := by
  obtain ⟨h1, h0, h2, h3⟩ := cell_alg_inv hx
  have hmD : m ≤ m / D := by rw [le_div_iff₀ hD0]; nlinarith
  have ha : m * x⁻¹ * x⁻¹ ≤ m := by
    have : x⁻¹ * x⁻¹ ≤ 1 := by linarith
    calc m * x⁻¹ * x⁻¹ = m * (x⁻¹ * x⁻¹) := by ring
      _ ≤ m * 1 := mul_le_mul_of_nonneg_left this hm.le
      _ = m := mul_one m
  have hb : (1 + x) * (m * x⁻¹ * x⁻¹) / (4 * D) ≤ m / D := by
    rw [div_le_div_iff₀ (by positivity) hD0]
    have e : (1 + x) * (m * x⁻¹ * x⁻¹) * D = m * D * ((1 + x) * (x⁻¹ * x⁻¹)) := by ring
    rw [e]
    have : m * D * ((1 + x) * (x⁻¹ * x⁻¹)) ≤ m * D * (1 / 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [mul_pos hm hD0]
  linarith

theorem cell_alg_chart {x m : ℝ} (hx : 4 ≤ x) (hm : 0 < m) (hm1 : m ≤ 1) :
    (x + m + 1) * (m * x⁻¹ * x⁻¹) ≤ m / 2 := by
  obtain ⟨h1, h0, h2, h3⟩ := cell_alg_inv hx
  have e : (x + m + 1) * (m * x⁻¹ * x⁻¹) = m * ((1 + x) * (x⁻¹ * x⁻¹) + m * (x⁻¹ * x⁻¹)) := by
    ring
  rw [e]
  have : (1 + x) * (x⁻¹ * x⁻¹) + m * (x⁻¹ * x⁻¹) ≤ 1 / 2 := by
    have h4 : m * (x⁻¹ * x⁻¹) ≤ 1 * (1 / 16) := mul_le_mul hm1 h3 (by positivity) (by norm_num)
    have h5 : (1 + x) * (x⁻¹ * x⁻¹) = x⁻¹ * x⁻¹ + x⁻¹ := by field_simp
    rw [h5]; linarith
  calc m * ((1 + x) * (x⁻¹ * x⁻¹) + m * (x⁻¹ * x⁻¹)) ≤ m * (1 / 2) :=
        mul_le_mul_of_nonneg_left this hm.le
    _ = m / 2 := by ring

theorem cell_alg_strip {x m D : ℝ} (hx : 4 ≤ x) (hm : 0 < m) (hD0 : 0 < D)
    (h : 2240 * (m / D) ≤ 1) : (1 + x) * (m * x⁻¹ * x⁻¹) ≤ D := by
  obtain ⟨h1, h0, h2, h3⟩ := cell_alg_inv hx
  have e : (1 + x) * (m * x⁻¹ * x⁻¹) = m * ((1 + x) * (x⁻¹ * x⁻¹)) := by ring
  rw [e]
  rw [mul_div_assoc', div_le_iff₀ hD0] at h
  have : m * ((1 + x) * (x⁻¹ * x⁻¹)) ≤ m * (1 / 2) := mul_le_mul_of_nonneg_left h2 hm.le
  linarith

theorem gain_alg {K x A : ℝ} (hK1 : 1 ≤ K) (hK : K ≤ x) (hA : 2000000 * (x * x * (x * x)) ≤ A) :
    1000000 * K * (K + 1) * (x * x) ≤ A := by
  have hx1 : 1 ≤ x := hK1.trans hK
  have hK0 : 0 ≤ K := by linarith
  have h2 : K + 1 ≤ 2 * x := by linarith
  calc 1000000 * K * (K + 1) * (x * x) ≤ 1000000 * x * (2 * x) * (x * x) := by gcongr
    _ = 2000000 * (x * x * (x * x)) := by ring
    _ ≤ A := hA

theorem exp_count {dh s u d : ℝ} (h0 : 0 ≤ dh - s) (h1 : dh - s ≤ u) (hd0 : 0 ≤ d)
    (hd1 : d < 1) : (dh - s) * d ≤ 5 * u := by
  have : (dh - s) * d ≤ (dh - s) * 1 := mul_le_mul_of_nonneg_left hd1.le h0
  have hu : 0 ≤ u := h0.trans h1
  linarith

theorem exp_thick {dh s u d : ℝ} (h0 : 0 ≤ dh - s) (h1 : dh - s ≤ u) (hd0 : 0 ≤ d)
    (hd1 : d < 1) (hus : u * 10 < s * (1 - d)) : -s * ((1 + d) / 2) ≤ -dh * d := by
  have hk : (dh - s) * d ≤ (dh - s) * 1 := mul_le_mul_of_nonneg_left hd1.le h0
  have hpos : 0 ≤ s * (1 - d) := by
    have hu : 0 ≤ u := h0.trans h1
    linarith
  nlinarith

theorem compare_numerics_eventually (cfg : Data α) (hv : cfg.Valid) {buffer s₀ s u v R M : ℝ}
    (hbuf : 100 < buffer) (hdep : Depths cfg buffer s₀ s u v R M) {τ R₀ η : ℝ}
    (hτ : 0 < τ) (hτη : 20 * τ ≤ (10 / (1 - cfg.d)) * u * η) (hη : 0 < η) (h : Fin 3) :
    ∀ᶠ k in atTop, CompareNumerics (cfg.N k) (cfg.K k) cfg.d τ (cfg.N k ^ (-M))
      (cfg.N k ^ (-2 * cfg.κ * s₀)) (cfg.N k ^ (-cfg.e₀)) (M + 2 * τ)
      (cfg.N k ^ (-((![s, s + u, s + v] : Fin 3 → ℝ) 0)))
      (cfg.N k ^ (-((![s, s + u, s + v] : Fin 3 → ℝ) h)))
      (cfg.N k ^ ((10 / (1 - cfg.d)) * u)) R₀ η := by
  have hd0 := hv.dimension_nonneg
  have hd1 := hv.dimension_lt_one
  have hκ0 := hv.rate_pos
  have hκ1 := hv.rate_le_one
  have hNt := hv.resolution_tendsto
  have hs₀ := hdep.s₀_pos
  have hu := hdep.u_pos
  have hvv := hdep.v_pos
  have hvu := hdep.v_lt_u
  have hss : s₀ < s := hdep.s₀_lt
  have hsu : s + u < 3 * s₀ / 2 := hdep.su_lt
  have hM : buffer * s₀ < M := hdep.M_gt
  have he : buffer * M < cfg.e₀ := hdep.M_e
  have hCd : 0 < 10 / (1 - cfg.d) := by apply div_pos (by norm_num); linarith
  have hgain : 0 < (10 / (1 - cfg.d)) * u := mul_pos hCd hu
  obtain ⟨huh0, huh1⟩ := depth_sub_mem (s := s) hu hvv hvu h
  set dh := (![s, s + u, s + v] : Fin 3 → ℝ) h with hdh
  have hd0' : (![s, s + u, s + v] : Fin 3 → ℝ) 0 = s := rfl
  rw [hd0']
  -- the fine scales sit far below the layer depths
  have hκs : cfg.κ * s₀ ≤ s₀ := by nlinarith
  have hbs : 100 * s₀ < buffer * s₀ := by nlinarith
  have hMs : 2 * cfg.κ * s₀ + s + u < M := by nlinarith
  have hMpos : 0 < M := by linarith
  have hbM : M < buffer * M := by nlinarith
  have heM : M < cfg.e₀ := by linarith
  have hus : u < s * (1 - cfg.d) / 10 := by
    have hw := hdep.wide_h
    have h1 : 10 / (1 - cfg.d) * u < cfg.κ * s := by nlinarith
    have h2 : cfg.κ * s ≤ s := by nlinarith
    have h3 : 10 / (1 - cfg.d) * u < s := by linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)] at h3
    rw [lt_div_iff₀ (by norm_num)]
    nlinarith
  filter_upwards [hNt.eventually (eventually_gt_atTop 1),
    eventually_mul_rpow_le hNt (a := -M) (b := -(2 * cfg.κ * s₀ + s)) (by linarith) 1920,
    eventually_mul_rpow_le hNt (a := -cfg.e₀) (b := -(2 * cfg.κ * s₀ + s)) (by linarith) 1920,
    eventually_const_le_rpow hNt (c := τ) hτ 4,
    eventually_mul_rpow_le hNt (a := -M + 2 * cfg.κ * s₀) (b := -dh) (by linarith) 2240,
    eventually_const_le_rpow hNt (c := (10 / (1 - cfg.d)) * u) hgain R₀,
    eventually_const_le_rpow hNt (c := (10 / (1 - cfg.d)) * u * η - 4 * τ)
      (by nlinarith) 2000000,
    hv.loss_subpower τ hτ] with k hN1 hdrift1 hdrift2 hNτ hfit hR₀ hA hK
  set N := cfg.N k with hNdef
  have hN0 : 0 < N := by linarith
  have hNτ1 : 1 ≤ N ^ τ := Real.one_le_rpow hN1.le hτ.le
  have hK1 := hv.loss_lower k
  have hrp : ∀ x : ℝ, 0 < N ^ x := fun x => Real.rpow_pos_of_pos hN0 x
  have hsplit : ∀ x y : ℝ, N ^ (x + y) = N ^ x * N ^ y := fun x y => Real.rpow_add hN0 x y
  -- basic scales
  have hDa : N ^ (-2 * cfg.κ * s₀) * N ^ (-s) = N ^ (-(2 * cfg.κ * s₀ + s)) := by
    rw [← hsplit]; ring_nf
  have hr : N ^ (-(M + 2 * τ)) = N ^ (-M) * (N ^ τ)⁻¹ * (N ^ τ)⁻¹ := by
    rw [show -(M + 2 * τ) = -M + -τ + -τ by ring, hsplit, hsplit, Real.rpow_neg hN0.le τ]
  have hχ1 : N ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by linarith)
  have hD1 : N ^ (-2 * cfg.κ * s₀) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by nlinarith)
  have hq : N ^ (-M + 2 * cfg.κ * s₀) = N ^ (-M) / N ^ (-2 * cfg.κ * s₀) := by
    rw [show -M + 2 * cfg.κ * s₀ = -M - (-2 * cfg.κ * s₀) by ring, Real.rpow_sub hN0]
  have hX : N ^ (-(M + 2 * τ)) + (1 + N ^ τ) * N ^ (-(M + 2 * τ)) / (4 * N ^ (-2 * cfg.κ * s₀)) ≤
      2 * N ^ (-M + 2 * cfg.κ * s₀) := by
    rw [hr, hq]; exact cell_alg_fit hNτ (hrp _) (hrp _) hD1
  have hdh : N ^ (-dh) ≤ N ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
  have hfit' : 2240 * N ^ (-M + 2 * cfg.κ * s₀) ≤ N ^ (-dh) := hfit
  have hdh1 : N ^ (-dh) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by linarith)
  have h1920a : 1920 * N ^ (-M) ≤ N ^ (-(2 * cfg.κ * s₀ + s)) := hdrift1
  have h1920b : 1920 * N ^ (-cfg.e₀) ≤ N ^ (-(2 * cfg.κ * s₀ + s)) := hdrift2
  refine
    { N_gt := hN1
      eps_pos := hτ
      d_nonneg := hd0
      d_lt := hd1
      K_one := hK1
      χ_pos := hrp _
      D_pos := hrp _
      D_le := hD1
      ζ₀_nonneg := (hrp _).le
      a_pos := hrp _
      a_le := Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by linarith)
      ah_pos := hrp _
      ah_le := hdh
      drift := ?_
      close := ?_
      cell_chart := ?_
      cell_half := ?_
      cell_strip := ?_
      cell_fit := ?_
      cell_jet := ?_
      gain_one := Real.one_le_rpow hN1.le hgain.le
      gain_R₀ := hR₀
      gain_A := ?_
      gain_count := ?_
      thick_count := ?_ }
  · -- drift
    rw [hDa]
    linarith [hrp (-(2 * cfg.κ * s₀ + s)), hrp (-M), hrp (-cfg.e₀)]
  · -- close
    rw [div_le_iff₀ (hrp _), mul_comm (N ^ (-s)), hDa]
    linarith [hrp (-(2 * cfg.κ * s₀ + s)), hrp (-M), hrp (-cfg.e₀)]
  · -- cell_chart
    rw [hr]; exact cell_alg_chart hNτ (hrp _) hχ1
  · -- cell_half
    rw [hr]
    obtain ⟨h1, h0, -, h3⟩ := cell_alg_inv hNτ
    have : N ^ (-M) * (N ^ τ)⁻¹ * (N ^ τ)⁻¹ = N ^ (-M) * ((N ^ τ)⁻¹ * (N ^ τ)⁻¹) := by ring
    rw [this]
    have h4 : N ^ (-M) * ((N ^ τ)⁻¹ * (N ^ τ)⁻¹) ≤ 1 * (1 / 16) :=
      mul_le_mul hχ1 h3 (by positivity) (by norm_num)
    linarith
  · -- cell_strip
    rw [hr]
    apply cell_alg_strip hNτ (hrp _) (hrp _)
    rw [← hq]; linarith
  · -- cell_fit
    linarith
  · -- cell_jet
    linarith [hrp (-s)]
  · -- gain_A
    have hpow : N ^ (2 * τ) = N ^ τ * N ^ τ := by rw [← hsplit]; ring_nf
    have h4 : N ^ (4 * τ) = N ^ τ * N ^ τ * (N ^ τ * N ^ τ) := by
      rw [show 4 * τ = (τ + τ) + (τ + τ) by ring, hsplit, hsplit]
    have hA' : 2000000 * N ^ (4 * τ) ≤ N ^ (10 / (1 - cfg.d) * u * η) := by
      have := mul_le_mul_of_nonneg_right hA (hrp (4 * τ)).le
      rw [← hsplit] at this
      convert this using 2; ring
    rw [hpow, ← Real.rpow_mul hN0.le]
    rw [h4] at hA'
    exact gain_alg hK1 hK hA'
  · -- gain_count
    have hq' : N ^ (-s) / N ^ (-dh) = N ^ (dh - s) := by
      rw [← Real.rpow_sub hN0]; ring_nf
    rw [hq', ← Real.rpow_mul hN0.le, ← Real.rpow_mul hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1.le
    have hne : 1 - cfg.d ≠ 0 := (sub_pos.mpr hd1).ne'
    have e : 10 / (1 - cfg.d) * u * ((1 - cfg.d) / 2) = 5 * u := by
      field_simp; ring
    rw [e]
    exact exp_count huh0 huh1 hd0 hd1
  · -- thick_count
    rw [← Real.rpow_mul hN0.le, ← Real.rpow_mul hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1.le
    exact exp_thick huh0 huh1 hd0 hd1 (by linarith [hus])

end

end Submission.Obl.k4_horizontal_wide_interval_return.Core
