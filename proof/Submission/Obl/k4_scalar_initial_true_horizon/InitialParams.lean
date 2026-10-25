import Submission.Obl.k4_scalar_initial_true_horizon.InitialWorld
import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic
import Submission.Obl.k4_scalar_initial_true_horizon.InitialPriorPlank
import Submission.Obl.k4_scalar_initial_true_horizon.Basic

/-!
# Parameters of the initial atlas and the world bound at each sample

Block length `q = 2^-T` with `T = ⌈L log₂ N⌉`, finest cell level `kmax = ⌈κ log₂ N⌉` with
`κ = 2M + |f(L)| + 4`, slope doubling `r = ⌈log₂ (K + 1)⌉`, short-trajectory threshold
`φ₀ = N^(-ε/8)`, floor `Φf = N^(-f(L)) q N^(-ε)`, and density threshold
`2 c₀ = N^(-f(L) - ε/4)`.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff spatial hidden obsL)

noncomputable def Tpar (p : Data) (k : ℕ) : ℕ := ⌈L p * Real.logb 2 (N p k)⌉₊

noncomputable def kappaPar (p : Data) : ℝ := 2 * (M p : ℝ) + |profile p (L p)| + 4

noncomputable def kmaxPar (p : Data) (k : ℕ) : ℕ := ⌈kappaPar p * Real.logb 2 (N p k)⌉₊

noncomputable def rPar (p : Data) (k : ℕ) : ℕ := ⌈1 * Real.logb 2 (K p k + 1)⌉₊

noncomputable def qPar (p : Data) (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ Tpar p k

noncomputable def floorPar (p : Data) (k : ℕ) (ε : ℝ) : ℝ :=
  N p k ^ (-profile p (L p)) * qPar p k * N p k ^ (-ε)

section basic

variable {p : Data} (hp : Exact p) (k : ℕ)
include hp

theorem Exact.N_pos : 0 < N p k := lt_of_lt_of_le (by norm_num) (hp.resolution_ge k)

theorem Exact.N_one_le : 1 ≤ N p k := le_trans (by norm_num) (hp.resolution_ge k)

theorem Exact.logb_N_nonneg : 0 ≤ Real.logb 2 (N p k) :=
  Real.logb_nonneg (by norm_num) (hp.N_one_le k)

theorem qPar_pos : 0 < qPar p k := by unfold qPar; positivity

theorem qPar_mul_two_pow : qPar p k * 2 ^ Tpar p k = 1 := by
  unfold qPar; field_simp

theorem two_pow_Tpar_ge : N p k ^ L p ≤ (2 : ℝ) ^ Tpar p k :=
  two_pow_ceil_logb_ge (hp.N_pos k)

theorem two_pow_Tpar_le : (2 : ℝ) ^ Tpar p k ≤ 2 * N p k ^ L p :=
  two_pow_ceil_logb_le (hp.N_pos k) (mul_nonneg hp.length_pos.le (hp.logb_N_nonneg k))

theorem qPar_le_aL : qPar p k ≤ N p k ^ (-L p) := by
  unfold qPar
  rw [Real.rpow_neg (hp.N_pos k).le, ← one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (hp.N_pos k) _) (two_pow_Tpar_ge hp k)

theorem kappaPar_pos : 0 < kappaPar p := by unfold kappaPar; positivity

theorem two_pow_kmax_ge : N p k ^ kappaPar p ≤ (2 : ℝ) ^ kmaxPar p k :=
  two_pow_ceil_logb_ge (hp.N_pos k)

theorem two_pow_kmax_le : (2 : ℝ) ^ kmaxPar p k ≤ 2 * N p k ^ kappaPar p :=
  two_pow_ceil_logb_le (hp.N_pos k) (mul_nonneg (kappaPar_pos hp).le (hp.logb_N_nonneg k))

theorem two_pow_rPar_ge : K p k + 1 ≤ (2 : ℝ) ^ rPar p k := by
  have h := two_pow_ceil_logb_ge (x := K p k + 1) (a := 1) (by linarith [hp.slack_ge k])
  rwa [Real.rpow_one] at h

theorem two_pow_rPar_le : (2 : ℝ) ^ rPar p k ≤ 2 * (K p k + 1) := by
  have h := two_pow_ceil_logb_le (x := K p k + 1) (a := 1) (by linarith [hp.slack_ge k])
    (by rw [one_mul]; exact Real.logb_nonneg (by norm_num) (by linarith [hp.slack_ge k]))
  rwa [Real.rpow_one] at h

end basic

/-- The world bound at one sample, with the initial parameters. -/
theorem world_bound_at {p : Data} (hp : Exact p) (k : ℕ) (a : Fin (worlds p k)) {ε : ℝ}
    (hε : 0 < ε)
    (hRd : (N p k ^ (2 * (M p : ℝ)) * 8 * N p k ^ (-L p) * (2 * K p k) ^ 2) *
        (qPar p k / 2 ^ kmaxPar p k) ≤
      30 * 2 ^ rPar p k * floorPar p k ε / N p k ^ (-(ε / 8))) :
    mu p k a univ ≤
      mu p k a (covInc (mu p k a) (N p k ^ (M p : ℝ)) (K p k) (N p k ^ (-L p)) (qPar p k)
          (floorPar p k ε) (Tpar p k) (kmaxPar p k)) +
        ENNReal.ofReal (N p k ^ (-(ε / 8))) +
        ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ≥0∞) *
          ENNReal.ofReal (groupCoef (qPar p k) (floorPar p k ε) (N p k ^ (-(ε / 8)))
            (N p k ^ (-profile p (L p) - ε / 4) / 2) (kmaxPar p k) (rPar p k)) +
        2 * mu p k a {z | density p k a (L p) (obsL (N p k ^ (-L p)) z) <
          ENNReal.ofReal (2 * (N p k ^ (-profile p (L p) - ε / 4) / 2))} := by
  haveI := hp.prior_probability k a
  have hN := hp.N_pos k
  have hK : 0 ≤ K p k := by linarith [hp.slack_ge k]
  have hlaw := hp.observation_law k a hp.length_pos.le le_rfl
  have hEn : ∀ z ∈ event p k a, (z.1.1 : ℝ) ≤ N p k ^ (M p : ℝ) :=
    ((hp.2.1 k).2.2.2.1 a).2.2.2.2.2.1
  refine world_uncovered_le (prior p k a) (hp.event_measurable k a) (hp.event_time k a) hEn
    (hp.prior_coefficients k a) (density p k a (L p)) hlaw.1 hlaw.2 (Tpar p k)
    (qPar_mul_two_pow hp k) (Real.rpow_pos_of_pos hN _) (qPar_le_aL hp k) hK
    (by unfold floorPar; have := qPar_pos hp k; positivity)
    (Real.rpow_pos_of_pos hN _) (by positivity) (kmaxPar p k) (rPar p k)
    (two_pow_rPar_ge hp k) (Rd := N p k ^ (2 * (M p : ℝ)) * 8 * N p k ^ (-L p) * (2 * K p k) ^ 2)
    ?_ hRd
  intro j m l₀ w hw
  have h := hp.prior_plank_mass_le k a (Nb := N p k ^ (M p : ℝ)) (t₀ := j * qPar p k)
    (aL := N p k ^ (-L p)) hK (Real.rpow_pos_of_pos hN _) (qPar_pos hp k) hw.le m l₀
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · rfl
  · congr 1; ring

/-- Closed form of the group constant for the initial parameters. -/
theorem groupCoef_initial {Nk q y ε : ℝ} (hN : 0 < Nk) (hq : 0 < q) (hy : 0 < y) (kmax r : ℕ) :
    groupCoef q (y * q * Nk ^ (-ε)) (Nk ^ (-(ε / 8))) (y * Nk ^ (-(ε / 4)) / 2) kmax r =
      1920 * 4 ^ r * (kmax + r + 3) * Nk ^ (-(ε / 2)) := by
  set x := Nk ^ (-(ε / 8)) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos hN _
  have h8 : Nk ^ (-ε) = x ^ 8 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; push_cast; ring
  have h2 : Nk ^ (-(ε / 4)) = x ^ 2 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; push_cast; ring
  have h4 : Nk ^ (-(ε / 2)) = x ^ 4 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; push_cast; ring
  rw [h8, h2, h4, groupCoef]
  have h4r : (4 : ℝ) ^ r = 2 ^ r * 2 ^ r := by rw [← mul_pow]; norm_num
  rw [h4r]
  field_simp
  ring

/-- `N^(-a) ≤ N^(-δ) / C` as soon as `C ≤ N^(a - δ)`. -/
theorem rpow_neg_le_of_le {Nk a δ C : ℝ} (hN : 0 < Nk) (hC : 0 < C) (h : C ≤ Nk ^ (a - δ)) :
    Nk ^ (-a) ≤ Nk ^ (-δ) / C := by
  rw [le_div_iff₀ hC]
  calc Nk ^ (-a) * C ≤ Nk ^ (-a) * Nk ^ (a - δ) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hN.le _)
    _ = Nk ^ (-δ) := by rw [← Real.rpow_add hN]; congr 1; ring

/-- **The initial loss budget.** -/
theorem eventually_initial_budget {p : Data} (hp : Exact p) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ k in atTop,
      N p k ^ (-ε) + N p k ^ (-(ε / 8)) +
        ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ) *
          (1920 * 4 ^ rPar p k * (kmaxPar p k + rPar p k + 3) * N p k ^ (-(ε / 2))) +
        2 * N p k ^ (-c) ≤ (K p k)⁻¹ := by
  set δ := min ε c / 100 with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos (lt_min hε hc) (by norm_num)
  have hδε : δ ≤ ε / 100 := by rw [hδ]; gcongr; exact min_le_left _ _
  have hδc : δ ≤ c / 100 := by rw [hδ]; gcongr; exact min_le_right _ _
  have hNt := hp.resolution_tendsto
  filter_upwards [hp.slack_subpower δ hδpos,
    eventually_logb_le_rpow hNt hδpos (kappaPar p),
    eventually_const_le_rpow hNt (a := ε - δ) (by linarith) 4,
    eventually_const_le_rpow hNt (a := ε / 8 - δ) (by linarith) 4,
    eventually_const_le_rpow hNt (a := ε / 2 - 5 * δ) (by linarith) (4 * 3041280),
    eventually_const_le_rpow hNt (a := c - δ) (by linarith) 8] with k hK hlog h1 h2 h3 h4
  have hN := hp.N_pos k
  have hN1 := hp.N_one_le k
  have hK1 : 1 ≤ K p k := hp.slack_ge k
  have hNδ1 : 1 ≤ N p k ^ δ := Real.one_le_rpow hN1 hδpos.le
  -- `1/K ≥ N^-δ`
  have hKinv : N p k ^ (-δ) ≤ (K p k)⁻¹ := by
    rw [Real.rpow_neg hN.le]
    exact inv_anti₀ (by linarith) hK
  -- the counting factors
  have hc1 : ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ) ≤ 11 * K p k := by
    have hceil : (⌈3 * K p k⌉ : ℝ) ≤ 3 * K p k + 1 := (Int.ceil_lt_add_one _).le
    have hnn : 0 ≤ 2 * (⌈3 * K p k⌉ + 1) + 1 := by
      have := Int.ceil_nonneg (show (0 : ℝ) ≤ 3 * K p k by linarith); omega
    have : ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ) = ((2 * (⌈3 * K p k⌉ + 1) + 1 : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    rw [this]; push_cast; linarith
  have hr2 : (2 : ℝ) ^ rPar p k ≤ 4 * K p k := by
    have := two_pow_rPar_le hp k; linarith
  have h4r : (4 : ℝ) ^ rPar p k ≤ 16 * K p k ^ 2 := by
    have : (4 : ℝ) ^ rPar p k = (2 ^ rPar p k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    calc ((2 : ℝ) ^ rPar p k) ^ 2 ≤ (4 * K p k) ^ 2 := by gcongr
      _ = 16 * K p k ^ 2 := by ring
  have hrK : (rPar p k : ℝ) ≤ 4 * K p k := by
    have : (rPar p k : ℝ) ≤ 2 ^ rPar p k := by
      exact_mod_cast (Nat.lt_two_pow_self).le
    linarith
  have hkmax : (kmaxPar p k : ℝ) ≤ N p k ^ δ + 1 := by
    have := ceil_logb_le (x := N p k) (a := kappaPar p)
      (mul_nonneg (kappaPar_pos hp).le (hp.logb_N_nonneg k))
    unfold kmaxPar; linarith
  have hsum : (kmaxPar p k : ℝ) + rPar p k + 3 ≤ 9 * N p k ^ δ := by linarith
  have hprod : ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ) *
      (1920 * 4 ^ rPar p k * (kmaxPar p k + rPar p k + 3)) ≤ 3041280 * N p k ^ (4 * δ) := by
    have hK3 : K p k ^ 3 ≤ (N p k ^ δ) ^ 3 := by gcongr
    have hpow : (N p k ^ δ) ^ 4 = N p k ^ (4 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; push_cast; ring
    calc ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ) * (1920 * 4 ^ rPar p k * (kmaxPar p k + rPar p k + 3))
        ≤ (11 * K p k) * (1920 * (16 * K p k ^ 2) * (9 * N p k ^ δ)) := by
          have hS0 : (0 : ℝ) ≤ (kmaxPar p k : ℝ) + rPar p k + 3 := by positivity
          refine mul_le_mul hc1 (mul_le_mul (mul_le_mul_of_nonneg_left h4r (by norm_num))
            hsum hS0 (by positivity)) (by positivity) (by positivity)
      _ = 3041280 * (K p k ^ 3 * N p k ^ δ) := by ring
      _ ≤ 3041280 * ((N p k ^ δ) ^ 3 * N p k ^ δ) := by gcongr
      _ = 3041280 * N p k ^ (4 * δ) := by rw [← hpow]; ring
  -- the four losses
  have l1 : N p k ^ (-ε) ≤ N p k ^ (-δ) / 4 := rpow_neg_le_of_le hN (by norm_num) h1
  have l2 : N p k ^ (-(ε / 8)) ≤ N p k ^ (-δ) / 4 := rpow_neg_le_of_le hN (by norm_num) h2
  have l3 : ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ) *
      (1920 * 4 ^ rPar p k * (kmaxPar p k + rPar p k + 3) * N p k ^ (-(ε / 2))) ≤
      N p k ^ (-δ) / 4 := by
    have hneg := rpow_neg_le_of_le (a := ε / 2 - 4 * δ) hN (by norm_num : (0 : ℝ) < 4 * 3041280)
      (by rw [show ε / 2 - 4 * δ - δ = ε / 2 - 5 * δ by ring]; exact h3)
    have hsplit : N p k ^ (4 * δ) * N p k ^ (-(ε / 2)) = N p k ^ (-(ε / 2 - 4 * δ)) := by
      rw [← Real.rpow_add hN]; congr 1; ring
    calc ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ) *
          (1920 * 4 ^ rPar p k * (kmaxPar p k + rPar p k + 3) * N p k ^ (-(ε / 2)))
        = (((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ) *
            (1920 * 4 ^ rPar p k * (kmaxPar p k + rPar p k + 3))) * N p k ^ (-(ε / 2)) := by ring
      _ ≤ (3041280 * N p k ^ (4 * δ)) * N p k ^ (-(ε / 2)) := by
          gcongr
      _ = 3041280 * N p k ^ (-(ε / 2 - 4 * δ)) := by rw [mul_assoc, hsplit]
      _ ≤ 3041280 * (N p k ^ (-δ) / (4 * 3041280)) := by gcongr
      _ = N p k ^ (-δ) / 4 := by ring
  have l4 : 2 * N p k ^ (-c) ≤ N p k ^ (-δ) / 4 := by
    have := rpow_neg_le_of_le hN (by norm_num : (0 : ℝ) < 8) h4
    linarith
  linarith

/-- The prior-density compatibility of the finest cell level holds eventually. -/
theorem eventually_hRd {p : Data} (hp : Exact p) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ k in atTop, (N p k ^ (2 * (M p : ℝ)) * 8 * N p k ^ (-L p) * (2 * K p k) ^ 2) *
        (qPar p k / 2 ^ kmaxPar p k) ≤
      30 * 2 ^ rPar p k * floorPar p k ε / N p k ^ (-(ε / 8)) := by
  filter_upwards [hp.slack_subpower (1 / 2) (by norm_num)] with k hK
  have hN := hp.N_pos k
  have hN1 := hp.N_one_le k
  have hN2 : 2 ≤ N p k := hp.resolution_ge k
  have hq := qPar_pos hp k
  have hK1 : 1 ≤ K p k := hp.slack_ge k
  set Φ := profile p (L p) with hΦ
  set κ := kappaPar p with hκ
  have hκdef : κ = 2 * (M p : ℝ) + |Φ| + 4 := rfl
  -- left side
  have hKsq : K p k ^ 2 ≤ N p k := by
    have : (N p k ^ (1 / 2 : ℝ)) ^ 2 = N p k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
      norm_num
    calc K p k ^ 2 ≤ (N p k ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = N p k := this
  have hNL : N p k ^ (-L p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith [hp.length_pos])
  have hkmax := two_pow_kmax_ge hp k
  have hLHS : (N p k ^ (2 * (M p : ℝ)) * 8 * N p k ^ (-L p) * (2 * K p k) ^ 2) *
      (qPar p k / 2 ^ kmaxPar p k) ≤ 32 * qPar p k * N p k ^ (-|Φ| - 3) := by
    have hexp : N p k ^ (2 * (M p : ℝ)) * N p k / N p k ^ κ = N p k ^ (-|Φ| - 3) := by
      rw [← Real.rpow_add_one hN.ne', ← Real.rpow_sub hN]
      congr 1; rw [hκdef]; ring
    have hk0 : 0 < (2 : ℝ) ^ kmaxPar p k := by positivity
    have hκ0 : 0 < N p k ^ κ := Real.rpow_pos_of_pos hN _
    calc (N p k ^ (2 * (M p : ℝ)) * 8 * N p k ^ (-L p) * (2 * K p k) ^ 2) *
          (qPar p k / 2 ^ kmaxPar p k)
        = 32 * qPar p k * (N p k ^ (2 * (M p : ℝ)) * N p k ^ (-L p) * K p k ^ 2) /
            2 ^ kmaxPar p k := by ring
      _ ≤ 32 * qPar p k * (N p k ^ (2 * (M p : ℝ)) * 1 * N p k) / N p k ^ κ := by
          apply div_le_div₀ (by positivity) _ hκ0 hkmax
          gcongr
      _ = 32 * qPar p k * (N p k ^ (2 * (M p : ℝ)) * N p k / N p k ^ κ) := by ring
      _ = 32 * qPar p k * N p k ^ (-|Φ| - 3) := by rw [hexp]
  -- right side
  have hRHS : 30 * qPar p k * N p k ^ (-|Φ| - 1) ≤
      30 * 2 ^ rPar p k * floorPar p k ε / N p k ^ (-(ε / 8)) := by
    have hr1 : (1 : ℝ) ≤ 2 ^ rPar p k := one_le_pow₀ (by norm_num)
    have hP : N p k ^ (-|Φ|) ≤ N p k ^ (-Φ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_abs_self Φ])
    have hE : N p k ^ (-1 : ℝ) ≤ N p k ^ (-ε) / N p k ^ (-(ε / 8)) := by
      rw [← Real.rpow_sub hN]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hsplit : N p k ^ (-|Φ| - 1) = N p k ^ (-|Φ|) * N p k ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hN]; ring_nf
    rw [hsplit]
    unfold floorPar
    rw [← hΦ]
    have hE8 : 0 < N p k ^ (-(ε / 8)) := Real.rpow_pos_of_pos hN _
    calc 30 * qPar p k * (N p k ^ (-|Φ|) * N p k ^ (-1 : ℝ))
        ≤ 30 * 1 * (N p k ^ (-Φ) * qPar p k * (N p k ^ (-ε) / N p k ^ (-(ε / 8)))) := by
          have h0 : 0 ≤ N p k ^ (-|Φ|) := Real.rpow_nonneg hN.le _
          have h1 : 0 ≤ N p k ^ (-1 : ℝ) := Real.rpow_nonneg hN.le _
          nlinarith [mul_le_mul hP hE h1 (Real.rpow_nonneg hN.le _)]
      _ ≤ 30 * 2 ^ rPar p k * (N p k ^ (-Φ) * qPar p k * (N p k ^ (-ε) / N p k ^ (-(ε / 8)))) := by
          gcongr
      _ = 30 * 2 ^ rPar p k * (N p k ^ (-Φ) * qPar p k * N p k ^ (-ε)) / N p k ^ (-(ε / 8)) := by
          ring
  -- compare
  have hcmp : 32 * qPar p k * N p k ^ (-|Φ| - 3) ≤ 30 * qPar p k * N p k ^ (-|Φ| - 1) := by
    have hsplit : N p k ^ (-|Φ| - 1) = N p k ^ (-|Φ| - 3) * N p k ^ (2 : ℝ) := by
      rw [← Real.rpow_add hN]; ring_nf
    rw [hsplit]
    have h2 : (4 : ℝ) ≤ N p k ^ (2 : ℝ) := by
      rw [Real.rpow_two]; nlinarith
    have h0 : 0 ≤ qPar p k * N p k ^ (-|Φ| - 3) := by positivity
    have h5 := mul_le_mul_of_nonneg_left h2 h0
    nlinarith
  linarith

/-- **The selected original mass of the covered incidences.** -/
theorem eventually_initial_mass {p : Data} (hp : Exact p) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ k in atTop, ENNReal.ofReal (N p k ^ (-ε)) ≤ ∑ a, ENNReal.ofReal (weight p k a) *
      mu p k a (covInc (mu p k a) (N p k ^ (M p : ℝ)) (K p k) (N p k ^ (-L p)) (qPar p k)
        (floorPar p k ε) (Tpar p k) (kmaxPar p k)) := by
  obtain ⟨c, hc, hexc⟩ := hp.2.2.2.2.2.1 (L p) (ε / 4) hp.length_pos.le le_rfl (by positivity)
  filter_upwards [hexc, eventually_initial_budget hp hε hc, eventually_hRd hp hε hε1]
    with k hk1 hk2 hk3
  have hN := hp.N_pos k
  set Φ := profile p (L p) with hΦ
  set cov : Fin (worlds p k) → ℝ≥0∞ := fun a =>
    mu p k a (covInc (mu p k a) (N p k ^ (M p : ℝ)) (K p k) (N p k ^ (-L p)) (qPar p k)
      (floorPar p k ε) (Tpar p k) (kmaxPar p k)) with hcov
  set exc : Fin (worlds p k) → ℝ≥0∞ := fun a =>
    mu p k a {z | density p k a (L p) (obsL (N p k ^ (-L p)) z) <
      ENNReal.ofReal (2 * (N p k ^ (-Φ - ε / 4) / 2))} with hexcdef
  set G : ℝ := groupCoef (qPar p k) (floorPar p k ε) (N p k ^ (-(ε / 8)))
    (N p k ^ (-Φ - ε / 4) / 2) (kmaxPar p k) (rPar p k) with hG
  set cnt : ℝ := ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ) with hcnt
  -- the closed form of the group constant
  have hGeq : G = 1920 * 4 ^ rPar p k * (kmaxPar p k + rPar p k + 3) * N p k ^ (-(ε / 2)) := by
    rw [hG]
    have hc0 : N p k ^ (-Φ - ε / 4) = N p k ^ (-Φ) * N p k ^ (-(ε / 4)) := by
      rw [← Real.rpow_add hN]; ring_nf
    rw [hc0]
    unfold floorPar
    exact groupCoef_initial hN (qPar_pos hp k) (Real.rpow_pos_of_pos hN _) _ _
  -- the world bounds
  have hworld : ∀ a, mu p k a univ ≤ cov a + (ENNReal.ofReal (N p k ^ (-(ε / 8))) +
      ENNReal.ofReal cnt * ENNReal.ofReal G) + 2 * exc a := by
    intro a
    have h := world_bound_at hp k a hε hk3
    have hcast : ((2 * (⌈3 * K p k⌉ + 1) + 1).toNat : ℝ≥0∞) = ENNReal.ofReal cnt := by
      rw [hcnt, ENNReal.ofReal_natCast]
    rw [hcast] at h
    calc mu p k a univ ≤ _ := h
      _ = cov a + (ENNReal.ofReal (N p k ^ (-(ε / 8))) + ENNReal.ofReal cnt * ENNReal.ofReal G) +
          2 * exc a := by ring
  -- the exceptional sets are inside the typical-density exception
  have hexcle : ∑ a, ENNReal.ofReal (weight p k a) * exc a ≤ ENNReal.ofReal (N p k ^ (-c)) := by
    refine le_trans ?_ hk1
    apply Finset.sum_le_sum
    intro a _
    refine mul_le_mul' le_rfl (measure_mono ?_)
    intro z hz
    left
    have h2 : 2 * (N p k ^ (-Φ - ε / 4) / 2) = N p k ^ (-profile p (L p) - ε / 4) := by
      rw [hΦ]; ring
    simp only [mem_ofPred_eq] at hz ⊢
    rw [h2] at hz
    exact hz
  -- weighted sums
  have hw1 : ∑ a, ENNReal.ofReal (weight p k a) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp.weight_nonneg k a), hp.weight_sum k,
      ENNReal.ofReal_one]
  set X : ℝ≥0∞ := ENNReal.ofReal (N p k ^ (-(ε / 8))) + ENNReal.ofReal cnt * ENNReal.ofReal G
    with hX
  have htotal : ENNReal.ofReal (K p k)⁻¹ ≤
      ∑ a, ENNReal.ofReal (weight p k a) * cov a + X + 2 * ENNReal.ofReal (N p k ^ (-c)) := by
    calc ENNReal.ofReal (K p k)⁻¹ ≤ ∑ a, ENNReal.ofReal (weight p k a) * mu p k a univ :=
          hp.mass_lower k
      _ ≤ ∑ a, ENNReal.ofReal (weight p k a) * (cov a + X + 2 * exc a) := by
          gcongr with a ha; exact hworld a
      _ = ∑ a, ENNReal.ofReal (weight p k a) * cov a +
            (∑ a, ENNReal.ofReal (weight p k a)) * X +
            2 * ∑ a, ENNReal.ofReal (weight p k a) * exc a := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro a _; ring
      _ ≤ ∑ a, ENNReal.ofReal (weight p k a) * cov a + X + 2 * ENNReal.ofReal (N p k ^ (-c)) := by
          rw [hw1, one_mul]; gcongr
  -- the real budget
  have hbudget : ENNReal.ofReal (N p k ^ (-ε)) + (X + 2 * ENNReal.ofReal (N p k ^ (-c))) ≤
      ENNReal.ofReal (K p k)⁻¹ := by
    have hcnt0 : 0 ≤ cnt := by rw [hcnt]; positivity
    have hG0 : 0 ≤ G := by rw [hGeq]; positivity
    rw [hX, ← ENNReal.ofReal_mul hcnt0, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (Real.rpow_nonneg hN.le _) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (Real.rpow_nonneg hN.le _) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hGeq]
    linarith [hk2]
  have hfin : X + 2 * ENNReal.ofReal (N p k ^ (-c)) ≠ ⊤ := by
    rw [hX]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩,
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
  have hcomb : ENNReal.ofReal (N p k ^ (-ε)) + (X + 2 * ENNReal.ofReal (N p k ^ (-c))) ≤
      (∑ a, ENNReal.ofReal (weight p k a) * cov a) + (X + 2 * ENNReal.ofReal (N p k ^ (-c))) :=
    calc _ ≤ ENNReal.ofReal (K p k)⁻¹ := hbudget
      _ ≤ ∑ a, ENNReal.ofReal (weight p k a) * cov a + X + 2 * ENNReal.ofReal (N p k ^ (-c)) :=
          htotal
      _ = _ := add_assoc _ _ _
  exact (ENNReal.add_le_add_iff_right hfin).mp hcomb

end Submission.Obl.k4_scalar_initial_true_horizon
