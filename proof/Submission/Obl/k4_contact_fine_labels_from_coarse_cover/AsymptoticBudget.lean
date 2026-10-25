import Submission.Obl.k4_discrete_of_terminal_charts.Horizon
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open Submission.Obl.k4_profile_density_bounds

noncomputable def fineLam (K H : ℝ) : ℝ := (17280 * K ^ 7 * H)⁻¹

noncomputable def fineLoss (C K H θ : ℝ) : ℝ :=
  C * (4 * 10 ^ 4 * K ^ 6 / (fineLam K H * θ ^ 3)) ^ 80

private theorem fineLoss_eq {N K H : ℝ} (hN : 0 < N) (_hK : 0 < K)
    (_hH : 0 < H) (C v : ℝ) :
    fineLoss C K H (N ^ (-v)) =
      (C * ((4 * 10 ^ 4 * 17280) * K ^ 13 * H) ^ 80) * N ^ (240 * v) := by
  have hpow : (N ^ (-v)) ^ (3 : ℕ) = N ^ (-(3 * v)) := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    ring
  have hinv : ((N ^ (-v)) ^ (3 : ℕ))⁻¹ = N ^ (3 * v) := by
    rw [hpow, Real.rpow_neg hN.le, inv_inv]
  have heq : 4 * 10 ^ 4 * K ^ 6 / (fineLam K H * (N ^ (-v)) ^ 3) =
      ((4 * 10 ^ 4 * 17280) * K ^ 13 * H) * N ^ (3 * v) := by
    rw [div_eq_mul_inv, mul_inv_rev, hinv, fineLam, inv_inv]
    ring
  rw [fineLoss, heq, mul_pow, ← mul_assoc, ← Real.rpow_mul_natCast hN.le]
  congr 2
  ring

private theorem fine_base_subpower (N K H : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k) (hH : ∀ k, 1 ≤ H k)
    (hKsub : SubpowerBound N K) (hHsub : SubpowerBound N H) (C : ℝ) (hC : 0 ≤ C) :
    SubpowerBound N (fun k => C * ((4 * 10 ^ 4 * 17280) * K k ^ 13 * H k) ^ 80) := by
  have hNpos : ∀ k, 0 < N k := fun k => zero_lt_one.trans_le (hN k)
  have hK0 : ∀ k, 0 ≤ K k := fun k => (zero_le_one.trans (hK k))
  have hH0 : ∀ k, 0 ≤ H k := fun k => (zero_le_one.trans (hH k))
  have hKpow := subpower_pow hN hK0 hKsub 13
  have hD := subpower_const hNt (4 * 10 ^ 4 * 17280 : ℝ)
  have hDK := subpower_mul hNpos (fun _ => by norm_num) (fun k => pow_nonneg (hK0 k) _)
    hD hKpow
  have hDKH := subpower_mul hNpos (fun k => mul_nonneg (by norm_num) (pow_nonneg (hK0 k) 13)) hH0 hDK hHsub
  have hb0 (k : ℕ) : 0 ≤ (4 * 10 ^ 4 * 17280 : ℝ) * K k ^ 13 * H k :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (hK0 k) 13)) (hH0 k)
  have hpow := subpower_pow hN hb0 hDKH 80
  exact subpower_mul hNpos (fun _ => hC) (fun k => pow_nonneg (hb0 k) _)
    (subpower_const hNt C) hpow

/-- The heavy-state filling fraction is positive and at most one. -/
theorem fineLam_bounds {K H : ℝ} (hK : 1 ≤ K) (hH : 1 ≤ H) :
    0 < fineLam K H ∧ fineLam K H ≤ 1 := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hpow : 1 ≤ K ^ 7 := one_le_pow₀ hK
  have hden : 1 ≤ 17280 * K ^ 7 * H := by nlinarith
  constructor
  · unfold fineLam; positivity
  · simpa only [fineLam, inv_one] using inv_anti₀ zero_lt_one hden

/-- The contact normalization has scale at least one. -/
theorem fine_normalization_ge_one {K θ : ℝ} (hK : 1 ≤ K) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) : 1 ≤ 200 * K ^ 3 / θ := by
  rw [le_div_iff₀ hθ]
  have hpow : 1 ≤ K ^ 3 := one_le_pow₀ hK
  linarith

/-- An arbitrarily small fixed velocity separation spends only a prescribed positive exponent. -/
theorem eventually_fine_loss (N K H : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k) (hH : ∀ k, 1 ≤ H k)
    (hKsub : SubpowerBound N K) (hHsub : SubpowerBound N H)
    {C v e : ℝ} (hC : 0 ≤ C) (hve : 240 * v < e) :
    ∀ᶠ k in atTop, fineLoss C (K k) (H k) (N k ^ (-v)) ≤ N k ^ e := by
  filter_upwards [fine_base_subpower N K H hN hNt hK hH hKsub hHsub C hC
    (e - 240 * v) (by linarith)] with k hk
  rw [fineLoss_eq (zero_lt_one.trans_le (hN k)) (zero_lt_one.trans_le (hK k))
    (zero_lt_one.trans_le (hH k))]
  calc
    _ ≤ N k ^ (e - 240 * v) * N k ^ (240 * v) :=
      mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (by linarith [hN k]) _)
    _ = _ := by rw [← Real.rpow_add (by linarith [hN k])]; congr 1; ring

/-- A deep true block and the occupied reciprocal mesh are both finer than the shallow witness scale. -/
theorem eventually_fine_proximity (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k)
    (hKsub : SubpowerBound N K) {s κ t : ℝ} (hs : 0 < s) (hdeep : 30 * s < κ * t) :
    ∀ᶠ k in atTop, ∀ q : ℝ, q ≤ K k * N k ^ (-κ * t) →
      N k ^ (-40 * s) + 6 * K k ^ 2 * q ≤ N k ^ (-30 * s) := by
  filter_upwards [eventually_const_mul_rpow_lt hNt (show -40 * s < -30 * s by linarith) 2,
    eventually_subpower_mul_rpow_lt hN hNt hK hKsub 3
      (show -κ * t < -30 * s by linarith) (show (0 : ℝ) ≤ 12 by norm_num)]
    with k hmesh hblock
  intro q hq
  have hK0 : 0 ≤ K k := by linarith [hK k]
  have h := mul_le_mul_of_nonneg_left hq (show 0 ≤ 6 * K k ^ 2 by positivity)
  nlinarith

/-- Contact error and mesh error satisfy the deterministic palette budget at every sufficiently large scale. -/
theorem eventually_fine_smallness (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k)
    (hKsub : SubpowerBound N K) {s κ e₀ : ℝ} (hs : 0 < s)
    (hκ : κ ≤ 1) (he₀ : 2 * s < e₀) :
    ∀ᶠ k in atTop, ∀ q μ E : ℝ, 0 < q →
      (K k)⁻¹ * N k ^ (-κ * s) ≤ q → 1 ≤ μ →
      0 ≤ E → E ≤ N k ^ s →
      N k ^ (-e₀) ≤ q ∧
      E * (N k ^ (-e₀) / (q * μ) + 7 * K k * N k ^ (-30 * s) / q ^ 2) ≤ 1 := by
  filter_upwards [eventually_subpower_mul_rpow_lt hN hNt hK hKsub 1
      (show 2 * s - e₀ < 0 by linarith) (show (0 : ℝ) ≤ 2 by norm_num),
    eventually_subpower_mul_rpow_lt hN hNt hK hKsub 3
      (show -27 * s < 0 by linarith) (show (0 : ℝ) ≤ 14 by norm_num)]
    with k hc hm
  simp only [Real.rpow_zero, pow_one] at hc hm
  intro q μ E hq hql hμ hE hEs
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  have hKp : 0 < K k := zero_lt_one.trans_le (hK k)
  have hμp : 0 < μ := zero_lt_one.trans_le hμ
  have hqinv : q⁻¹ ≤ K k * N k ^ s := by
    have hlo : 0 < (K k)⁻¹ * N k ^ (-κ * s) := by positivity
    calc
      q⁻¹ ≤ ((K k)⁻¹ * N k ^ (-κ * s))⁻¹ := inv_anti₀ hlo hql
      _ = K k * N k ^ (κ * s) := by
        rw [mul_inv_rev, inv_inv, show -κ * s = -(κ * s) by ring,
          Real.rpow_neg hNp.le, inv_inv]
        ring
      _ ≤ K k * N k ^ s := by
        apply mul_le_mul_of_nonneg_left _ hKp.le
        exact Real.rpow_le_rpow_of_exponent_le (hN k) (by nlinarith)
  have hqinv2 : q⁻¹ ^ 2 ≤ K k ^ 2 * N k ^ (2 * s) := by
    calc
      _ ≤ (K k * N k ^ s) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hqinv 2
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hNp.le]; congr 2; ring
  have hcontact : E * (N k ^ (-e₀) / (q * μ)) ≤ K k * N k ^ (2 * s - e₀) := by
    calc
      _ ≤ N k ^ s * (N k ^ (-e₀) * q⁻¹) := by
        apply mul_le_mul hEs _ (by positivity) (by positivity)
        rw [div_eq_mul_inv, mul_inv_rev]
        have : μ⁻¹ ≤ (1 : ℝ) := by simpa using inv_anti₀ zero_lt_one hμ
        nlinarith [mul_nonneg (Real.rpow_nonneg hNp.le (-e₀)) (inv_nonneg.mpr hq.le)]
      _ ≤ N k ^ s * (N k ^ (-e₀) * (K k * N k ^ s)) := by gcongr
      _ = _ := by
        rw [show N k ^ s * (N k ^ (-e₀) * (K k * N k ^ s)) =
          K k * (N k ^ s * N k ^ (-e₀) * N k ^ s) by ring,
          ← Real.rpow_add hNp, ← Real.rpow_add hNp]
        congr 2
        ring
  have hmeshs : E * (7 * K k * N k ^ (-30 * s) / q ^ 2) ≤
      7 * K k ^ 3 * N k ^ (-27 * s) := by
    calc
      _ ≤ N k ^ s * ((7 * K k * N k ^ (-30 * s)) *
          (K k ^ 2 * N k ^ (2 * s))) := by
        rw [div_eq_mul_inv, ← inv_pow]
        gcongr
      _ = _ := by
        rw [show N k ^ s * (7 * K k * N k ^ (-30 * s) * (K k ^ 2 * N k ^ (2 * s))) =
          7 * K k ^ 3 * (N k ^ s * N k ^ (-30 * s) * N k ^ (2 * s)) by ring,
          ← Real.rpow_add hNp, ← Real.rpow_add hNp]
        congr 2
        ring
  constructor
  · have hpow : 1 ≤ N k ^ s := Real.one_le_rpow (hN k) hs.le
    have hc' : N k ^ s * (N k ^ (-e₀) * q⁻¹) ≤ K k * N k ^ (2 * s - e₀) := by
      calc
        _ ≤ N k ^ s * (N k ^ (-e₀) * (K k * N k ^ s)) := by gcongr
        _ = _ := by
          rw [show N k ^ s * (N k ^ (-e₀) * (K k * N k ^ s)) =
            K k * (N k ^ s * N k ^ (-e₀) * N k ^ s) by ring,
            ← Real.rpow_add hNp, ← Real.rpow_add hNp]
          congr 2
          ring
    have : N k ^ (-e₀) * q⁻¹ ≤ 1 := by nlinarith [(show 0 ≤ N k ^ (-e₀) * q⁻¹ by positivity)]
    exact (div_le_one hq).mp (by simpa only [div_eq_mul_inv] using this)
  · rw [mul_add]
    linarith

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
