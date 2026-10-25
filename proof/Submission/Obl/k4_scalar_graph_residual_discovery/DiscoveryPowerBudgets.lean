/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 09bc463f, file DiscoveryPowerBudgets.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryPowerBounds
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryGrowth

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

theorem discovery_list_formula_nonneg {N H Hg η : ℝ} (hN : 0 < N)
    (hH : 0 ≤ H) (hHg : 0 ≤ Hg) (hη : 0 ≤ η) (J : ℕ) :
    0 ≤ discoveryListFormula N H Hg η J := by
  unfold discoveryListFormula
  positivity

/-- The literal raw-list formula has the uniform polynomial envelope
used for the finite original-state selection cost. -/
theorem discovery_actual_list_formula_le {N H Hg Hbig η : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHg : 1 ≤ Hg) (hHbig : 1 ≤ Hbig)
    (hHHbig : H ≤ Hbig) (hHgHbig : Hg ≤ Hbig) (hη : 0 < η) (hη₁ : η ≤ 1) (J : ℕ) :
    discoveryListFormula N H Hg η J ≤
      30000000 * Hbig ^ 10 * (η⁻¹) ^ 3 * (N ^ (1 / (J : ℝ))) ^ 2 := by
  have hN₀ : 0 < N := by linarith
  have hH₀ : 0 ≤ H := by linarith
  have hHg₀ : 0 ≤ Hg := by linarith
  have hηinv : 1 ≤ η⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hη).mpr (by simpa only [one_mul] using hη₁)
  have hQ : 1 ≤ N ^ (1 / (J : ℝ)) := Real.one_le_rpow hN (by positivity)
  have hKrow₀ : 0 ≤ discoveryRowConstant N Hg J := by unfold discoveryRowConstant; positivity
  have hrow := discovery_first_row_constant_le hHbig hHg₀ hHgHbig hQ
  have htime := discovery_time_row_constants_le hHbig (show 1 ≤ H + 1 by linarith)
    (show H + 1 ≤ 2 * Hbig by linarith) hKrow₀ hQ hrow
  have hLrow : 0 ≤ 12 * discoveryTimeConstant N H Hg J ^ 2 := by positivity
  have hgeom := discovery_raw_list_bound_le hHbig hHg₀ hHgHbig hHg₀ hHgHbig hLrow hQ hηinv htime.2
  apply le_trans ?_ hgeom
  simp only [discoveryListFormula, div_eq_mul_inv]
  gcongr

namespace DiscoveryPowerSchedule

noncomputable section

def majorant (K H Hg : ℝ) : ℝ := K * H * Hg
def eta (N ω : ℝ) : ℝ := N ^ (-ω)
def mass (N ω : ℝ) : ℝ := N ^ (-(ω / 4))
def base (N Hbig ω : ℝ) : ℝ := 3 * Hbig * N ^ (2 * ω)
def fill (N Hbig Cmk ω τ : ℝ) : ℝ := 64800 * Cmk * Hbig ^ 6 * N ^ (8 * ω + τ)
def geom (N Hbig Cmk ω τ : ℝ) : ℝ :=
  2000000 * (max 1 Cmk + 1) * Hbig ^ 8 * N ^ (8 * ω + τ)
def selection (N α : ℝ) : ℝ := N ^ (α / 10)

theorem majorant_one_le {K H Hg : ℝ} (hK : 1 ≤ K) (hH : 1 ≤ H) (hHg : 1 ≤ Hg) :
    1 ≤ majorant K H Hg ∧ K ≤ majorant K H Hg ∧
      H ≤ majorant K H Hg ∧ Hg ≤ majorant K H Hg := by
  have hKH : 1 ≤ K * H := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hH)]
  have hKHK : K ≤ K * H := by nlinarith [mul_nonneg (by linarith : 0 ≤ K) (sub_nonneg.mpr hH)]
  have hKHH : H ≤ K * H := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (by linarith : 0 ≤ H)]
  have hprod : K * H ≤ K * H * Hg := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ K * H) (sub_nonneg.mpr hHg)]
  have hHgprod : Hg ≤ K * H * Hg := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hKH) (by linarith : 0 ≤ Hg)]
  exact ⟨hKH.trans hprod, hKHK.trans hprod, hKHH.trans hprod, hHgprod⟩

theorem majorant_subpower {N K H Hg : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hK : Subpower N K) (hH : Subpower N H) (hHg : Subpower N Hg) :
    Subpower N (fun k => majorant (K k) (H k) (Hg k)) :=
  DiscoveryGrowth.subpower_mul hN (DiscoveryGrowth.subpower_mul hN hK hH) hHg

theorem eta_inv {N ω : ℝ} (hN : 0 ≤ N) : (eta N ω)⁻¹ = N ^ ω := by
  rw [eta, Real.rpow_neg hN, inv_inv]

theorem eta_le_one {N ω : ℝ} (hN : 1 ≤ N) (hω : 0 ≤ ω) : eta N ω ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hω)

theorem rpow_nat_power {N : ℝ} (hN : 0 < N) (a : ℝ) (n : ℕ) :
    (N ^ a) ^ n = N ^ (a * (n : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]

theorem base_budgets {N H Hbig ω : ℝ} (hN : 1 ≤ N) (hH : 1 ≤ H)
    (hHbig : 1 ≤ Hbig) (hHHbig : H ≤ Hbig) (hω : 0 ≤ ω) :
    0 < base N Hbig ω ∧ 3 * H ≤ base N Hbig ω ∧ H / (eta N ω * eta N ω) ≤ base N Hbig ω := by
  have hN₀ : 0 < N := by linarith
  have hHb₀ : 0 < Hbig := by linarith
  have hpow : 1 ≤ N ^ (2 * ω) := Real.one_le_rpow hN (by positivity)
  have hbase₀ : 0 < base N Hbig ω := by unfold base; positivity
  refine ⟨hbase₀, ?_, ?_⟩
  · unfold base
    have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 3 * Hbig)
    nlinarith only [hh, hHHbig]
  · have heq : H / (eta N ω * eta N ω) = H * N ^ (2 * ω) := by
      rw [div_eq_mul_inv, mul_inv, eta_inv hN₀.le, ← Real.rpow_add hN₀]
      congr 1
      ring
    rw [heq]
    unfold base
    gcongr
    linarith

theorem fill_geom_representation {N Hbig Cmk ω τ : ℝ} (hN : 0 < N) :
    fill N Hbig Cmk ω τ = 64800 * Cmk * Hbig ^ 6 * (N ^ ω) ^ 8 * N ^ τ ∧
      geom N Hbig Cmk ω τ = 2000000 * (max 1 Cmk + 1) * Hbig ^ 8 * (N ^ ω) ^ 8 * N ^ τ := by
  have hp : N ^ (8 * ω + τ) = (N ^ ω) ^ 8 * N ^ τ := by
    rw [rpow_nat_power hN, ← Real.rpow_add hN]
    congr 1
    norm_num
    ring
  constructor <;> simp only [fill, geom, hp] <;> ring

theorem geometry_budgets {N H Hg Hbig Cmk ω τ : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHg : 1 ≤ Hg) (hHbig : 1 ≤ Hbig)
    (hHHbig : H ≤ Hbig) (hHgHbig : Hg ≤ Hbig) (hCmk : 0 < Cmk)
    (hω : 0 ≤ ω) (hτ : 0 ≤ τ) :
    0 < fill N Hbig Cmk ω τ ∧ 0 < geom N Hbig Cmk ω τ ∧
      200 * Cmk * (base N Hbig ω) ^ 4 * (1 + H) ^ 2 ≤ fill N Hbig Cmk ω τ * N ^ (-τ) ∧
      fill N Hbig Cmk ω τ ≤ geom N Hbig Cmk ω τ ∧
      18 * ((5 + 2 * Hg) + 1) * (13824 * H ^ 7) ≤ geom N Hbig Cmk ω τ ∧
      2 * (5 + 2 * Hg) + 2 ≤ geom N Hbig Cmk ω τ := by
  have hN₀ : 0 < N := by linarith
  have hH₀ : 0 ≤ H := by linarith
  have hHb₀ : 0 < Hbig := by linarith
  have hX : 1 ≤ N ^ ω := Real.one_le_rpow hN hω
  have hV : 1 ≤ N ^ τ := Real.one_le_rpow hN hτ
  have hbase : base N Hbig ω = 3 * Hbig * (N ^ ω) ^ 2 := by
    unfold base
    rw [rpow_nat_power hN₀]
    congr 1
    norm_num
    ring
  have hproduct : fill N Hbig Cmk ω τ * N ^ (-τ) = 64800 * Cmk * Hbig ^ 6 * (N ^ ω) ^ 8 := by
    rw [(fill_geom_representation hN₀).1, mul_assoc, ← Real.rpow_add hN₀]
    simp only [add_neg_cancel, Real.rpow_zero, mul_one]
  have hgeom := discovery_hereditary_budget (C := Cmk) hHbig (show 5 + 2 * Hg ≤ 7 * Hbig by linarith) hX hV
  refine ⟨by unfold fill; positivity, by unfold geom; positivity, ?_, ?_, ?_, ?_⟩
  · rw [hbase, hproduct]
    apply le_trans ?_ (discovery_planar_filling_budget hHbig hCmk.le)
    gcongr
  · rw [(fill_geom_representation hN₀).1, (fill_geom_representation hN₀).2]
    exact discovery_filling_constant_le hHbig hCmk.le (Real.rpow_nonneg hN₀.le _)
  · rw [(fill_geom_representation hN₀).2]
    apply le_trans ?_ hgeom.1
    gcongr
  · simpa only [(fill_geom_representation hN₀).2] using hgeom.2

theorem time_constant_monomial {N H Hg Hbig : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHg : 1 ≤ Hg) (hHbig : 1 ≤ Hbig)
    (hHHbig : H ≤ Hbig) (hHgHbig : Hg ≤ Hbig) (J : ℕ) :
    12 * discoveryTimeConstant N H Hg J ^ 2 ≤ 196608 * Hbig ^ 4 * N ^ (2 / (J : ℝ)) := by
  have hN₀ : 0 < N := by linarith
  have hQ : 1 ≤ N ^ (1 / (J : ℝ)) := Real.one_le_rpow hN (by positivity)
  have hrow := discovery_first_row_constant_le hHbig (show 0 ≤ Hg by linarith) hHgHbig hQ
  have hKrow : 0 ≤ discoveryRowConstant N Hg J := by unfold discoveryRowConstant; positivity
  have hh := (discovery_time_row_constants_le hHbig (show 1 ≤ H + 1 by linarith)
    (show H + 1 ≤ 2 * Hbig by linarith) hKrow hQ hrow).2
  have hpow : (N ^ (1 / (J : ℝ))) ^ 2 = N ^ (2 / (J : ℝ)) := by
    rw [rpow_nat_power hN₀]
    congr 1
    norm_num
    ring
  simpa only [hpow, discoveryTimeConstant] using hh

theorem residual_constant_monomial {N Hg Hbig : ℝ}
    (hN : 1 ≤ N) (hHbig : 1 ≤ Hbig) (hHgHbig : Hg ≤ Hbig) (J : ℕ) :
    6 * (N ^ (1 / (J : ℝ)) + Hg + 5) ≤ 42 * Hbig * N ^ (1 / (J : ℝ)) := by
  have hQ : 1 ≤ N ^ (1 / (J : ℝ)) := Real.one_le_rpow hN (by positivity)
  have h₁ := mul_le_mul_of_nonneg_right hHbig (show 0 ≤ N ^ (1 / (J : ℝ)) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hQ (show 0 ≤ Hbig by linarith)
  simp only [one_mul, mul_one] at h₁ h₂
  nlinarith only [h₁, h₂, hHgHbig, hHbig]

theorem list_formula_monomial {N H Hg Hbig ω : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHg : 1 ≤ Hg) (hHbig : 1 ≤ Hbig)
    (hHHbig : H ≤ Hbig) (hHgHbig : Hg ≤ Hbig) (hω : 0 ≤ ω) (J : ℕ) :
    discoveryListFormula N H Hg (eta N ω) J ≤
      30000000 * Hbig ^ 10 * N ^ (3 * ω + 2 / (J : ℝ)) := by
  have hN₀ : 0 < N := by linarith
  have hh := discovery_actual_list_formula_le hN hH hHg hHbig hHHbig hHgHbig
    (Real.rpow_pos_of_pos hN₀ _) (eta_le_one hN hω) J
  rw [← Real.rpow_neg hN₀.le, neg_neg] at hh
  have hpow : (N ^ ω) ^ 3 * (N ^ (1 / (J : ℝ))) ^ 2 = N ^ (3 * ω + 2 / (J : ℝ)) := by
    simp only [rpow_nat_power hN₀]
    rw [← Real.rpow_add hN₀]
    congr 1
    norm_num
    ring
  exact hh.trans_eq (by rw [mul_assoc, hpow])

theorem cap_constant_monomial {N H Hbig ω : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHbig : 1 ≤ Hbig) (hHHbig : H ≤ Hbig) (J : ℕ) :
    9 * H ^ 2 * (H * N ^ (1 / (J : ℝ))) ^ 4 / eta N ω ≤
      9 * Hbig ^ 6 * N ^ (ω + 4 / (J : ℝ)) := by
  have hN₀ : 0 < N := by linarith
  have hpow : (N ^ (1 / (J : ℝ))) ^ 4 * N ^ ω = N ^ (ω + 4 / (J : ℝ)) := by
    rw [rpow_nat_power hN₀, ← Real.rpow_add hN₀]
    congr 1
    norm_num
    ring
  calc
    _ = 9 * H ^ 6 * ((N ^ (1 / (J : ℝ))) ^ 4 * N ^ ω) := by
      rw [div_eq_mul_inv, eta_inv hN₀.le, mul_pow]
      ring
    _ ≤ 9 * Hbig ^ 6 * ((N ^ (1 / (J : ℝ))) ^ 4 * N ^ ω) := by gcongr
    _ = _ := by rw [hpow]

theorem support_constant_monomial {N Hrow Hbig Cmk ω τ d : ℝ}
    (hN : 1 ≤ N) (hHrow : 0 ≤ Hrow) (hHbig : 1 ≤ Hbig) (hHrowHbig : Hrow ≤ Hbig)
    (hω : 0 ≤ ω) (hτ : 0 ≤ τ) (hd : d ≤ 1) (J : ℕ) :
    ((4 * (3 + 2 * Hrow) + 3) * (10648 * (geom N Hbig Cmk ω τ) ^ 3)) *
        ((N ^ (1 / (J : ℝ))) ^ 2) ^ d ≤
      3000000000000000000000000 * (max 1 Cmk + 1) ^ 3 * Hbig ^ 25 *
        N ^ (24 * ω + 3 * τ + 2 / (J : ℝ)) := by
  have hN₀ : 0 < N := by linarith
  have hh := discovery_scalar_support_bound_le (C := Cmk) hHbig hHrow hHrowHbig
    (Real.one_le_rpow hN hω) (Real.one_le_rpow hN hτ)
    (Real.one_le_rpow hN (by positivity : 0 ≤ 1 / (J : ℝ))) hd
  rw [← (fill_geom_representation hN₀).2] at hh
  have hpow : (N ^ ω) ^ 24 * (N ^ τ) ^ 3 * (N ^ (1 / (J : ℝ))) ^ 2 =
      N ^ (24 * ω + 3 * τ + 2 / (J : ℝ)) := by
    simp only [rpow_nat_power hN₀]
    rw [← Real.rpow_add hN₀, ← Real.rpow_add hN₀]
    congr 1
    norm_num
    ring
  exact hh.trans_eq (by
    convert congrArg (fun x : ℝ =>
      3000000000000000000000000 * (max 1 Cmk + 1) ^ 3 * Hbig ^ 25 * x) hpow using 1 <;> ring)

def firstReal (Hg : ℝ) (C J : ℕ) : ℝ :=
  ((4 : ℝ) ^ 3 * (8 * (⌈(2 * Hg + 2) ^ 2⌉₊ : ℝ))) ^ (C * J + 1)

theorem firstFactor_eq_ofReal (Hg : ℝ) (C J : ℕ) :
    discoveryFirstFactor Hg C J = ENNReal.ofReal (firstReal Hg C J) := by
  simp (disch := positivity) only [discoveryFirstFactor, firstReal, ENNReal.ofReal_pow,
    ENNReal.ofReal_mul, ENNReal.ofReal_natCast]
  norm_num

theorem eventually_source_budget {N Hg : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hHg : Subpower N Hg)
    (C J : ℕ) {ω δ : ℝ} (hω : 0 < ω) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ENNReal.ofReal (2 * mass (N k) ω) * discoveryFirstFactor (Hg k) C J ≤
      ENNReal.ofReal (δ / (2 * Hg k)) := by
  have hF : Subpower N (fun k => firstReal (Hg k) C J) :=
    DiscoveryGrowth.subpower_first_row_factor hN hNt hHg (C * J + 1)
  have hprod := DiscoveryGrowth.subpower_mul hN hHg hF
  have hgrow := DiscoveryGrowth.eventually_monomial_lt hN hNt hprod 1
    (a := -(ω / 4)) (b := 0) (by linarith) (A := 4 / δ) (by positivity)
  filter_upwards [hgrow] with k hk
  have hN₀ : 0 < N k := by linarith [hN k]
  have hHg₀ : 0 < Hg k := by linarith [hHg.1 k]
  simp only [pow_one, Real.rpow_zero] at hk
  have hscaled : 4 * Hg k * firstReal (Hg k) C J * mass (N k) ω < δ := by
    have hh : (4 * Hg k * firstReal (Hg k) C J * mass (N k) ω) / δ < 1 := by
      convert hk using 1 <;> dsimp only [mass] <;> ring
    simpa only [one_mul] using (div_lt_iff₀ hδ).mp hh
  have hreal : 2 * mass (N k) ω * firstReal (Hg k) C J ≤ δ / (2 * Hg k) :=
    (le_div_iff₀ (by positivity : 0 < 2 * Hg k)).mpr (by nlinarith only [hscaled])
  rw [firstFactor_eq_ofReal, ← ENNReal.ofReal_mul (by unfold mass; positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem eventually_cut_budget {N Hbig : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hHbig : Subpower N Hbig)
    (C J : ℕ) {ω : ℝ} (hω : 0 < ω) :
    ∀ᶠ k in atTop, 10000000000 * ((C : ℝ) * J + 1) * Hbig k ^ 2 * eta (N k) ω ≤ mass (N k) ω := by
  have hh := DiscoveryGrowth.eventually_monomial_lt hN hNt hHbig 2
    (a := -ω) (b := -(ω / 4)) (by linarith)
    (A := 10000000000 * ((C : ℝ) * J + 1)) (by positivity)
  exact hh.mono (fun _ hk => hk.le)

theorem eventually_angular_budget {N K Hg Hbig : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (hHg : Subpower N Hg) (hHbig : Subpower N Hbig)
    (hKHbig : ∀ k, K k ≤ Hbig k) (hHgHbig : ∀ k, Hg k ≤ Hbig k)
    {ω τ S : ℝ} (hω : 0 < ω) (hrel : S * τ = 4 * ω) :
    ∀ᶠ k in atTop, 5 * (ENNReal.ofReal (Hg k) / ENNReal.ofReal (eta (N k) ω)) *
      ENNReal.ofReal (K k * N k ^ (-S * τ)) ≤ 1 / 2 := by
  have hh := DiscoveryGrowth.eventually_monomial_lt hN hNt hHbig 2
    (a := -3 * ω) (b := 0) (by linarith) (A := 10) (by norm_num)
  filter_upwards [hh] with k hk
  have hN₀ : 0 < N k := by linarith [hN k]
  have hK₀ : 0 ≤ K k := by linarith [hK.1 k]
  have hHg₀ : 0 ≤ Hg k := by linarith [hHg.1 k]
  have hHb₀ : 0 ≤ Hbig k := by linarith [hHbig.1 k]
  have hη : 0 < eta (N k) ω := Real.rpow_pos_of_pos hN₀ _
  have hpow : N k ^ ω * N k ^ (-S * τ) = N k ^ (-3 * ω) := by
    rw [← Real.rpow_add hN₀]
    congr 1
    nlinarith only [hrel]
  have hreal : 5 * (Hg k / eta (N k) ω) * (K k * N k ^ (-S * τ)) ≤ (1 / 2 : ℝ) := by
    have hprod : Hg k * K k ≤ Hbig k ^ 2 := by
      simpa only [pow_two] using mul_le_mul (hHgHbig k) (hKHbig k) hK₀ hHb₀
    calc
      _ = 5 * (Hg k * K k) * (N k ^ ω * N k ^ (-S * τ)) := by
        rw [div_eq_mul_inv, eta_inv hN₀.le]
        ring
      _ ≤ 5 * Hbig k ^ 2 * N k ^ (-3 * ω) := by rw [hpow]; gcongr
      _ ≤ _ := by simp only [Real.rpow_zero] at hk; nlinarith only [hk]
  have heq : ENNReal.ofReal (5 * (Hg k / eta (N k) ω) * (K k * N k ^ (-S * τ))) =
      5 * (ENNReal.ofReal (Hg k) / ENNReal.ofReal (eta (N k) ω)) *
        ENNReal.ofReal (K k * N k ^ (-S * τ)) := by
    simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_div_of_pos hη]
    norm_num
  rw [← heq]
  exact (ENNReal.ofReal_le_ofReal hreal).trans_eq (by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num)

end

end DiscoveryPowerSchedule

end Submission.Obl.k4_scalar_graph_residual_discovery
