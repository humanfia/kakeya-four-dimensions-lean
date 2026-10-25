import Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing.Basics
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! The numerical choices of one depth. With `a = N^-s`, the fit accuracy is
`δ = 4 N^ε₁ a`, the static mesh is the velocity width `N^-M`, the physical mesh
is `N^-(M+1)`, the norm bound is `200 K^4 N^ε₁`, the pruning constant is
`N^(5 ε₁)` and the comparison scale is `N^ε a / 10`. Every requirement of the
depth step holds at all sufficiently late samples. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_subcritical_endpoint_native_pairing.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The fit accuracy. -/
def numδ (cfg : Data α) (k : ℕ) (s ε₁ : ℝ) : ℝ := 4 * cfg.N k ^ ε₁ * cfg.N k ^ (-s)
/-- The norm bound. -/
def numE (cfg : Data α) (k : ℕ) (ε₁ : ℝ) : ℝ := 200 * cfg.K k ^ 4 * cfg.N k ^ ε₁
/-- The pruning constant. -/
def numA₀ (cfg : Data α) (k : ℕ) (ε₁ : ℝ) : ℝ := cfg.N k ^ (5 * ε₁)
/-- The comparison scale. -/
def numMst (cfg : Data α) (k : ℕ) (s ε : ℝ) : ℝ := cfg.N k ^ ε * cfg.N k ^ (-s) / 10

/-- All numerical requirements of one depth at one sample. -/
structure DepthNumerics (cfg : Data α) (k : ℕ) (s M ε ε₁ η R₀ : ℝ) : Prop where
  fit_le_one : numδ cfg k s ε₁ ≤ 1
  phys_le_fit : 3 * cfg.N k ^ (-(M + 1)) ≤ numδ cfg k s ε₁
  phys_le_mesh : 3 * (2 * cfg.K k + 2) * cfg.N k ^ (-(M + 1)) ≤ cfg.N k ^ (-M)
  mesh_le : cfg.N k ^ (-M) ≤ 2 * cfg.K k + 2
  vel_le_one : cfg.N k ^ (-M) ≤ 1
  width_le_one : cfg.parameterWidth k s ≤ 1
  hidden_le_one : cfg.N k ^ (-s) ≤ 1
  fitE : cfg.N k ^ ε₁ * cfg.hiddenWidth k s ≤ numδ cfg k s ε₁ / 2
  fitN : cfg.K k * cfg.N k ^ (-s) +
    36 * cfg.K k ^ 4 * (cfg.N k ^ (-M) + cfg.N k ^ (-M)) ≤ numδ cfg k s ε₁ / 2
  E_one : 1 ≤ numE cfg k ε₁
  E_pow : cfg.N k ^ ε₁ ≤ numE cfg k ε₁
  E_K : 200 * cfg.K k ^ 4 ≤ numE cfg k ε₁
  A₀_pos : 0 < numA₀ cfg k ε₁
  mesh_time : 15360 * numE cfg k ε₁ * cfg.N k ^ (-M) ≤
    numδ cfg k s ε₁ * (cfg.N k ^ (-cfg.κ * s) / cfg.K k)
  mesh_width : 15360 * numE cfg k ε₁ * cfg.N k ^ (-M) ≤
    numδ cfg k s ε₁ * cfg.parameterWidth k s
  scale : R₀ * numδ cfg k s ε₁ ≤ numMst cfg k s ε
  gain : 2000000 * numA₀ cfg k ε₁ * numE cfg k ε₁ ≤
    (numMst cfg k s ε / numδ cfg k s ε₁) ^ η
  mass : (numA₀ cfg k ε₁)⁻¹ * depthBudget cfg k s ε₁ (numδ cfg k s ε₁) <
    cfg.N k ^ (-ε₁) / 2
  loss : ((numA₀ cfg k ε₁)⁻¹ + 2000000 * numA₀ cfg k ε₁ * numE cfg k ε₁ *
      (numMst cfg k s ε / numδ cfg k s ε₁) ^ (-η)) *
      depthBudget cfg k s ε₁ (numδ cfg k s ε₁) ≤ cfg.N k ^ (-ε₁) / 4
  list : 2000000 * numA₀ cfg k ε₁ * numE cfg k ε₁ *
    ((5120 * numMst cfg k s ε) / numδ cfg k s ε₁) ^ cfg.d ≤ cfg.N k ^ ε
  table : cfg.N k ^ (-M) ≤ cfg.N k ^ (-cfg.κ * s) / cfg.K k * cfg.N k ^ (-cfg.κ * s)

set_option maxHeartbeats 1000000 in
theorem eventually_depthNumerics (h : cfg.Prepared) {s M ε ε₁ η R₀ : ℝ}
    (hs : 0 < s) (hMs : s + 2 * cfg.κ * s < M) (hε₁ : 0 < ε₁) (hε₁ε : ε₁ < ε)
    (hε₁s : ε₁ < s) (hη : 0 < η) (hgain : 11 * ε₁ < η * (ε - ε₁))
    (hlist : 7 * ε₁ < (1 - cfg.d) * ε) :
    ∀ᶠ k in atTop, DepthNumerics cfg k s M ε ε₁ η R₀ := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hNt := h.scale_limit
  have hK1 := h.subpower.1
  have hsub := h.subpower.2
  have hκ := h.rate_pos
  have hd0 := h.dimension_nonneg
  have hd1 := h.dimension_lt_one
  have hκs : 0 < 2 * cfg.κ * s := by positivity
  have hκs1 : 0 < cfg.κ * s := by positivity
  -- Eventual comparisons.
  have e1 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 0
    (show ε₁ - s < 0 by linarith) (show (0 : ℝ) ≤ 4 by norm_num)
  have e2 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 1
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) ≤ 12 by norm_num)
  have e3 := hsub ε₁ hε₁
  have e4 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 4
    (show -M < -s by linarith) (show (0 : ℝ) ≤ 72 by norm_num)
  have e5 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 5
    (show -M < -s - cfg.κ * s by nlinarith) (show (0 : ℝ) ≤ 768000 by norm_num)
  have e6 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 4
    (show -M < -s - 2 * cfg.κ * s by linarith) (show (0 : ℝ) ≤ 768000 by norm_num)
  have e7 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 0
    (show ε₁ < ε by linarith) (show (0 : ℝ) ≤ 40 * |R₀| by positivity)
  have e8 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 4
    (show 6 * ε₁ < η * (ε - ε₁) by linarith)
    (show (0 : ℝ) ≤ 400000000 * 40 ^ η by positivity)
  -- The budget constant: B ≤ C₁ K^8 N^(2ε₁).
  have e9 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 8
    (show 2 * ε₁ - 5 * ε₁ < -ε₁ by linarith)
    (show (0 : ℝ) ≤ 8 * 300000000 by norm_num)
  have e10 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 12
    (show 6 * ε₁ - η * (ε - ε₁) + 2 * ε₁ < -ε₁ by linarith)
    (show (0 : ℝ) ≤ 8 * (400000000 * 40 ^ η) * 300000000 by positivity)
  have e11 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 4
    (show 6 * ε₁ + cfg.d * (ε - ε₁) < ε by nlinarith)
    (show (0 : ℝ) ≤ 400000000 * 128 by norm_num)
  have e12 := eventually_subpower_mul_rpow_lt hN1 hNt hK1 hsub 1
    (show -M < -(2 * cfg.κ * s) by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12] with k
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hN : 1 ≤ cfg.N k := hN1 k
  have hNp : 0 < cfg.N k := by linarith
  have hK : 1 ≤ cfg.K k := hK1 k
  have hKp : 0 < cfg.K k := by linarith
  have hadd (x y : ℝ) : cfg.N k ^ x * cfg.N k ^ y = cfg.N k ^ (x + y) :=
    (Real.rpow_add hNp x y).symm
  have hadd' (x y z : ℝ) (hz : x + y = z) : cfg.N k ^ x * cfg.N k ^ y = cfg.N k ^ z := by
    rw [← hz]; exact hadd x y
  have hpos (x : ℝ) : 0 < cfg.N k ^ x := Real.rpow_pos_of_pos hNp x
  have hone (x : ℝ) (hx : 0 ≤ x) : 1 ≤ cfg.N k ^ x := Real.one_le_rpow hN hx
  have hle1 (x : ℝ) (hx : x ≤ 0) : cfg.N k ^ x ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN hx
  have hmono {x y : ℝ} (hxy : x ≤ y) : cfg.N k ^ x ≤ cfg.N k ^ y :=
    Real.rpow_le_rpow_of_exponent_le hN hxy
  have hM : 0 < M := by nlinarith
  simp only [pow_zero, mul_one, one_mul, Real.rpow_zero, pow_one, Real.rpow_one] at h1 h2 h7 h12
  -- Common values.
  have hε₁1 : 1 ≤ cfg.N k ^ ε₁ := hone ε₁ hε₁.le
  have hK4 : 1 ≤ cfg.K k ^ 4 := one_le_pow₀ hK
  have hδ : numδ cfg k s ε₁ = 4 * cfg.N k ^ ε₁ * cfg.N k ^ (-s) := rfl
  have hratio : numMst cfg k s ε / numδ cfg k s ε₁ = cfg.N k ^ (ε - ε₁) / 40 := by
    unfold numMst numδ
    rw [Real.rpow_sub hNp]
    have := hpos ε₁
    have := hpos (-s)
    field_simp
    ring
  have hratio_pow : (cfg.N k ^ (ε - ε₁) / 40) ^ η = cfg.N k ^ (η * (ε - ε₁)) / 40 ^ η := by
    rw [Real.div_rpow (hpos _).le (by norm_num), ← Real.rpow_mul hNp.le, mul_comm]
  have hratio_neg : (cfg.N k ^ (ε - ε₁) / 40) ^ (-η) =
      40 ^ η * cfg.N k ^ (-(η * (ε - ε₁))) := by
    rw [Real.rpow_neg (by positivity), hratio_pow, Real.rpow_neg hNp.le]
    have : (0 : ℝ) < 40 ^ η := by positivity
    have := hpos (η * (ε - ε₁))
    field_simp
  have hA₀E : 2000000 * numA₀ cfg k ε₁ * numE cfg k ε₁ =
      400000000 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) := by
    unfold numA₀ numE
    rw [show (6 : ℝ) * ε₁ = 5 * ε₁ + ε₁ by ring, ← hadd]
    ring
  -- The budget bound B ≤ 3·10^8 K^8 N^(2ε₁).
  have hdb : depthBudget cfg k s ε₁ (numδ cfg k s ε₁) ≤
      300000000 * cfg.K k ^ 8 * cfg.N k ^ (2 * ε₁) := by
    unfold depthBudget
    have hq : numδ cfg k s ε₁ / cfg.hiddenWidth k s = 4 * cfg.N k ^ ε₁ := by
      unfold numδ hiddenWidth
      have := hpos (-s)
      field_simp
    rw [hq]
    have h4 : (4 * cfg.N k ^ ε₁) ^ cfg.d ≤ 4 * cfg.N k ^ ε₁ := by
      calc (4 * cfg.N k ^ ε₁) ^ cfg.d ≤ (4 * cfg.N k ^ ε₁) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hd1.le
        _ = _ := Real.rpow_one _
    have h4' : 0 ≤ (4 * cfg.N k ^ ε₁) ^ cfg.d := by positivity
    have hsum : cfg.N k ^ ε₁ * cfg.K k + 4096 * cfg.K k ^ 6 ≤
        4097 * cfg.K k ^ 6 * cfg.N k ^ ε₁ := by
      have hK6 : cfg.K k ≤ cfg.K k ^ 6 := by
        simpa using pow_le_pow_right₀ hK (show 1 ≤ 6 by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hK6 (hpos ε₁).le]
    have h2e : cfg.N k ^ (2 * ε₁) = cfg.N k ^ ε₁ * cfg.N k ^ ε₁ :=
      (hadd' _ _ _ (by ring)).symm
    rw [h2e]
    have hK8 : cfg.K k ^ 8 = cfg.K k * cfg.K k * cfg.K k ^ 6 := by ring
    rw [hK8]
    have hKK : 2 * cfg.K k + 2 ≤ 4 * cfg.K k := by linarith
    have hpos1 : 0 ≤ cfg.N k ^ ε₁ * cfg.K k + 4096 * cfg.K k ^ 6 := by positivity
    calc 4320 * cfg.K k * (2 * cfg.K k + 2) * (4 * cfg.N k ^ ε₁) ^ cfg.d *
          (cfg.N k ^ ε₁ * cfg.K k + 4096 * cfg.K k ^ 6)
        ≤ 4320 * cfg.K k * (4 * cfg.K k) * (4 * cfg.N k ^ ε₁) *
          (4097 * cfg.K k ^ 6 * cfg.N k ^ ε₁) := by
          gcongr
      _ = 283184640 * (cfg.K k * cfg.K k * cfg.K k ^ 6 * (cfg.N k ^ ε₁ * cfg.N k ^ ε₁)) := by
          ring
      _ ≤ 300000000 * (cfg.K k * cfg.K k * cfg.K k ^ 6 * (cfg.N k ^ ε₁ * cfg.N k ^ ε₁)) := by
          gcongr
          norm_num
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- fit_le_one
    rw [hδ, mul_assoc, hadd, show ε₁ + -s = ε₁ - s by ring]
    exact h1.le
  · -- phys_le_fit
    rw [hδ]
    have h1' := hmono (show -(M + 1) ≤ -s by linarith)
    have h2' : cfg.N k ^ (-s) ≤ cfg.N k ^ ε₁ * cfg.N k ^ (-s) :=
      le_mul_of_one_le_left (hpos _).le hε₁1
    have h3' := mul_pos (hpos ε₁) (hpos (-s))
    rw [mul_assoc]
    linarith
  · -- phys_le_mesh
    rw [show -(M + 1) = -M + -1 by ring, ← hadd, Real.rpow_neg_one]
    have hNi : (cfg.N k)⁻¹ * (3 * (2 * cfg.K k + 2)) ≤ 1 := by
      rw [inv_mul_le_iff₀ hNp]; linarith
    calc 3 * (2 * cfg.K k + 2) * (cfg.N k ^ (-M) * (cfg.N k)⁻¹)
        = cfg.N k ^ (-M) * ((cfg.N k)⁻¹ * (3 * (2 * cfg.K k + 2))) := by ring
      _ ≤ cfg.N k ^ (-M) * 1 := mul_le_mul_of_nonneg_left hNi (hpos _).le
      _ = _ := mul_one _
  · -- mesh_le
    linarith [hle1 (-M) (by linarith)]
  · exact hle1 (-M) (by linarith)
  · exact hle1 _ (by nlinarith)
  · exact hle1 _ (by linarith)
  · -- fitE
    rw [hδ]; unfold hiddenWidth
    have h3' := mul_pos (hpos ε₁) (hpos (-s))
    rw [mul_assoc]
    linarith
  · -- fitN
    rw [hδ]
    have hk : cfg.K k * cfg.N k ^ (-s) ≤ cfg.N k ^ ε₁ * cfg.N k ^ (-s) :=
      mul_le_mul_of_nonneg_right h3 (hpos _).le
    have hm : 72 * cfg.K k ^ 4 * cfg.N k ^ (-M) ≤ cfg.N k ^ ε₁ * cfg.N k ^ (-s) := by
      calc _ ≤ cfg.N k ^ (-s) := h4.le
        _ ≤ _ := le_mul_of_one_le_left (hpos _).le hε₁1
    rw [mul_assoc]
    linarith
  · unfold numE
    have := one_le_mul_of_one_le_of_one_le hK4 hε₁1
    linarith
  · unfold numE
    have := mul_le_mul_of_nonneg_right hK4 (hpos ε₁).le
    linarith
  · unfold numE
    have := mul_le_mul_of_nonneg_left hε₁1 (show (0 : ℝ) ≤ 200 * cfg.K k ^ 4 by positivity)
    linarith
  · exact hpos _
  · -- mesh_time
    rw [hδ]; unfold numE
    have hsκ : cfg.N k ^ (-s) * cfg.N k ^ (-cfg.κ * s) = cfg.N k ^ (-s - cfg.κ * s) :=
      hadd' _ _ _ (by ring)
    rw [mul_div_assoc', le_div_iff₀ hKp]
    have hpe := hpos ε₁
    calc 15360 * (200 * cfg.K k ^ 4 * cfg.N k ^ ε₁) * cfg.N k ^ (-M) * cfg.K k
        = 4 * cfg.N k ^ ε₁ * (768000 * cfg.K k ^ 5 * cfg.N k ^ (-M)) := by ring
      _ ≤ 4 * cfg.N k ^ ε₁ * cfg.N k ^ (-s - cfg.κ * s) :=
          mul_le_mul_of_nonneg_left h5.le (by positivity)
      _ = _ := by rw [← hsκ]; ring
  · -- mesh_width
    rw [hδ]; unfold numE parameterWidth
    have hs2 : cfg.N k ^ (-s) * cfg.N k ^ (-2 * cfg.κ * s) =
        cfg.N k ^ (-s - 2 * cfg.κ * s) := hadd' _ _ _ (by ring)
    have hpe := hpos ε₁
    calc 15360 * (200 * cfg.K k ^ 4 * cfg.N k ^ ε₁) * cfg.N k ^ (-M)
        = 4 * cfg.N k ^ ε₁ * (768000 * cfg.K k ^ 4 * cfg.N k ^ (-M)) := by ring
      _ ≤ 4 * cfg.N k ^ ε₁ * cfg.N k ^ (-s - 2 * cfg.κ * s) :=
          mul_le_mul_of_nonneg_left h6.le (by positivity)
      _ = _ := by rw [← hs2]; ring
  · -- scale
    rw [hδ]; unfold numMst
    have hR : R₀ ≤ |R₀| := le_abs_self R₀
    have hps := hpos (-s)
    have hpe := hpos ε₁
    have : R₀ * (4 * cfg.N k ^ ε₁) ≤ cfg.N k ^ ε / 10 := by
      have h' := mul_le_mul_of_nonneg_right hR (show (0 : ℝ) ≤ 4 * cfg.N k ^ ε₁ by positivity)
      linarith
    calc R₀ * (4 * cfg.N k ^ ε₁ * cfg.N k ^ (-s))
        = (R₀ * (4 * cfg.N k ^ ε₁)) * cfg.N k ^ (-s) := by ring
      _ ≤ (cfg.N k ^ ε / 10) * cfg.N k ^ (-s) := mul_le_mul_of_nonneg_right this hps.le
      _ = _ := by ring
  · -- gain
    rw [hA₀E, hratio, hratio_pow, le_div_iff₀ (by positivity)]
    calc 400000000 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) * 40 ^ η
        = 400000000 * 40 ^ η * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) := by ring
      _ ≤ _ := h8.le
  · -- mass
    unfold numA₀
    rw [← Real.rpow_neg hNp.le]
    have hlt : 300000000 * cfg.K k ^ 8 * cfg.N k ^ (2 * ε₁ - 5 * ε₁) <
        cfg.N k ^ (-ε₁) / 8 := by
      rw [lt_div_iff₀ (by norm_num)]
      linarith [h9]
    calc cfg.N k ^ (-(5 * ε₁)) * depthBudget cfg k s ε₁ (numδ cfg k s ε₁)
        ≤ cfg.N k ^ (-(5 * ε₁)) * (300000000 * cfg.K k ^ 8 * cfg.N k ^ (2 * ε₁)) :=
          mul_le_mul_of_nonneg_left hdb (hpos _).le
      _ = 300000000 * cfg.K k ^ 8 * cfg.N k ^ (2 * ε₁ - 5 * ε₁) := by
          rw [show 2 * ε₁ - 5 * ε₁ = -(5 * ε₁) + 2 * ε₁ by ring, ← hadd]; ring
      _ < cfg.N k ^ (-ε₁) / 8 := hlt
      _ ≤ _ := by linarith [hpos (-ε₁)]
  · -- loss
    have hinv : (numA₀ cfg k ε₁)⁻¹ = cfg.N k ^ (-(5 * ε₁)) := by
      unfold numA₀; rw [Real.rpow_neg hNp.le]
    rw [hinv, hA₀E, hratio, hratio_neg]
    have hfirst : cfg.N k ^ (-(5 * ε₁)) * depthBudget cfg k s ε₁ (numδ cfg k s ε₁) ≤
        cfg.N k ^ (-ε₁) / 8 := by
      calc _ ≤ cfg.N k ^ (-(5 * ε₁)) * (300000000 * cfg.K k ^ 8 * cfg.N k ^ (2 * ε₁)) :=
            mul_le_mul_of_nonneg_left hdb (hpos _).le
        _ = 300000000 * cfg.K k ^ 8 * cfg.N k ^ (2 * ε₁ - 5 * ε₁) := by
            rw [show 2 * ε₁ - 5 * ε₁ = -(5 * ε₁) + 2 * ε₁ by ring, ← hadd]; ring
        _ ≤ _ := by rw [le_div_iff₀ (by norm_num)]; linarith [h9]
    have hexp : cfg.N k ^ (6 * ε₁) * cfg.N k ^ (-(η * (ε - ε₁))) * cfg.N k ^ (2 * ε₁) =
        cfg.N k ^ (6 * ε₁ - η * (ε - ε₁) + 2 * ε₁) := by
      rw [hadd' (6 * ε₁) (-(η * (ε - ε₁))) (6 * ε₁ - η * (ε - ε₁)) (by ring),
        hadd' (6 * ε₁ - η * (ε - ε₁)) (2 * ε₁) _ rfl]
    have hsecond : 400000000 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) *
        (40 ^ η * cfg.N k ^ (-(η * (ε - ε₁)))) * depthBudget cfg k s ε₁ (numδ cfg k s ε₁) ≤
        cfg.N k ^ (-ε₁) / 8 := by
      have hc : 0 ≤ 400000000 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) *
          (40 ^ η * cfg.N k ^ (-(η * (ε - ε₁)))) := by positivity
      calc _ ≤ 400000000 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) *
            (40 ^ η * cfg.N k ^ (-(η * (ε - ε₁)))) *
              (300000000 * cfg.K k ^ 8 * cfg.N k ^ (2 * ε₁)) :=
            mul_le_mul_of_nonneg_left hdb hc
        _ = 400000000 * 40 ^ η * 300000000 * cfg.K k ^ 12 *
            (cfg.N k ^ (6 * ε₁) * cfg.N k ^ (-(η * (ε - ε₁))) * cfg.N k ^ (2 * ε₁)) := by
            ring
        _ = 400000000 * 40 ^ η * 300000000 * cfg.K k ^ 12 *
            cfg.N k ^ (6 * ε₁ - η * (ε - ε₁) + 2 * ε₁) := by rw [hexp]
        _ ≤ _ := by rw [le_div_iff₀ (by norm_num)]; linarith [h10]
    calc (cfg.N k ^ (-(5 * ε₁)) + 400000000 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) *
          (40 ^ η * cfg.N k ^ (-(η * (ε - ε₁))))) * depthBudget cfg k s ε₁ (numδ cfg k s ε₁)
        = cfg.N k ^ (-(5 * ε₁)) * depthBudget cfg k s ε₁ (numδ cfg k s ε₁) +
          400000000 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) *
            (40 ^ η * cfg.N k ^ (-(η * (ε - ε₁)))) *
              depthBudget cfg k s ε₁ (numδ cfg k s ε₁) := by ring
      _ ≤ cfg.N k ^ (-ε₁) / 8 + cfg.N k ^ (-ε₁) / 8 := add_le_add hfirst hsecond
      _ = _ := by ring
  · -- list
    rw [hA₀E]
    have h5120 : 5120 * numMst cfg k s ε / numδ cfg k s ε₁ =
        128 * cfg.N k ^ (ε - ε₁) := by
      rw [mul_div_assoc, hratio]; ring
    rw [h5120, Real.mul_rpow (by norm_num) (hpos _).le, ← Real.rpow_mul hNp.le]
    have h128 : (128 : ℝ) ^ cfg.d ≤ 128 := by
      calc (128 : ℝ) ^ cfg.d ≤ (128 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hd1.le
        _ = 128 := Real.rpow_one _
    have hcomb : cfg.N k ^ (6 * ε₁) * cfg.N k ^ ((ε - ε₁) * cfg.d) =
        cfg.N k ^ (6 * ε₁ + cfg.d * (ε - ε₁)) := hadd' _ _ _ (by ring)
    calc 400000000 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) *
          ((128 : ℝ) ^ cfg.d * cfg.N k ^ ((ε - ε₁) * cfg.d))
        ≤ 400000000 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁) *
          (128 * cfg.N k ^ ((ε - ε₁) * cfg.d)) := by
          gcongr
      _ = 400000000 * 128 * cfg.K k ^ 4 * (cfg.N k ^ (6 * ε₁) * cfg.N k ^ ((ε - ε₁) * cfg.d)) := by ring
      _ = 400000000 * 128 * cfg.K k ^ 4 * cfg.N k ^ (6 * ε₁ + cfg.d * (ε - ε₁)) := by rw [hcomb]
      _ ≤ _ := h11.le
  · -- table
    have h2κ : cfg.N k ^ (-cfg.κ * s) * cfg.N k ^ (-cfg.κ * s) =
        cfg.N k ^ (-(2 * cfg.κ * s)) := hadd' _ _ _ (by ring)
    rw [div_mul_eq_mul_div, h2κ, le_div_iff₀ hKp]
    linarith [h12]

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing
