import Submission.Obl.k4_scalar_candidate_original_return.Core.PlankBasic
import Submission.Obl.k4_scalar_candidate_original_return.Core.LayerMass

/-!
# The per-plank hypotheses hold at all late stages
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid)
include ha

theorem eventually_plankHyp (π : CmpParams)
    (hpar : 0 < π.σ.s₀ ∧ 0 < π.σ.c₀ ∧ 0 < π.θ ∧ π.θ ≤ π.εm / 16 ∧ 0 < π.εm ∧ π.εm ≤ 1 / 2) :
    ∀ᶠ k in atTop, ∀ s : ℝ, |s - π.σ.s₀| ≤ π.θ * π.σ.c₀ / 4 → |s - π.σ.s₀| ≤ π.σ.s₀ / 2 →
      ∀ i : Fin (a.ls k (a.nd k s)).n, a.PlankHyp π k (a.nd k s) i s := by
  obtain ⟨hs0, hc0, hθ0, hθεm, hεm0, hεm1⟩ := hpar
  have hTI := ha.tangent_input
  have hN2 : ∀ k, 2 ≤ a.tangent k := hTI.1
  have hNtend : Tendsto a.tangent atTop atTop := hTI.2.1
  have hK1 : ∀ k, 1 ≤ a.rK k := hTI.2.2.1.1
  have hKsub := hTI.2.2.1.2
  have hd0 : 0 ≤ a.rd := hTI.2.2.2.1
  have hd1 : a.rd < 1 := hTI.2.2.2.2.1
  have hκ0 : 0 < a.κ := hTI.2.2.2.2.2.1
  have hκ1 : a.κ ≤ 1 := hTI.2.2.2.2.2.2.1
  have hb9 := hTI.2.2.2.2.2.2.2.2.1
  have hb10 := hTI.2.2.2.2.2.2.2.2.2.1
  have hb11 := hTI.2.2.2.2.2.2.2.2.2.2
  have hkap : 0 < kap0 π := by unfold kap0; positivity
  have hθ1 : π.θ ≤ 1 / 32 := by linarith
  have hs' : 0 < π.s' := by
    unfold CmpParams.s'
    nlinarith
  have hr : 2 ≤ π.r := by
    unfold CmpParams.r
    have : (0 : ℝ) ≤ (π.σ.R : ℝ) := Nat.cast_nonneg _
    linarith
  set R₁ : ℝ := π.r + 2 / π.s' + 2 / π.σ.s₀ + 2 * π.σ.s₀ + π.s' + 2 with hR₁
  have h2s' : 0 < 2 / π.s' := by positivity
  have h2s0 : 0 < 2 / π.σ.s₀ := by positivity
  have hR₁1 : 1 < R₁ := by rw [hR₁]; linarith
  have hR₁pos : 0 < R₁ := by linarith
  have hR₁inv : R₁⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hR₁pos (by norm_num)]
    rw [hR₁]; norm_num; linarith
  have e1 := hb10 R₁ hR₁1
  have e2 := hb11 R₁ hR₁1
  have e3 := hKsub (kap0 π) hkap
  have e4 := H_subpower ha (kap0 π) hkap
  have e5 : ∀ᶠ k in atTop, (10 : ℝ) ^ 30 ≤ a.tangent k ^ (kap0 π) :=
    ((tendsto_rpow_atTop hkap).comp hNtend).eventually_ge_atTop _
  have e6 : ∀ᶠ k in atTop, π.R₀ ≤ a.tangent k ^ π.σ.c₀ :=
    ((tendsto_rpow_atTop hc0).comp hNtend).eventually_ge_atTop _
  have e7 : ∀ᶠ k in atTop, a.sc k * (π.s' + 2) < L (a.p k) :=
    ha.range (π.s' + 2) (by linarith)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7] with k h1 h2 h3 h4 h5 h6 h7
  intro s hsθ hshalf i
  have hsabs := abs_le.mp hshalf
  have hs_lo : R₁⁻¹ ≤ s := by
    have hRinv : R₁⁻¹ ≤ π.σ.s₀ / 2 := by
      rw [inv_le_comm₀ hR₁pos (by positivity)]
      have he : (π.σ.s₀ / 2)⁻¹ = 2 / π.σ.s₀ := by field_simp
      rw [he, hR₁]
      linarith
    linarith [hsabs.1]
  have hs_hi : s ≤ R₁ := by rw [hR₁]; linarith [hsabs.2]
  obtain ⟨hTl, hTu, hmeas, hdisj, hplank, hcov⟩ := h2 s hs_lo hs_hi
  obtain ⟨hνl, hνu, hρl, huv, hFdeg, hFb, hfit⟩ := hplank i
  have hrR : π.r ≤ R₁ := by rw [hR₁]; linarith
  have hrR' : R₁⁻¹ ≤ π.r := by linarith
  have hs'R : π.s' ≤ R₁ := by rw [hR₁]; linarith
  have hs'R' : R₁⁻¹ ≤ π.s' := by
    rw [inv_le_comm₀ hR₁pos hs']
    have : π.s'⁻¹ ≤ 2 / π.s' := by
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by norm_num) hs'.le
    rw [hR₁]; linarith
  have h1R : (1 : ℝ) ≤ R₁ := hR₁1.le
  have h1R' : R₁⁻¹ ≤ 1 := by linarith
  have hnc := (h1 ((a.ls k (a.nd k s)).world i) π.r π.s' 1 hrR' hrR hs'R' hs'R h1R' h1R).2.1
  have h9 := (hb9 k).2.2.1 ((a.ls k (a.nd k s)).world i)
  -- the layer's line bounds
  have hCD := (ha.layer k (a.nd k s)).2.2.1
  have hlinebd := (hCD.2.2.2.2.2.1 i).2.2.2.2.2.2.2.1
  have hHfac : a.original k ^ (Real.log (a.H k) / Real.log (a.original k)) = a.H k :=
    ha.scales.original_rpow_log_factor k
  -- the original observation resolution
  have hN0 : 2 ≤ a.original k := ha.scales.original_ge_two k
  have hN0pos : 0 < a.original k := by linarith
  have hNk : 2 ≤ a.tangent k := hN2 k
  have hNpos : 0 < a.tangent k := by linarith
  have hobs : a.obsRes k ≤ a.tangent k ^ (-π.s') / 4 := by
    unfold obsRes
    have hle : a.original k ^ (-L (a.p k)) ≤ a.original k ^ (a.sc k * (-(π.s' + 2))) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
    have heq : a.original k ^ (a.sc k * (-(π.s' + 2))) =
        a.tangent k ^ (-π.s') * a.tangent k ^ (-2 : ℝ) := by
      rw [Real.rpow_mul hN0pos.le, ← Real.rpow_add hNpos]
      unfold tangent
      congr 1
      ring
    have h2 : a.tangent k ^ (-2 : ℝ) ≤ 1 / 4 := by
      rw [Real.rpow_neg hNpos.le]
      have : (4 : ℝ) ≤ a.tangent k ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        nlinarith
      rw [one_div]
      exact inv_anti₀ (by norm_num) this
    have hpos : 0 < a.tangent k ^ (-π.s') := Real.rpow_pos_of_pos hNpos _
    calc a.original k ^ (-L (a.p k)) ≤ a.original k ^ (a.sc k * (-(π.s' + 2))) := hle
      _ = a.tangent k ^ (-π.s') * a.tangent k ^ (-2 : ℝ) := heq
      _ ≤ a.tangent k ^ (-π.s') * (1 / 4) := mul_le_mul_of_nonneg_left h2 hpos.le
      _ = a.tangent k ^ (-π.s') / 4 := by ring
  exact
    { par_pos := ⟨hs0, hc0, hθ0, hθεm, hεm0, hεm1⟩
      d_range := ⟨hd0, hd1⟩
      κ_range := ⟨hκ0, hκ1⟩
      s_win := ⟨hsθ, hshalf⟩
      N_ge := hNk
      K_ge := hK1 k
      H_ge := (ha.bounds k).2.2.1
      K_small := h3
      H_small := h4
      N_large := h5
      R0_le := h6
      obs_small := hobs
      T_lower := hTl
      T_upper := hTu
      nu_lower := hνl
      nu_upper := hνu
      nu_prob := h9.1
      rho_le := h9.2.2.2.1
      rho_finite := rho_finite ha k _
      uv_le := huv
      F_deg := hFdeg
      F_bound := hFb
      fit := hfit
      lines := fun l hl e => ((hlinebd l hl).2 e).trans_eq hHfac
      prior_meas := hmeas i
      noncon := hnc }

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
