import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.FrameData
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Parents
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set Filter

noncomputable section

/-- Resolving both the frame and its motion uses only the fixed frame budget. -/
theorem resolving_bounds {q K H δ ξ g : ℝ}
    (hq : 0 < q) (hK : 1 ≤ K) (hH : 1 ≤ H) (hδ : 0 < δ)
    (hξg : ξ ≤ g) (hqi : q⁻¹ ≤ H)
    (hsmall : 2 * K * H ^ 2 * δ ≤ ξ) :
    δ ≤ q * ξ ∧ δ ≤ 2 * K * q * g ∧
      K * (1 + H) * δ ≤ q * ξ ∧ K * (1 + H) * δ ≤ 2 * K * q * g := by
  have hK0 : 0 ≤ K := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hL : 1 ≤ K * (1 + H) := by nlinarith
  have hqH : 1 ≤ q * H := by
    calc
      1 = q * q⁻¹ := by field_simp
      _ ≤ q * H := mul_le_mul_of_nonneg_left hqi hq.le
  have hLδ : 0 ≤ K * (1 + H) * δ := by positivity
  have hδL : δ ≤ K * (1 + H) * δ := by nlinarith
  have hHL : H * (K * (1 + H) * δ) ≤ ξ := by
    have hh := mul_le_mul_of_nonneg_left (show 1 + H ≤ 2 * H by linarith)
      (by positivity : 0 ≤ H * K * δ)
    nlinarith only [hh, hsmall]
  have hmotion : K * (1 + H) * δ ≤ q * ξ := by
    have h₁ := mul_le_mul_of_nonneg_left hHL hq.le
    have h₂ := mul_le_mul_of_nonneg_right hqH hLδ
    nlinarith only [h₁, h₂]
  have hqξ : q * ξ ≤ 2 * K * q * g := by
    have hg0 : 0 ≤ g := by
      have hξ0 : 0 ≤ ξ := (show 0 ≤ 2 * K * H ^ 2 * δ by positivity).trans hsmall
      exact hξ0.trans hξg
    have h₁ := mul_le_mul_of_nonneg_left hξg hq.le
    have h₂ := mul_le_mul_of_nonneg_right hK (mul_nonneg hq.le hg0)
    nlinarith only [h₁, h₂, mul_nonneg hK0 (mul_nonneg hq.le hg0)]
  exact ⟨hδL.trans hmotion, (hδL.trans hmotion).trans hqξ,
    hmotion, hmotion.trans hqξ⟩

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

structure FrameMesh {k : ℕ} {r v m ε : ℝ} (f : ListFrame cfg k r v m ε) : Prop where
  fine_le_one : cfg.N k ^ (-(100 * m)) ≤ 1
  mesh_le_transverse : cfg.N k ^ (-m) ≤ cfg.N k ^ (-cfg.ℓ * r)
  cell : cfg.N k ^ (-(100 * m)) ≤ f.q * cfg.N k ^ (-m)
  transverse : cfg.N k ^ (-(100 * m)) ≤
    2 * cfg.K k * f.q * cfg.N k ^ (-cfg.ℓ * r)
  motion_cell : cfg.K k * (1 + cfg.N k ^ (m / 10)) * cfg.N k ^ (-(100 * m)) ≤
    f.q * cfg.N k ^ (-m)
  motion_transverse : cfg.K k * (1 + cfg.N k ^ (m / 10)) * cfg.N k ^ (-(100 * m)) ≤
    2 * cfg.K k * f.q * cfg.N k ^ (-cfg.ℓ * r)
  velocity : |f.zv| ≤ cfg.K k * (1 + cfg.N k ^ (m / 10))
  transverse_velocity : |cfg.c k r f.parent 3 + cfg.c k r f.parent 4 * f.zv| ≤
    cfg.K k * (1 + cfg.N k ^ (m / 10))
  background : 216 * cfg.N k ^ (m / 10) * (2 * cfg.K k) ^ 2 *
    cfg.N k ^ (-(100 * m)) ≤ cfg.N k ^ (-(r + v))

/-- One fixed fine exponent works for every incoming frame, every scalar
hidden test depth, and every later law restriction. -/
theorem Valid.eventually_frame_mesh (h : Valid cfg)
    {r v m : ℝ} (hr : 0 < r) (hv : 0 < v) (hm : 100 * (r + v) < m) :
    ∀ᶠ k in atTop, ∀ ε : ℝ, ∀ f : ListFrame cfg k r v m ε,
      ParentGeometry cfg k r → FrameMesh f := by
  have hm0 : 0 < m := by linarith
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have h₁ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.loss_lower h.loss_subpower 1
    (show -(100 * m) + m / 5 < -m by linarith) (show (0 : ℝ) ≤ 2 by norm_num)
  have h₂ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.loss_lower h.loss_subpower 2
    (show -(100 * m) + m / 10 < -(r + v) by linarith) (show (0 : ℝ) ≤ 864 by norm_num)
  filter_upwards [h₁, h₂] with k h₁ h₂
  intro ε f a
  let H := cfg.N k ^ (m / 10)
  let δ := cfg.N k ^ (-(100 * m))
  let ξ := cfg.N k ^ (-m)
  let g := cfg.N k ^ (-cfg.ℓ * r)
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.loss_lower k
  have hH : 1 ≤ H := Real.one_le_rpow (hN1 k) (by positivity)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN _
  have hpow₁ : H ^ 2 * δ = cfg.N k ^ (-(100 * m) + m / 5) := by
    dsimp [H, δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    ring
  have hpow₂ : H * δ = cfg.N k ^ (-(100 * m) + m / 10) := by
    dsimp [H, δ]
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hsmall : 2 * cfg.K k * H ^ 2 * δ ≤ ξ := by
    rw [mul_assoc (2 * cfg.K k), hpow₁]
    simpa only [pow_one] using h₁.le
  have hξg : ξ ≤ g := by
    apply Real.rpow_le_rpow_of_exponent_le (hN1 k)
    have hℓ : cfg.ℓ ≤ 1 := h.horizontal_rate ▸ h.rate_le_one
    change -m ≤ -cfg.ℓ * r
    nlinarith [mul_le_mul_of_nonneg_right hℓ hr.le]
  have bounds := resolving_bounds f.q_pos hK hH hδ hξg f.frame_component_bounds.1 hsmall
  refine ⟨Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith), hξg,
    bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2, ?_, ?_, ?_⟩
  · have hz := f.frame_component_bounds.2
    have hKH : H ≤ cfg.K k * (1 + H) := by nlinarith
    exact hz.trans hKH
  · calc
      _ ≤ |cfg.c k r f.parent 3| + |cfg.c k r f.parent 4| * |f.zv| := by
        rw [← abs_mul]
        exact abs_add_le _ _
      _ ≤ cfg.K k + cfg.K k * H := by
        gcongr
        · exact a.coefficient_bound f.parent 3
        · exact a.coefficient_bound f.parent 4
        · exact f.frame_component_bounds.2
      _ = _ := by dsimp [H]; ring
  · have hh : 216 * H * (2 * cfg.K k) ^ 2 * δ =
        864 * cfg.K k ^ 2 * cfg.N k ^ (-(100 * m) + m / 10) := by
      rw [← hpow₂]
      ring
    change 216 * H * (2 * cfg.K k) ^ 2 * δ ≤ cfg.N k ^ (-(r + v))
    rw [hh]
    exact h₂.le

end Data

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
