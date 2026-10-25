import Submission.Obl.k4_scalar_grid_cartesian_field.RetainedPacket
import Submission.Obl.k4_scalar_grid_cartesian_field.FinalBudget
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketConclusion

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft blockLength blockInterval)

/-- The retained packet gives the exact frozen output, with one common subpower envelope. -/
theorem RetainedPacket.conclusion {data : Data} {k M : ℕ} {Λ B R C : ℝ} {q : ℕ}
    {p : ReadyPacket data k M Λ B R} (r : RetainedPacket p C q) (hC : 0 < C) :
    PacketConclusion data k p.i r.μ (originalOrigin data k p.i) r.𝒯
      (finalBudget C Λ q) (2 * M) 10 B R := by
  let H := finalBudget C Λ q
  have hΛ : 1 ≤ Λ := by simpa only [p.original_Λ] using p.core.hΛ
  have hN : 0 < data.N k := by have := p.core.hN; rw [p.original_N] at this; linarith
  have hK : 1 ≤ data.K k := p.original.budget_one
  have hhpos := p.original.positive_horizon
  have hKpos : 0 < data.K k := by linarith
  have hΛpos : 0 < Λ := by linarith
  obtain ⟨hHone, hHtwo, hHfield, hHpalette, hHmass⟩ := finalBudget_bounds hC hΛ q
  have hΛH : Λ ≤ H := by dsimp [H]; linarith
  have hKH : data.K k ≤ H := p.original_budget.trans hΛH
  have hHpos : 0 < H := by dsimp [H]; linarith
  have hfinalpos : 0 < finalBudget C Λ q := hHpos
  have hcorea : p.core.a = blockLeft (data.T k 1) (data.j k 1 p.i) := by
    have h := congrFun p.original_origin 0
    simpa only [originalOrigin, packetOrigin, Matrix.cons_val_zero] using h
  have hI : Icc p.core.a (p.core.a + p.core.h) = I data (data.T k 1) (data.j k 1 p.i) := by
    rw [hcorea, p.original_h, I_eq_blockInterval]
    rfl
  have hmem : ∀ᵐ x ∂r.μ, x.1 ∈ data.A k 1 p.i ∧
      x.2 ∈ I data (data.T k 1) (data.j k 1 p.i) := by
    have hs := (ae_restrict_mem p.core.measurable_S₀).filter_mono (ae_mono r.dominated)
    filter_upwards [hs] with x hx
    have hp := p.core.subset_packet hx
    exact ⟨p.assignment_subset hp.1, by rw [← hI]; exact hp.2⟩
  have hdom : r.μ ≤ data.ρ k (data.γ k 1 p.i) := by
    rw [← p.original_ρ]
    exact r.dominated.trans Measure.restrict_le_self
  unfold PacketConclusion
  dsimp only
  simp only [show -(2 : ℝ) * 10 = -20 by norm_num, show (2 : ℝ) * 10 = 20 by norm_num]
  refine ⟨p.original.measurable_A, p.original.probability_ν, p.original.probability_π,
    ?_, ?_, ?_, p.original.positive_horizon, p.original.bounded_horizon,
    ?_, ?_, hdom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [p.original.coefficient_bound] with l hl
    exact fun e => (hl e).trans hKH
  · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hN.le _) hKpos hKH).trans p.original.horizon_lower
  · exact p.original.horizon_upper.trans
      (mul_le_mul_of_nonneg_right hKH (Real.rpow_nonneg hN.le _))
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) p.original.prior_lower
    exact div_le_div_of_nonneg_left (by positivity) hKpos hKH
  · exact p.original.prior_upper.trans (ENNReal.ofReal_le_ofReal (by gcongr))
  · apply hdom.trans
    apply p.original.original_density.trans
    intro S
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hKH) le_rfl
  · exact ae_iff.mp hmem
  · calc
      _ = ENNReal.ofReal (1 / H) * (ENNReal.ofReal (packetLength data k) *
          data.ν k (data.γ k 1 p.i) (data.A k 1 p.i)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / H)]
        congr 2
        ring
      _ ≤ ENNReal.ofReal (1 / (2 * C * Λ ^ (q + 1))) *
          (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 p.i) (data.A k 1 p.i)) := by
        apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        exact one_div_le_one_div_of_le (by positivity) hHmass
      _ ≤ _ := r.mass_floor
  · rfl
  · exact fun e => (p.original.center_bound e).trans hKH
  · filter_upwards [hmem] with x hx
    intro t ht e
    exact (p.original.normalized_bound x.1 hx.1 t ht e).trans (by
      exact (mul_le_mul_of_nonneg_left p.original_budget (by norm_num : (0 : ℝ) ≤ 2)).trans hHtwo)
  · intro q₀
    apply (r.dominated _).trans
    apply (p.base_ceiling q₀).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    gcongr
  · intro s hs₀ hs₁
    refine ⟨?_, ?_⟩
    · intro c
      exact (p.angular_cap s hs₀ hs₁ c).trans (ENNReal.ofReal_le_ofReal (by gcongr))
    · intro q₀ c
      exact (r.palette s hs₀ hs₁ q₀ c).trans
        (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hHpalette) le_rfl) le_rfl)
  · intro e
    exact ⟨r.degree e, fun b => (r.coefficients e b).trans hHfield⟩
  · filter_upwards [r.comparison] with x hx
    intro t ht
    have h := hx t (by rwa [hI])
    rw [p.original_error, p.original_h, p.original_origin] at h
    apply h.trans
    calc
      _ = (C * Λ ^ q) * data.N k ^ (-1 : ℝ) * packetLength data k ^ (-(3 : ℝ) / 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hHfield (Real.rpow_nonneg hN.le _))
        (Real.rpow_nonneg hhpos.le _)
  · intro w hwlo hwhi
    obtain ⟨hf, hn⟩ := p.joint_support w hwlo hwhi
    obtain ⟨hfμ, hnμ⟩ := active_count_mono r.dominated _ hf
    have hw : 0 < w := (mul_pos (Real.rpow_pos_of_pos hN _)
      (Real.rpow_pos_of_pos p.original.positive_horizon _)).trans_le hwlo
    have hcount := hnμ.trans (hn.trans (show
      Λ * data.N k ^ (20 : ℝ) * (data.N k ^ (-1 : ℝ) / w) ^ data.d ≤
        H * data.N k ^ (20 : ℝ) * (data.N k ^ (-1 : ℝ) / w) ^ data.d by gcongr))
    simpa only [H, activeCodes, Prod.ext_iff, normalizedBase, y_eq_scalarY, x_eq_scalarX] using
      (And.intro hfμ hcount)

end Submission.Obl.k4_scalar_grid_cartesian_field
