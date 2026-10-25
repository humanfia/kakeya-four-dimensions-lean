import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameBasic
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameNativeBounds

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- Original row centering gives a polynomial bound for the entire
conditional parent prior, without any inverse-width loss. -/
theorem FrameGood.prior_base_bound (hg : FrameGood f Rk θ K₂ e₀') (h1 : D.Basic) :
    ∀ᵐ l ∂cond (D.ν k) f.parentSet,
      |f.coeff l 0| + |f.coeff l 1| + |f.coeff l 3| + |f.coeff l 4| ≤
        2 * D.K k + 2 * D.K k ^ 2 + 2 * (K₂ + D.K k + 1) * D.K k +
          (K₂ + D.K k + 1) := by
  have hK : 0 ≤ D.K k := by linarith [hg.K_ge]
  have hJ : 0 ≤ K₂ + D.K k + 1 := by linarith [hg.K₂_ge]
  have hq := f.q₀_pos
  have hm : f.mid 0 f.i₀ = f.t₀ + f.q₀ / 2 := by
    simp only [Frame.mid, Frame.t₀, Frame.left, Frame.q₀, Frame.T₀, Frame.ql,
      zpow_neg, zpow_natCast, div_eq_mul_inv]
    ring
  have hmt : |f.mid 0 f.i₀ - f.t₀| ≤ f.q₀ := by
    rw [hm, show f.t₀ + f.q₀ / 2 - f.t₀ = f.q₀ / 2 by ring,
      abs_of_nonneg (div_nonneg hq.le (by norm_num : (0 : ℝ) ≤ 2))]
    linarith
  let c := D.c k (f.depth 0) f.i₀
  have hcen : |c 3 + c 0 + f.mid 0 f.i₀ * c 1| + |c 4 - f.mid 0 f.i₀| ≤ K₂ * f.q₀ := by
    simpa only [← f.q₀_eq] using hg.centered 0 (Nat.zero_le _) f.i₀
  obtain ⟨hcenter, hpivot⟩ := parent_center_at_left hq.le hK c
    (hg.cbound 0 (Nat.zero_le _) f.i₀ 1) hmt hcen
  have hg₀ : D.N k ^ (-D.ℓ * f.depth 0) ≤ D.K k * f.q₀ := by
    have hh := hg.g_over_q₀ (Nat.zero_le _)
    simp only [Nat.cast_zero, zero_mul, mul_zero, neg_zero, Real.rpow_zero, mul_one] at hh
    exact (div_le_iff₀ hq).mp hh
  have ht : f.t₀ ∈ f.block 0 f.i₀ := by
    rw [f.parent_block]
    exact ⟨le_rfl, by linarith⟩
  obtain ⟨_, _, _, _, _, _, _, _, hbase, _⟩ := h1 k
  have hv : ∀ᵐ l ∂D.ν k, |D.b k l 3| ≤ D.K k := by
    filter_upwards [hbase] with l hl
    linarith [abs_nonneg (D.b k l 0), abs_nonneg (D.b k l 1), abs_nonneg (D.b k l 4)]
  exact f.parent_prior_base_bound hK hJ hg.measurableSet_parent hg₀ hv
    (fun l hl => by simpa only [← f.q₀_eq] using hg.rows 0 (Nat.zero_le _) f.i₀ l hl f.t₀ ht)
    hcenter hpivot

/-- All basic frame bounds except the retained original residual-mass
comparison follow from the good frame and a polynomial loss allowance. -/
theorem FrameGood.basic_bounds (hg : FrameGood f Rk θ K₂ e₀') (h1 : D.Basic)
    {K' : ℝ} (hK : D.K k ≤ K') (hH : f.H ≤ K')
    (hprior : 2 * D.K k + 2 * D.K k ^ 2 + 2 * (K₂ + D.K k + 1) * D.K k +
      (K₂ + D.K k + 1) ≤ K')
    (hρ : ENNReal.ofReal K'⁻¹ * f.scale ≤ D.ρ k f.core) : FrameBasicBounds f K' :=
  { parent_meas := hg.measurableSet_parent
    parent_pos := hg.parent_pos.ne'
    core_parent := hg.core_parent_event
    density_bound := hK
    native_bound := hH
    prior_bound := (hg.prior_base_bound h1).mono (fun _ hl => hl.trans hprior)
    residual_mass := hρ }

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
