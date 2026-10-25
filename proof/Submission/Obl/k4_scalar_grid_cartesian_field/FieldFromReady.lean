import Submission.Obl.k4_scalar_grid_cartesian_field.Conclude

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- The exact frozen conclusion follows once original qualified packets are prepared for the core. -/
theorem field_of_ready_packets (data : Data) (hscale : scaleHyp data)
    (M : ℕ) (hcore : CartesianCoreStatement M) (Λ : ℕ → ℝ) (hΛ : subpower data Λ)
    (B : ℝ) (hB : 20 ≤ B)
    (hready : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, Nonempty (ReadyPacket data k M (Λ k) B R)) :
    fieldStatement data := by
  obtain ⟨C, q, q₀, hC, hc⟩ := core_packet_output hcore
  apply fieldStatement_of_packet_conclusions data (fun k => finalBudget C (Λ k) q)
    (2 * M) 10 B (finalBudget_subpower hscale hΛ hC q) le_rfl (by linarith)
  intro R hR
  have hsmall : ∀ᶠ k in atTop, max 1 C * Λ k ^ q₀ ≤ data.N k ^ ((1 : ℝ) / 8) := by
    exact eventually_polynomial_subpower_le
      (fun k => by linarith [hscale.1 k]) hscale.2.1 hΛ
      (le_max_left 1 C) q₀ (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [hready R hR, hsmall] with k hk hsmallk
  obtain ⟨p⟩ := hk
  have hN : 0 < data.N k := by linarith [hscale.1 k]
  have hε : 0 ≤ p.core.εT := by
    rw [p.core.hεT, p.original_N]
    exact Real.rpow_nonneg hN.le _
  have hinput : C * p.core.Λ ^ q₀ * p.core.εT ≤ 1 := by
    rw [p.original_Λ]
    calc
      _ ≤ data.N k ^ ((1 : ℝ) / 8) * data.N k ^ (-(1 : ℝ) / 8) :=
        mul_le_mul ((mul_le_mul_of_nonneg_right (le_max_right 1 C) (pow_nonneg (by linarith [hΛ.1 k]) q₀)).trans hsmallk)
          p.error_bound hε (Real.rpow_nonneg hN.le _)
      _ = 1 := by rw [← Real.rpow_add hN]; norm_num
  obtain ⟨r⟩ := p.retain hC (hc p.core hinput)
  exact ⟨p.i, r.μ, originalOrigin data k p.i, r.𝒯, r.conclusion hC⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
