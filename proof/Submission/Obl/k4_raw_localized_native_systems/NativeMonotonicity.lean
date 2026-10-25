import Submission.Obl.k4_raw_localized_native_systems.SplitInterfaces
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

/-!
Adapted from this LOT tree, o197, session x0690, `NativeMonotonicity.lean`
(commit f7206748), renamed into this obligation's namespace.
-/

namespace Submission.Obl.k4_raw_localized_native_systems

open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option maxRecDepth 4096

/-- A construction may use a smaller loss than requested, for instance to fit
the fixed coefficient allowance `χ`. The laws and the witness certificate stay
exactly the same when the requested geometric slack is enlarged. -/
theorem nativeSampleWith_mono_loss {cert : CertificateType}
    {p₀ N K W ω ν E P B M D a₀ w ε loss h χ d s m S U}
    (hN : 1 ≤ N) (hB : ∀ γ, 0 ≤ B γ) (he : ε ≤ loss)
    (hs : NativeSampleWith cert p₀ N K W ω ν E P B M D a₀ w ε h χ d s m S U) :
    NativeSampleWith cert p₀ N K W ω ν E P B M D a₀ w loss h χ d s m S U := by
  obtain ⟨T, C, γ, j, c, u, Q, A, F, lst, α, v, law, Y, X, hs⟩ := hs
  refine ⟨T, C, γ, j, c, u, Q, A, F, lst, α, v, law, Y, X, ?_⟩
  dsimp only at hs ⊢
  obtain ⟨hK, hT, hC, hd, hl, hlm, hc, hcoef, hR, hlaw, hmass, hsupport, hgeo⟩ := hs
  have hκ : N ^ ε ≤ N ^ loss := Real.rpow_le_rpow_of_exponent_le hN he
  have hκpos : 0 < N ^ ε := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _
  refine ⟨hK.trans hκ, hT.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    hC, hd, (fun γ o => (hl γ o).trans hκ), hlm, ?_, hcoef, hR, hlaw, ?_, hsupport, hgeo⟩
  · intro a
    exact k4_quadratic_atlas_normalization.chart_mono hN le_rfl le_rfl hκpos hκ
      (hB (γ a)) (hc a) id
  · exact (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg he))).trans hmass

end
end Submission.Obl.k4_raw_localized_native_systems
