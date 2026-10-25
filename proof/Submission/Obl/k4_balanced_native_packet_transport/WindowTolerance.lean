import Submission.Obl.k4_balanced_native_packet_transport.WindowSelection

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Set
noncomputable section

/-- The same earlier reference laws work at a larger scalar tolerance. The
second-derivative allowance is unchanged because its two powers cancel. -/
theorem WindowCertificate.mono_chi
    {N χ χ' d s m : ℝ} {C : ℕ} {R : Fin C → ENNReal}
    {μ : Fin C → Measure Inc} {b : Fin C → Traj → Fin 5 → ℝ}
    (hN : 1 ≤ N) (hχ : χ ≤ χ') (h : WindowCertificate N χ d s m C R μ b) :
    WindowCertificate N χ' d s m C R μ b := by
  obtain ⟨J, w, Λ, P, S, tag, A, z, hw, htwo, href, hA, hcharge,
    hsignal, hcount, hclose⟩ := h
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ χ ≤ N ^ χ' := Real.rpow_le_rpow_of_exponent_le hN hχ
  have hwidth : N ^ (-s + χ) ≤ N ^ (-s + χ') :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hinv : (N ^ χ')⁻¹ ≤ (N ^ χ)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNpos χ) hpow
  have hratio : N ^ χ / N ^ (-s + χ) = N ^ χ' / N ^ (-s + χ') := by
    rw [← Real.rpow_sub hNpos, ← Real.rpow_sub hNpos]
    congr 1
    ring
  refine ⟨J, w, Λ, P, S, tag, A, z, hw, htwo.trans hpow,
    ?_, hA, hcharge, hsignal, ?_, ?_⟩
  · intro e
    obtain ⟨hprob, hP, hS, hbase, hpoint⟩ := href e
    refine ⟨hprob, hP, hS, hbase.trans ?_, ?_⟩
    · intro E
      rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl
    · filter_upwards [hpoint] with p hp
      obtain ⟨hb, hP₀, hdlo, hdhi, hdd, hS₀, hSd, hSdd⟩ := hp
      exact ⟨hb.trans hpow,
        hP₀.trans (mul_le_mul hpow hwidth (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)),
        hinv.trans hdlo, hdhi.trans hpow, hdd.trans_eq hratio,
        hS₀.trans hpow, hSd.trans hpow, hSdd.trans hpow⟩
  · intro a t y
    exact (hcount a t y).trans
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  · intro a p hp p' hp' heq ht hy
    exact (hclose a p hp p' hp' heq ht hy).trans hwidth

end
end Submission.Obl.k4_balanced_native_packet_transport
