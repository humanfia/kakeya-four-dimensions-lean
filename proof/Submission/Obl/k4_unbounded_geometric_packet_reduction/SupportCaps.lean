import Submission.Obl.k4_unbounded_geometric_packet_reduction.PacketInterfaces

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory

/-- Analytical deletions preserve all scalar caps on the same fixed prior.
Supplying finite occupied support completes exactly Q0's scalar input. -/
theorem ScalarCaps.complete_of_support
    {N χ η d s m S U : ℝ} {ν : Measure Traj} {μ μ' : Measure Inc}
    {b : Traj → Fin 5 → ℝ}
    (hcaps : ScalarCaps N χ d s m S U ν μ b) (hN : 1 ≤ N) (hχη : χ ≤ η)
    (hμ : μ' ≤ μ)
    (hsupport : ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) * (N ^ (-m)) ^ 2 ≤ N ^ η * (N ^ (-s)) ^ (-d) ∧
      ∀ᵐ p ∂μ', (scalarZ (b p.1) p.2 (N ^ (-m)),
        ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋) ∈ F) :
    ProjectedScalarLaw N η d s m S U ν μ' b := by
  obtain ⟨hmb, hν, hdom, hunit, hcoeff, hpure, hang, harea⟩ := hcaps
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ χ ≤ N ^ η := Real.rpow_le_rpow_of_exponent_le hN hχη
  refine ⟨⟨hmb, hν, ?_, ?_, fun l i => (hcoeff l i).trans hpow, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · apply hμ.trans (hdom.trans ?_)
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpow) zero_le
  · exact le_antisymm ((hμ _).trans_eq hunit) zero_le
  · exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  · simpa only [Real.rpow_one] using hN
  · intro r q j hr hrs
    apply ((hμ _).trans (hpure r q j hr hrs)).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow (sq_nonneg _))
      (Real.rpow_nonneg (Real.rpow_nonneg hNp.le _) d)
  · obtain ⟨F, hF, hmem⟩ := hsupport
    exact ⟨F, by simpa only [inv_one, mul_one] using hF, hmem⟩
  · intro r q j k hr hrU
    apply ((hμ _).trans (hang r q j k hr hrU)).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow (sq_nonneg _))
        (Real.rpow_nonneg (Real.rpow_nonneg hNp.le _) d))
      (Real.rpow_nonneg hNp.le _)
  · intro r j A hr hrs hA
    apply ((hμ _).trans (harea r j A hr hrs hA)).trans
    apply mul_le_mul_of_nonneg_right _ zero_le
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (Real.rpow_nonneg hNp.le _) d))

end Submission.Obl.k4_unbounded_geometric_packet_reduction
