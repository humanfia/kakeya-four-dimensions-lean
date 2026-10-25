import Submission.Obl.k4_scalar_grid_cartesian_field.OriginalPacketFacts
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketGradient
import Submission.Obl.k4_scalar_grid_cartesian_field.RectangularCaps

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft blockLength blockInterval)

/-- At the fixed normalized mesh the predictor and its gradient are nearly constant.
This uses the original strip norm, including on portions later deleted as steep. -/
theorem OriginalPacketFacts.fine_cell_variations {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) (hN : 2 ≤ data.N k) (hκ : data.κ ≤ 1)
    (hFsmall : 2880 * data.K k ^ 3 ≤ data.N k ^ (9 : ℝ))
    (hGsmall : 23040 * data.K k ^ 5 ≤ data.N k ^ (9 : ℝ)) :
    ∀ x : Incidence, x.1 ∈ data.A k 1 i → x.2 ∈ I data (data.T k 1) (data.j k 1 i) →
    ∀ x' : Incidence, x'.1 ∈ data.A k 1 i → x'.2 ∈ I data (data.T k 1) (data.j k 1 i) →
      (fun e => (⌊normalizedBase (packetLength data k) (originalOrigin data k i) x e /
        data.N k ^ (-10 : ℝ)⌋ : ℤ)) =
      (fun e => (⌊normalizedBase (packetLength data k) (originalOrigin data k i) x' e /
        data.N k ^ (-10 : ℝ)⌋ : ℤ)) →
      |eval ![x.2, scalarY x.1 x.2] (data.F k 1 i) -
        eval ![x'.2, scalarY x'.1 x'.2] (data.F k 1 i)| ≤ data.N k ^ (-1 : ℝ) ∧
      ∀ e, |eval ![x.2, scalarY x.1 x.2] (pderiv e (data.F k 1 i)) -
        eval ![x'.2, scalarY x'.1 x'.2] (pderiv e (data.F k 1 i))| ≤ 1 := by
  intro x hxA hxI x' hx'A hx'I hcell
  let K := data.K k
  let N := data.N k
  let h := packetLength data k
  let ξ := N ^ (-10 : ℝ)
  have hNp : 0 < N := by dsimp [N]; linarith
  have hN₁ : 1 ≤ N := by dsimp [N]; linarith
  have hK : 1 ≤ K := p.budget_one
  have hKpos : 0 < K := by linarith
  have hh : 0 < h := p.positive_horizon
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hNp _
  have hnorm : ∀ t ∈ Icc (blockLeft (data.T k 1) (data.j k 1 i))
      (blockLeft (data.T k 1) (data.j k 1 i) + h), ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, data.u k 1 i + t * data.v k 1 i + h * w] (data.F k 1 i)| ≤ K := by
    intro t ht w hw
    have htI : t ∈ I data (data.T k 1) (data.j k 1 i) := by rw [I_eq_blockInterval]; exact ht
    simpa only [h, packetLength, blockLength, div_eq_mul_inv, mul_comm w] using
      p.predictor_norm t htI w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hv : |data.v k 1 i| ≤ K := by linarith [p.uv_bound, abs_nonneg (data.u k 1 i)]
  have ht : x.2 ∈ Icc (blockLeft (data.T k 1) (data.j k 1 i))
      (blockLeft (data.T k 1) (data.j k 1 i) + h) := by
    simpa only [I_eq_blockInterval, blockInterval, h, packetLength] using hxI
  have ht' : x'.2 ∈ Icc (blockLeft (data.T k 1) (data.j k 1 i))
      (blockLeft (data.T k 1) (data.j k 1 i) + h) := by
    simpa only [I_eq_blockInterval, blockInterval, h, packetLength] using hx'I
  have hy : |scalarY x.1 x.2 - data.u k 1 i - x.2 * data.v k 1 i| ≤ K * h := by
    simpa only [K, h, packetLength, blockLength, div_eq_mul_inv] using (p.fit x.1 hxA x.2 hxI).1
  have hy' : |scalarY x'.1 x'.2 - data.u k 1 i - x'.2 * data.v k 1 i| ≤ K * h := by
    simpa only [K, h, packetLength, blockLength, div_eq_mul_inv] using (p.fit x'.1 hx'A x'.2 hx'I).1
  have hd := normalized_cell_diameter hh hξ hcell
  have hdt : |x.2 - x'.2| ≤ h * ξ := by simpa only [normalizedBase, Matrix.cons_val_zero] using hd 0
  have hdy : |scalarY x.1 x.2 - scalarY x'.1 x'.2| ≤ h * ξ := by
    simpa [normalizedBase] using hd 1
  have hvar := packet_polynomial_cell_variation (data.F k 1 i) p.quadratic hh hK hξ.le hv
    hnorm ht ht' hy hy' hdt hdy
  have hgrad := packet_gradient_cell_variation (data.F k 1 i) p.quadratic hh hK hξ.le hv
    hnorm ht ht' hy hy' hdt hdy
  have hδ : N ^ (-1 : ℝ) ≤ N ^ (-data.κ) := Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)
  have hδh : N ^ (-1 : ℝ) / K ≤ h :=
    (div_le_div_of_nonneg_right hδ hKpos.le).trans p.horizon_lower
  have hξeq : N ^ (9 : ℝ) * ξ = N ^ (-1 : ℝ) := by
    dsimp [ξ]
    rw [← Real.rpow_add hNp]
    norm_num
  have hgradsmall : 23040 * K ^ 4 * ξ ≤ h := by
    apply le_trans ?_ hδh
    apply (le_div_iff₀ hKpos).mpr
    calc
      _ = (23040 * K ^ 5) * ξ := by ring
      _ ≤ N ^ (9 : ℝ) * ξ := mul_le_mul_of_nonneg_right hGsmall hξ.le
      _ = _ := hξeq
  refine ⟨hvar.trans ?_, fun e => (hgrad e).trans ?_⟩
  · exact (mul_le_mul_of_nonneg_right hFsmall hξ.le).trans_eq hξeq
  · exact (div_le_one hh).mpr hgradsmall

end Submission.Obl.k4_scalar_grid_cartesian_field
