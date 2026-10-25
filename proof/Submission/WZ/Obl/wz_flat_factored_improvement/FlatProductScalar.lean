-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.FlatProductScalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Scalar

namespace WangZahlLot.Obl.wz_flat_factored_improvement

/-- The fine and coarse body estimates recover the tube profile with its full
aspect-ratio gain. Balance and saturation remove the intermediate counts. -/
theorem flat_product_scalar {σ u ε Af Ac δ a b c l n q N s D : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hAf : 0 < Af) (hAc : 0 < Ac) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l)
    (hn : 0 < n) (hq : 0 < q) (hN : 0 < N)
    (hD : 1 ≤ D) (hDmax : D ≤ δ ^ (-s))
    (hcover : n ≤ q * D * N) (hsat : N * δ ^ 2 ≤ 16 * c * a * b)
    (herr : ε / 2 + 7 * s ≤ ε) :
    (b / a) ^ u *
        profile σ u ε (Af * Ac / 432 * (16 : ℝ) ^ (-1 + 3 / 2 * σ)) δ c l n ≤
      ((Af / 432) * δ ^ (ε / 4 + (4 + σ) * s) * (δ / a) ^ u *
        (a * b) ^ (-σ) * N ^ (σ / 2) * δ ^ (2 * σ)) *
      (Ac * δ ^ (ε / 4) * b ^ u * D ^ (-2 : ℝ) * l ^ (-σ) *
        q ^ (1 - σ) * (a * b) ^ (1 - σ / 2)) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hcount := mul_le_mul_of_nonneg_left (Real.log_le_log hn hcover)
    (by linarith : 0 ≤ 1 - σ)
  have hoccupancy := mul_le_mul_of_nonpos_left
    (Real.log_le_log (by positivity : 0 < N * δ ^ 2) hsat)
    (by linarith : -1 + 3 / 2 * σ ≤ 0)
  have hdegree := mul_le_mul_of_nonpos_left (Real.log_le_log hDpos hDmax)
    (by linarith : -3 + σ ≤ 0)
  have herror := mul_le_mul_of_nonpos_right herr (Real.log_nonpos hδ.le hδ1)
  rw [profile_eq hδ hc hl hn]
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv,
    Real.log_rpow, Real.log_pow] at hcount hoccupancy hdegree ⊢
  nlinarith only [hcount, hoccupancy, hdegree, herror]

end WangZahlLot.Obl.wz_flat_factored_improvement
