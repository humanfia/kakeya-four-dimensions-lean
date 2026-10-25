-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.UnionArithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- The square-root part of a sampled one-rich estimate is linear in the
original mass after the coefficient count is applied. -/
theorem sampled_sqrt_mass_le {δ D K N μ M : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hK : 1 ≤ K) (_hN : 0 ≤ N)
    (hμ : 0 < μ) (hM : 0 ≤ M)
    (hpack : δ * N ≤ 2 * K * D) (hsample : M ≤ 4 * N / μ) :
    Real.sqrt (δ / D) * M * Real.sqrt M ≤
      12 * K * N * μ ^ (-(3 / 2 : ℝ)) := by
  have hsample' : μ * M ≤ 4 * N := by
    have := (le_div_iff₀ hμ).mp hsample
    nlinarith only [this]
  have hroot : (Real.sqrt (δ / D) * Real.sqrt M * Real.sqrt μ) ^ 2 ≤ 8 * K := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ δ / D),
      Real.sq_sqrt hM, Real.sq_sqrt hμ.le]
    apply (mul_le_mul_iff_right₀ hD).mp
    calc
      D * (δ / D * M * μ) = δ * (μ * M) := by field_simp
      _ ≤ δ * (4 * N) := mul_le_mul_of_nonneg_left hsample' hδ.le
      _ ≤ D * (8 * K) := by nlinarith only [hpack]
  have hroot' : Real.sqrt (δ / D) * Real.sqrt M * Real.sqrt μ ≤ 3 * K := by
    have hK0 : 0 ≤ K := by linarith
    nlinarith only [hroot, hK, hK0, sq_nonneg (K - 1)]
  have hpow : μ * Real.sqrt μ * μ ^ (-(3 / 2 : ℝ)) = 1 := by
    calc
      _ = μ ^ (1 : ℝ) * μ ^ (1 / 2 : ℝ) * μ ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = μ ^ ((1 : ℝ) + 1 / 2 - 3 / 2) := by
        rw [← Real.rpow_add hμ, ← Real.rpow_add hμ]
        congr 1
      _ = 1 := by norm_num
  calc
    _ = (Real.sqrt (δ / D) * Real.sqrt M * Real.sqrt μ) *
        (μ * M) * μ ^ (-(3 / 2 : ℝ)) := by
      calc
        _ = (Real.sqrt (δ / D) * M * Real.sqrt M) *
          (μ * Real.sqrt μ * μ ^ (-(3 / 2 : ℝ))) := by rw [hpow, mul_one]
        _ = _ := by ring
    _ ≤ (3 * K) * (4 * N) * μ ^ (-(3 / 2 : ℝ)) := by gcongr
    _ = _ := by ring

/-- Both the tangency term and the short-crossing term in a sampled union
bound have the requested richness exponent. -/
theorem sampled_narrow_union_expression_le {δ D K N μ M κ : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hK : 1 ≤ K) (hN : 0 ≤ N)
    (hμ : 0 < μ) (hM : 0 ≤ M)
    (hpack : δ * N ≤ 2 * K * D) (hsample : M ≤ 4 * N / μ)
    (hslope : κ ≤ μ ^ (-(1 / 2 : ℝ))) :
    Real.sqrt (δ / D) * M * Real.sqrt M + κ * M ≤
      16 * K * N * μ ^ (-(3 / 2 : ℝ)) := by
  have hfirst := sampled_sqrt_mass_le hδ hD hK hN hμ hM hpack hsample
  have hrepr : μ ^ (-(1 / 2 : ℝ)) / μ = μ ^ (-(3 / 2 : ℝ)) := by
    calc
      _ = μ ^ (-(1 / 2 : ℝ)) / μ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = μ ^ (-(1 / 2 : ℝ) - 1) := (Real.rpow_sub hμ _ _).symm
      _ = _ := by norm_num
  have hsecond : κ * M ≤ 4 * N * μ ^ (-(3 / 2 : ℝ)) := by
    calc
      _ ≤ μ ^ (-(1 / 2 : ℝ)) * (4 * N / μ) := by gcongr
      _ = _ := by rw [← hrepr]; ring
  have hterm : 0 ≤ N * μ ^ (-(3 / 2 : ℝ)) := by positivity
  nlinarith only [hfirst, hsecond, mul_le_mul_of_nonneg_right hK hterm]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
