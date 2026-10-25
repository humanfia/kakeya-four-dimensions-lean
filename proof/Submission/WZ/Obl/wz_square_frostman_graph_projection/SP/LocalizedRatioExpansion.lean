-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.LocalizedRatioExpansion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.LocalSumCover
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.HalfRatioNumerator
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RatioGapFrostman

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- Localizing the numerator projection removes the small-denominator loss.
An escaping ratio forces growth in a fixed additive expression in products. -/
theorem localized_half_escape_sum_count {δ q C σ r e : ℝ}
    (hδ : 0 < δ) (hδq : δ ≤ q) (hC : 0 ≤ C)
    (A : Finset ℝ) (hAne : A.Nonempty)
    (hA : ∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) (hAF : RealFiniteFrostman δ C σ A)
    (hr : r ∈ LargeDenominatorRatios q A) (hrI : r ∈ Set.Icc (0 : ℝ) 1)
    (he : e = 0 ∨ e = 1)
    (hgap : ∀ s ∈ LargeDenominatorRatios q A, 8 * δ / (q * q) < dist ((r + e) / 2) s)
    {m : ℕ} (cc : Fin m → ℝ)
    (hcov : Covers δ (↑(A + fourProductDifference A) : Set ℝ) cc) :
    1 ≤ C ^ 3 * (128 * δ * q) ^ σ * (m : ℝ) := by
  classical
  have hq : 0 < q := hδ.trans_le hδq
  obtain ⟨c, hc, d, hd, hden, T, hTS, hTbound, hTmem⟩ :=
    half_ratio_numerator hq A hA hr hrI he
  have hD : 0 < |c - d| := hq.trans_le hden
  have hne : c - d ≠ 0 := abs_pos.mp hD
  have hD1 : |c - d| ≤ 1 := abs_le.mpr ⟨by linarith [(hA c hc).1, (hA d hd).2],
    by linarith [(hA c hc).2, (hA d hd).1]⟩
  have hcovT : Covers δ (↑(A + T) : Set ℝ) cc := by
    apply hcov.mono_set
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    exact Finset.add_mem_add ha (hTS hb)
  obtain ⟨n, centers, hcover, hn⟩ := local_cover_of_sum_cover A T hδ
    (by linarith : δ ≤ 4 * |c - d|) hC hAne hAF
    (z := 0) (fun x hx => by simpa only [dist_zero_right, Real.norm_eq_abs] using hTbound x hx)
    cc hcovT
  let ρ := 4 * δ / |c - d|
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hδρ : δ ≤ ρ := by
    apply (le_div_iff₀ hD).mpr
    nlinarith
  have hcovP : Covers ρ ((fun p : ℝ × ℝ => p.1 + ((r + e) / 2) * p.2) ''
      (↑(A ×ˢ A) : Set (ℝ × ℝ))) (fun j => centers j / (2 * (c - d))) := by
    rintro x ⟨p, hp, rfl⟩
    have hp' := Finset.mem_product.mp hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover (hTmem p.1 hp'.1 p.2 hp'.2))
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    change dist (p.1 + ((r + e) / 2) * p.2) (centers j / (2 * (c - d))) ≤ ρ
    have hid : p.1 + ((r + e) / 2) * p.2 - centers j / (2 * (c - d)) =
        (2 * (c - d) * (p.1 + ((r + e) / 2) * p.2) - centers j) / (2 * (c - d)) := by
      field_simp
    rw [Real.dist_eq, hid, abs_div]
    have hj' : |2 * (c - d) * (p.1 + ((r + e) / 2) * p.2) - centers j| ≤ 4 * δ := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hj
    have hD2 : |c - d| ≤ |2 * (c - d)| := by rw [abs_mul]; norm_num; linarith
    exact (div_le_div_of_nonneg_right hj' (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) hD hD2)
  have hthreshold : 2 * ρ / q ≤ 8 * δ / (q * q) := by
    have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 4 * δ) hq hden
    calc 2 * ρ / q ≤ 2 * (4 * δ / q) / q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num)) hq.le
      _ = _ := by ring
  have hg := ratio_gap_frostman_count hδ hδρ hδq hC A hAne hAF
    (fun s hs => hthreshold.trans_lt (hgap s hs)) _ hcovP
  calc
    1 ≤ (n : ℝ) * C ^ 2 * (ρ * q) ^ σ := hg
    _ ≤ (C * (8 * (4 * |c - d|)) ^ σ * (m : ℝ)) * C ^ 2 * (ρ * q) ^ σ := by
      gcongr
    _ = C ^ 3 * (128 * δ * q) ^ σ * (m : ℝ) := by
      have hid : (8 * (4 * |c - d|)) * (ρ * q) = 128 * δ * q := by dsimp [ρ]; field_simp; ring
      calc
        (C * (8 * (4 * |c - d|)) ^ σ * (m : ℝ)) * C ^ 2 * (ρ * q) ^ σ =
            C ^ 3 * ((8 * (4 * |c - d|)) ^ σ * (ρ * q) ^ σ) * (m : ℝ) := by ring
        _ = _ := by rw [← Real.mul_rpow (by positivity) (by positivity), hid]

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
