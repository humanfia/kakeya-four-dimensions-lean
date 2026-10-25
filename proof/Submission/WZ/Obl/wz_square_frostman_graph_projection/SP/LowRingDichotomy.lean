-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.LowRingDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RingCoverDichotomy
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PowerSlopeProjection

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- The bounded ratio alternative, with a low-dimensional dense branch. -/
theorem low_ring_cover_dichotomy {δ q C σ : ℝ}
    (hδ : 0 < δ) (hδq : δ ≤ q) (hq1 : q ≤ 1) (hsmall : 16 * δ / (q * q) ≤ 1)
    (hC : 1 ≤ C) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (A : Finset ℝ) (hAne : A.Nonempty) (hA : ∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1)
    (hAF : RealFiniteFrostman δ C σ A) (hpair : ∃ c ∈ A, ∃ d ∈ A, q ≤ |c - d|)
    (m : ℕ) (cc : Fin m → ℝ) (hcov : Covers δ (↑(A + fourProductDifference A) : Set ℝ) cc) :
    1 ≤ (320 * C ^ 2 * energyConstant (3 / 4) * (16 * δ / (q * q)) ^ (3 * σ / 2)) * (m : ℝ) ∨
      1 ≤ C ^ 3 * (128 * δ * q) ^ σ * (m : ℝ) := by
  classical
  have hq : 0 < q := hδ.trans_le hδq
  have hq2 : q * q ≤ 1 := by nlinarith
  have hδρ : δ ≤ 16 * δ / (q * q) := by
    apply (le_div_iff₀ (mul_pos hq hq)).mpr
    nlinarith
  rcases bounded_large_ratio_dichotomy (h := 8 * δ / (q * q)) hq A hpair with hdense | hescape
  · left
    have hdense' : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ LargeDenominatorRatios q A,
        t ∈ Set.Icc (0 : ℝ) 1 ∧ dist t x ≤ 16 * δ / (q * q) := by
      intro x hx
      obtain ⟨t, ht, htI, htx⟩ := hdense x hx
      refine ⟨t, ht, htI, ?_⟩
      convert htx using 1 <;> ring
    have hAF' : RealFiniteFrostman (16 * δ / (q * q)) C σ A :=
      fun x ρ hρ => hAF x ρ (hδρ.trans hρ)
    obtain ⟨t, ht, htI, hprojection⟩ := dense_slope_low_projection
      (by positivity : 0 < 16 * δ / (q * q)) hsmall hC hσ hσ1 A hAne hAF'
      (LargeDenominatorRatios q A) hdense'
    obtain ⟨a, ha⟩ := hAne
    have hS := Covers.of_real_sum_left ha hcov
    have hzero : (0 : ℝ) ∈ A * A - A * A := by
      simpa only [sub_self, zero_mul] using product_difference_mem ha ha ha
    have hsub : (A * A - A * A) + (A * A - A * A) ⊆ fourProductDifference A := by
      intro x hx
      have hh := Finset.add_mem_add hx (Finset.add_mem_add hzero hzero)
      simpa only [fourProductDifference, add_zero, zero_add] using hh
    obtain ⟨centers, hcenters⟩ := Covers.ratio_projection hδ.le hq ht (hS.mono_set hsub)
    have hscale : δ / q ≤ 16 * δ / (q * q) := by
      have h1 : δ / q * (q * q) = δ * q := by field_simp
      apply (le_div_iff₀ (mul_pos hq hq)).mpr
      rw [h1]
      nlinarith
    exact hprojection m centers (hcenters.mono_radius hscale)
  · obtain ⟨r, hr, hrI, e, he, hgap⟩ := hescape
    exact Or.inr (localized_half_escape_sum_count hδ hδq (by linarith) A hAne hA hAF
      hr hrI he hgap cc hcov)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
