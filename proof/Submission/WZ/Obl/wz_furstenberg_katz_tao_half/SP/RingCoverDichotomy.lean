-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RingCoverDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.BoundedRatioDichotomy
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.LocalizedRatioExpansion

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

theorem Covers.of_real_sum_left {δ a : ℝ} {A B : Finset ℝ} (ha : a ∈ A)
    {m : ℕ} {cc : Fin m → ℝ} (h : Covers δ (↑(A + B) : Set ℝ) cc) :
    Covers δ (↑B : Set ℝ) (fun j => cc j - a) := by
  intro b hb
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (h (Finset.add_mem_add ha hb))
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  simpa only [Metric.mem_closedBall, Real.dist_eq,
    show b - (cc j - a) = a + b - cc j by ring] using hj

/-- Either density of ratios or an escaping bounded ratio gives a lower bound
for a cover of one fixed expression formed from sums and products of `A`. -/
theorem ring_cover_dichotomy (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ δ q C σ : ℝ,
      0 < δ → δ ≤ q → q ≤ 1 → 16 * δ / (q * q) ≤ ρ₀ →
      1 ≤ C → 1 / 2 ≤ σ →
      ∀ A : Finset ℝ, A.Nonempty → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
        RealFiniteFrostman δ C σ A →
        (∃ c ∈ A, ∃ d ∈ A, q ≤ |c - d|) →
        ∀ (m : ℕ) (cc : Fin m → ℝ),
          Covers δ (↑(A + fourProductDifference A) : Set ℝ) cc →
          (16 * δ / (q * q)) ^ (ε - 1) ≤ (max (C * C) 40) ^ 2 * (m : ℝ) ∨
            1 ≤ C ^ 3 * (128 * δ * q) ^ σ * (m : ℝ) := by
  classical
  obtain ⟨ρ₀, hρ₀, hcore⟩ := dense_slope_projection_count ε hε
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro δ q C σ hδ hδq hq1 hsmall hC hσ A hAne hA hAF hpair m cc hcov
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
    obtain ⟨t, ht, htI, hprojection⟩ := hcore (16 * δ / (q * q)) C C σ σ
      (by positivity) hsmall hC hC (by linarith) A A hAne hAne hAF' hAF'
      (LargeDenominatorRatios q A) hdense'
    obtain ⟨a, ha⟩ := hAne
    have hS := hcov.of_real_sum_left ha
    have hzero : (0 : ℝ) ∈ A * A - A * A := by
      simpa only [sub_self, zero_mul] using product_difference_mem ha ha ha
    have hsub : (A * A - A * A) + (A * A - A * A) ⊆ fourProductDifference A := by
      intro x hx
      have hh := Finset.add_mem_add hx (Finset.add_mem_add hzero hzero)
      simpa only [fourProductDifference, add_zero, zero_add] using hh
    obtain ⟨centers, hcenters⟩ := (hS.mono_set hsub).ratio_projection hδ.le hq ht
    have hscale : δ / q ≤ 16 * δ / (q * q) := by
      have h1 : δ / q * (q * q) = δ * q := by field_simp
      apply (le_div_iff₀ (mul_pos hq hq)).mpr
      rw [h1]
      nlinarith
    exact hprojection m centers (hcenters.mono_radius hscale)
  · obtain ⟨r, hr, hrI, e, he, hgap⟩ := hescape
    exact Or.inr (localized_half_escape_sum_count hδ hδq (by linarith) A hAne hA hAF
      hr hrI he hgap cc hcov)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
