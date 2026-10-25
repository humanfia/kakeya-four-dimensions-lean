-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.DenseRatioProducts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.DenseSlopeProjection

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

def LargeDenominatorRatios (q : ℝ) (A : Finset ℝ) : Set ℝ :=
  {t | ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A, q ≤ |c - d| ∧ t = (a - b) / (c - d)}

theorem Covers.ratio_projection {δ q : ℝ} (hδ : 0 ≤ δ) (hq : 0 < q)
    {A : Finset ℝ} {t : ℝ} (ht : t ∈ LargeDenominatorRatios q A)
    {m : ℕ} {cc : Fin m → ℝ}
    (hcov : Covers δ (↑((A * A - A * A) + (A * A - A * A)) : Set ℝ) cc) :
    ∃ centers : Fin m → ℝ,
      Covers (δ / q) ((fun p : ℝ × ℝ => p.1 + t * p.2) ''
        (↑(A ×ˢ A) : Set (ℝ × ℝ))) centers := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hden, rfl⟩ := ht
  have hdenp : 0 < |c - d| := hq.trans_le hden
  have hne : c - d ≠ 0 := abs_pos.mp hdenp
  refine ⟨fun j => cc j / (c - d), ?_⟩
  rintro z ⟨p, hp, rfl⟩
  have hp' := Finset.mem_product.mp hp
  have hmem : (c - d) * (p.1 + (a - b) / (c - d) * p.2) ∈
      (A * A - A * A) + (A * A - A * A) := by
    have hid : (c - d) * (p.1 + (a - b) / (c - d) * p.2) =
        (c * p.1 - d * p.1) + (a * p.2 - b * p.2) := by field_simp
    rw [hid]
    exact Finset.add_mem_add
      (Finset.sub_mem_sub (Finset.mul_mem_mul hc hp'.1) (Finset.mul_mem_mul hd hp'.1))
      (Finset.sub_mem_sub (Finset.mul_mem_mul ha hp'.2) (Finset.mul_mem_mul hb hp'.2))
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hmem)
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  change dist (p.1 + (a - b) / (c - d) * p.2) (cc j / (c - d)) ≤ δ / q
  have hid : p.1 + (a - b) / (c - d) * p.2 - cc j / (c - d) =
      ((c - d) * (p.1 + (a - b) / (c - d) * p.2) - cc j) / (c - d) := by
    field_simp
  rw [Real.dist_eq, hid, abs_div]
  exact (div_le_div_of_nonneg_right (show |(c - d) *
    (p.1 + (a - b) / (c - d) * p.2) - cc j| ≤ δ by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hj) hdenp.le).trans
        (div_le_div_of_nonneg_left hδ hq hden)

/-- The dense-ratio branch of a discretized sum-product argument. A dense
set of ratios with denominators bounded below forces a large four-product
sum-difference set. The denominator loss is retained in the output scale. -/
theorem dense_ratio_product_count (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ δ q C σ : ℝ,
      0 < δ → 0 < q → q ≤ 1 → δ / q ≤ ρ₀ → 1 ≤ C → 1 / 2 ≤ σ →
      ∀ A : Finset ℝ, A.Nonempty → RealFiniteFrostman δ C σ A →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ LargeDenominatorRatios q A,
          t ∈ Set.Icc (0 : ℝ) 1 ∧ dist t x ≤ δ / q) →
        ∀ (m : ℕ) (cc : Fin m → ℝ),
          Covers δ (↑((A * A - A * A) + (A * A - A * A)) : Set ℝ) cc →
          (δ / q) ^ (ε - 1) ≤ (max (C * C) 40) ^ 2 * (m : ℝ) := by
  obtain ⟨ρ₀, hρ₀, hcount⟩ := dense_slope_projection_count ε hε
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro δ q C σ hδ hq hq1 hsmall hC hσ A hA hAF hdense m cc hcov
  have hδρ : δ ≤ δ / q := (le_div_iff₀ hq).mpr (by nlinarith)
  have hAF' : RealFiniteFrostman (δ / q) C σ A := fun x r hr => hAF x r (hδρ.trans hr)
  obtain ⟨t, ht, htrange, htcount⟩ := hcount (δ / q) C C σ σ (div_pos hδ hq) hsmall hC hC
    (by linarith) A A hA hA hAF' hAF' (LargeDenominatorRatios q A) hdense
  obtain ⟨centers, hcenters⟩ := hcov.ratio_projection hδ.le hq ht
  exact htcount m centers hcenters

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
