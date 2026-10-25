-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarSelfSum.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarFamilyCover

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- One small projection with a nonzero scalar already bounds the self-sum. -/
theorem SmallScalarProjection.self_sum {δ u K : ℝ} {A : Finset ℝ}
    (hδ : 0 < δ) (hu : 0 < u) (hu1 : u ≤ 1) (hK : 0 ≤ K)
    (hA : A.Nonempty) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (ha : SmallScalarProjection δ A K u) :
    SmallScalarProjection δ A (144 * K ^ 2 / u) 1 := by
  classical
  obtain ⟨m, ca, hca, hm⟩ := ha
  have hcb : Covers δ (↑(realScalarImage u A + A) : Set ℝ) ca := by
    simpa only [add_comm] using hca
  obtain ⟨k, centers, hc, hk⟩ := real_ruzsa_sum hδ A (realScalarImage u A) A ca ca hca hcb
  refine ⟨k, centers, ?_, ?_⟩
  · simpa only [realScalarImage_one] using hc
  · have hG := scaled_grid_card_lower hδ hu hu1 A hsep
    have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
    have hprod : (m : ℝ) * (m : ℝ) ≤ (K * (A.card : ℝ)) * (K * (A.card : ℝ)) :=
      mul_le_mul hm hm (Nat.cast_nonneg _) (by positivity)
    have hfirst : (k : ℝ) * (u * (A.card : ℝ)) ≤ 4 * ((k : ℝ) *
        ((realScalarImage u A).image (realGridIndex δ)).card) := by
      have hh := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg k)
      dsimp only [realScalarImage]
      convert hh using 1 <;> ring
    have hlast : ((k : ℝ) * u) * (A.card : ℝ) ≤
        (144 * K ^ 2 * (A.card : ℝ)) * (A.card : ℝ) := by nlinarith [hk, hprod]
    have hcancel := (mul_le_mul_iff_left₀ hAp).mp hlast
    have hdiv := (le_div_iff₀ hu).mpr hcancel
    convert hdiv using 1 <;> field_simp <;> ring

/-- A uniform bound used to close a family of initial scalars under the
sum of two products. -/
noncomputable def scalarAlgebraBound (c K : ℝ) : ℝ :=
  let B := 144 * K ^ 2 / c
  9 * (6 * (B + 144 * B ^ 2 / c + 144 * B ^ 2 / c)) ^ 3

theorem scalar_algebra_bound_pos {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    0 < scalarAlgebraBound c K := by unfold scalarAlgebraBound; positivity

theorem product_sum_scalar_cover_of_family (A S : Finset ℝ) {δ c q C σ K : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hc1 : c ≤ 1) (hK : 1 ≤ K)
    (hδq : δ ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (hA : A.Nonempty) (hS : S.Nonempty) (hAF : RealFiniteFrostman δ C σ A)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hSb : ∀ s ∈ S, c ≤ s ∧ s ≤ 1)
    (hsmall : ∀ s ∈ S, SmallScalarProjection δ A K s)
    (hbudget : 12 * scalarAlgebraBound c K * C * q ^ σ ≤ 1) :
    RealCoverBound δ (S * S + S * S)
      ((12 * scalarAlgebraBound c K / q) * (A.card : ℝ)) := by
  have hKp : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let B := 144 * K ^ 2 / c
  have hB : 0 < B := by dsimp [B]; positivity
  have hKB : K ≤ B := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  obtain ⟨u, hu⟩ := hS
  have hbase : SmallScalarProjection δ A B 1 := by
    have hh := (hsmall u hu).self_sum hδ (hc.trans_le (hSb u hu).1) (hSb u hu).2 hKp.le hA hsep
    exact hh.weaken (div_le_div_of_nonneg_left (by positivity) hc (hSb u hu).1)
  exact product_sum_scalar_cover A S hδ hc hB hδq hq1 hC hA hAF hsep hSb hbase
    (fun s hs => (hsmall s hs).weaken hKB) hbudget

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
