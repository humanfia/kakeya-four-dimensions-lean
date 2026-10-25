-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ProductFrostmanIteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ProductFrostmanImprovement
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PopularScalarFamily

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- A finite number of improvements can be made while reserving an
arbitrarily prescribed error in the final Frostman constant. -/
theorem product_frostman_iteration (ε β : ℝ) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ g : ℝ, 0 < g ∧ ∀ N : ℕ, β + (N : ℝ) * g ≤ 1 - ε + g →
      ∀ ν : ℝ, 0 < ν → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ A : Finset ℝ, (1 : ℝ) ∈ A → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
            RealFiniteFrostman δ (δ ^ (-η)) β A →
            (∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) →
            RealCoverBound δ (A * A + A * A) (δ ^ (-η) * (A.card : ℝ)) →
            RealFiniteFrostman δ (δ ^ (-ν)) (β + (N : ℝ) * g) A := by
  classical
  obtain ⟨g, hg, hg1, hstep⟩ := product_frostman_improvement ε β hε hβ
  refine ⟨g, hg, ?_⟩
  intro N
  induction N with
  | zero =>
      intro hN ν hν
      refine ⟨ν, 1, hν, by norm_num, le_rfl, ?_⟩
      intro δ hδ hδ1 A hA1 hAb hAF hsep hsmall
      simpa only [Nat.cast_zero, zero_mul, add_zero] using hAF
  | succ N ih =>
      intro hN ν hν
      obtain ⟨ηS, dS, hηS, hdS, hdS1, hboost⟩ := hstep ν hν
      have hprev : β + (N : ℝ) * g ≤ 1 - ε := by
        push_cast at hN
        nlinarith
      have hprev' : β + (N : ℝ) * g ≤ 1 - ε + g := by linarith
      obtain ⟨ηP, dP, hηP, hdP, hdP1, hprevboost⟩ := ih hprev' ηS hηS
      refine ⟨min ηS ηP, min dS dP, lt_min hηS hηP, lt_min hdS hdP,
        (min_le_left _ _).trans hdS1, ?_⟩
      intro δ hδ hδs A hA1 hAb hAF hsep hsmall
      have hδ1 : δ ≤ 1 := (hδs.trans (min_le_left _ _)).trans hdS1
      have herrorS : δ ^ (-(min ηS ηP)) ≤ δ ^ (-ηS) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [min_le_left ηS ηP])
      have herrorP : δ ^ (-(min ηS ηP)) ≤ δ ^ (-ηP) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [min_le_right ηS ηP])
      have hFprev := hprevboost δ hδ (hδs.trans (min_le_right _ _)) A hA1 hAb
        (hAF.weaken hδ herrorP) hsep
        (hsmall.mono Finset.Subset.rfl (mul_le_mul_of_nonneg_right herrorP (Nat.cast_nonneg _)))
      have hh := hboost δ (β + (N : ℝ) * g) hδ (hδs.trans (min_le_left _ _))
        (by have hh := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hg.le; linarith) hprev A hA1 hAb hFprev hsep
        (hsmall.mono Finset.Subset.rfl (mul_le_mul_of_nonneg_right herrorS (Nat.cast_nonneg _)))
      convert hh using 1 <;> push_cast <;> ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
