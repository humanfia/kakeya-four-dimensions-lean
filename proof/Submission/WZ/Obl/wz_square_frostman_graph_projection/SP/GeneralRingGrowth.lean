-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GeneralRingGrowth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.LowRingGrowth
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.DiscretizedRingGrowth

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- Ring growth for every compact range of exponents inside `(0,1)`. -/
theorem general_discretized_ring_growth (ε β : ℝ) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ η gain δ₀ : ℝ, 0 < η ∧ 0 < gain ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ C : ℝ, 0 < δ → δ ≤ δ₀ → β ≤ σ → σ ≤ 1 - ε →
        1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A : Finset ℝ, A.Nonempty → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C σ A →
          CoverLower δ (↑(A + fourProductDifference A) : Set ℝ) (δ ^ (-σ - gain)) := by
  obtain ⟨ηL, gL, dL, hηL, hgL, hdL, hdL1, hlow⟩ := low_discretized_ring_growth β hβ
  obtain ⟨ηH, gH, dH, hηH, hgH, hdH, hdH1, hhigh⟩ := discretized_ring_growth ε hε
  refine ⟨min ηL ηH, min gL gH, min dL dH, lt_min hηL hηH, lt_min hgL hgH,
    lt_min hdL hdH, (min_le_left _ _).trans hdL1, ?_⟩
  intro δ σ C hδ hδs hσ hσmax hC hCb A hA hAb hAF m cc hc
  have hδ1 : δ ≤ 1 := (hδs.trans (min_le_left _ _)).trans hdL1
  by_cases hs : σ ≤ 1 / 2
  · have hCe : C ≤ δ ^ (-ηL) := hCb.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [min_le_left ηL ηH]))
    have hh := hlow δ σ C hδ (hδs.trans (min_le_left _ _)) hσ hs hC hCe A hA hAb hAF m cc hc
    exact (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [min_le_left gL gH])).trans hh
  · have hCe : C ≤ δ ^ (-ηH) := hCb.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [min_le_right ηL ηH]))
    have hh := hhigh δ σ C hδ (hδs.trans (min_le_right _ _)) (le_of_not_ge hs) hσmax hC hCe A hA hAb hAF m cc hc
    exact (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [min_le_right gL gH])).trans hh

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
