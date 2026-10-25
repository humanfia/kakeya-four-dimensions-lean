-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ProductFrostmanImprovement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GeneralProductSumGrowth
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.LocalSumPacking
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ProductTripleCover
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ProductFrostmanNumerics

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- If a separated set containing one has small product doubling, its
Frostman exponent improves. Coarse-scale product growth supplies the
packing estimates at each scale. -/
theorem product_frostman_improvement (ε β : ℝ) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧ ∀ ν : ℝ, 0 < ν →
      ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
        ∀ δ σ : ℝ, 0 < δ → δ ≤ δ₀ → β ≤ σ → σ ≤ 1 - ε →
          ∀ A : Finset ℝ, (1 : ℝ) ∈ A → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
            RealFiniteFrostman δ (δ ^ (-η)) σ A →
            (∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) →
            RealCoverBound δ (A * A + A * A) (δ ^ (-η) * (A.card : ℝ)) →
            RealFiniteFrostman δ (δ ^ (-ν)) (σ + g) A := by
  classical
  obtain ⟨ηS, gS, rS, hηS, hgS, hrS, hrS1, hprod⟩ := general_product_sum_growth ε β hε hβ
  let g := min gS 1
  have hg : 0 < g := lt_min hgS (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgg : g ≤ gS := min_le_left _ _
  refine ⟨g, hg, hg1, ?_⟩
  intro ν hν
  let p := min ν 1 / 10
  let η := min (ν / 100) (p * ηS / 2)
  have hp : 0 < p := by dsimp [p]; exact div_pos (lt_min hν (by norm_num)) (by norm_num)
  have hpν : p ≤ ν / 10 := by dsimp [p]; linarith [min_le_left ν (1 : ℝ)]
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hην : η ≤ ν / 100 := min_le_left _ _
  have hηp : η ≤ p * ηS / 2 := min_le_right _ _
  obtain ⟨dC, hdC, hdC1, hcut⟩ := exists_power_bound 248832 hη
  obtain ⟨dR, hdR, hdR1, hscale⟩ := exists_monomial_bound (1 / rS) (a := p) (b := 0) hp
  refine ⟨η, min dC dR, hη, lt_min hdC hdR, (min_le_left _ _).trans hdC1, ?_⟩
  intro δ σ hδ hδs hσ hσmax A hA1 hAb hAF hsep hsmall
  have hδ1 : δ ≤ 1 := (hδs.trans (min_le_left _ _)).trans hdC1
  have hconst := hcut δ hδ (hδs.trans (min_le_left _ _))
  have hC : 1 ≤ δ ^ (-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hAne : A.Nonempty := ⟨1, hA1⟩
  have hsig : 0 ≤ σ + g := by linarith
  have hsig2 : σ + g ≤ 2 := by linarith
  obtain ⟨n, centers, hc, hn⟩ := product_triple_cover hδ (Real.rpow_nonneg hδ.le _) A hA1 hsep hsmall
  intro x r hδr
  have hr : 0 < r := hδ.trans_le hδr
  by_cases hsmallr : 8 * r ≤ δ ^ p
  · have hρ : 0 < 8 * r := by positivity
    have hρS : 8 * r ≤ rS := by
      apply hsmallr.trans
      have hh := hscale δ hδ (hδs.trans (min_le_right _ _))
      rw [Real.rpow_zero] at hh
      have hh' : δ ^ p / rS ≤ 1 := by convert hh using 1 <;> ring
      have hh'' := (div_le_iff₀ hrS).mp hh'
      simpa only [one_mul] using hh''
    have hρ1 : 8 * r ≤ 1 := hρS.trans hrS1
    have hCF : δ ^ (-η) ≤ (8 * r) ^ (-ηS) := by
      calc
        δ ^ (-η) ≤ δ ^ (p * (-ηS)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
        _ = (δ ^ p) ^ (-ηS) := Real.rpow_mul hδ.le _ _
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos hρ hsmallr (by linarith)
    have hAFρ : RealFiniteFrostman (8 * r) (δ ^ (-η)) σ A := fun y s hs => hAF y s (by linarith)
    have hgrowth := hprod (8 * r) σ (δ ^ (-η)) hρ hρS hσ hσmax hC hCF A hAne hAb hAFρ
    have hgrowth' : CoverLower (8 * r) (↑(A * A + A * A) : Set ℝ) ((8 * r) ^ (-(σ + g))) := by
      intro m cc hcov
      have hh := hgrowth m cc hcov
      exact (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)).trans hh
    have hlocal := local_sum_packing_power (x := x) hδ hδr A (A * A + A * A) hsep hgrowth' centers hc
    have hbudget := product_frostman_small_budget (ν := ν) (s := σ + g) hδ hδ1 (by linarith) hsig2 hconst
    calc
      ((A.filter (fun a => dist a x ≤ r)).card : ℝ) ≤ 18 * (n : ℝ) * (8 * r) ^ (σ + g) := hlocal
      _ ≤ 18 * (216 * (δ ^ (-η)) ^ 3 * (A.card : ℝ)) * (8 * r) ^ (σ + g) := by gcongr
      _ = (18 * 216 * (δ ^ (-η)) ^ 3 * (8 : ℝ) ^ (σ + g)) * r ^ (σ + g) * (A.card : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hr.le]; ring
      _ ≤ _ := by gcongr
  · have hlarge : δ ^ p / 8 ≤ r := by linarith
    have hbudget := product_frostman_large_budget hδ hδ1 hp hpν hην hsig hsig2 hlarge hconst
    have hcA : ((A.filter (fun a => dist a x ≤ r)).card : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le A _
    exact hcA.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card))

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
