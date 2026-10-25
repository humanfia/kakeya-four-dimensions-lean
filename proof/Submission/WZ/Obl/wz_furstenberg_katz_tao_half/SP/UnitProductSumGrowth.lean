-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.UnitProductSumGrowth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.DiscretizedRingGrowth
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealPlunnecke
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.GridFrostmanLower
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ProductSumContainment
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ProductSumNumerics

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- A sum of two products expands a nonconcentrated set containing one.
No separation assumption on `A` is required. -/
theorem unit_product_sum_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ η gain δ₀ : ℝ, 0 < η ∧ 0 < gain ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 2 ≤ σ → σ ≤ 1 - ε →
        1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A : Finset ℝ, (1 : ℝ) ∈ A → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C σ A →
          CoverLower δ (↑(A * A + A * A) : Set ℝ) (δ ^ (-σ - gain)) := by
  classical
  obtain ⟨ξ, gainR, r₀, hξ, hgainR, hr₀, hr₀1, hring⟩ := discretized_ring_growth ε hε
  let g := min gainR 1
  have hg : 0 < g := lt_min hgainR (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  let η := min (ξ / 2) (g / 100)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηξ : η ≤ ξ / 2 := min_le_left _ _
  have hηg : η ≤ g / 100 := min_le_right _ _
  obtain ⟨dC, hdC, hdC1, hbudgetC⟩ := exists_monomial_bound ((9 : ℝ) ^ ξ)
    (a := ξ - η) (b := 0) (by linarith)
  obtain ⟨dN, hdN, hdN1, hbudgetN⟩ := exists_monomial_bound 81 (a := g / 2) (b := 0) (by positivity)
  obtain ⟨dP, hdP, hdP1, hbudgetP⟩ := exists_monomial_bound ((6 : ℝ) ^ (9 : ℕ))
    (a := g / 4) (b := 0) (by positivity)
  refine ⟨η, g / 100, min (r₀ / 9) (min dC (min dN dP)), hη, by positivity,
    lt_min (by positivity) (lt_min hdC (lt_min hdN hdP)), ?_, ?_⟩
  · apply le_trans (min_le_left _ _)
    linarith
  intro δ σ C hδ hδs hσ hσmax hC hCb A hA1 hA hAF m cc hcov
  have hsR : δ ≤ r₀ / 9 := hδs.trans (min_le_left _ _)
  have hsC : δ ≤ dC := (hδs.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsN : δ ≤ dN := ((hδs.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsP : δ ≤ dP := ((hδs.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hρ : 0 < 9 * δ := by positivity
  have hρR : 9 * δ ≤ r₀ := by linarith
  have hρ1 : 9 * δ ≤ 1 := hρR.trans hr₀1
  have hδ1 : δ ≤ 1 := by linarith
  have hCρ : C ≤ (9 * δ) ^ (-ξ) := hCb.trans (scaled_error_budget hδ
    (by simpa only [Real.rpow_zero] using hbudgetC δ hδ hsC))
  have hAFρ : RealFiniteFrostman (9 * δ) C σ A := fun x r hr => hAF x r (by linarith)
  have hAne : A.Nonempty := ⟨1, hA1⟩
  have hBne : (A * A).Nonempty := hAne.mul hAne
  obtain ⟨n, centers, hcover, hPlun⟩ := real_plunnecke_nine hδ (A * A) hBne cc hcov
  have hcover' := hcover.mono_set (ring_expression_subset_nine_products A hA1)
  have hlong := hring (9 * δ) σ C hρ hρR hσ hσmax hC hCρ A hAne hA hAFρ n centers hcover'
  have hlong' : (9 * δ) ^ (-σ - g) ≤ (n : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by have := min_le_left gainR (1 : ℝ); dsimp [g]; linarith)).trans hlong
  have hn : δ ^ (-σ - g / 2) ≤ (n : ℝ) :=
    (nine_scale_power_lower hδ (by linarith) hg1
      (by simpa only [Real.rpow_zero] using hbudgetN δ hδ hsN)).trans hlong'
  have hAsub : A ⊆ A * A := by
    intro a ha
    simpa only [one_mul] using Finset.mul_mem_mul hA1 ha
  have hgrid : ((A.image (realGridIndex δ)).card : ℝ) ≤ ((A * A).image (realGridIndex δ)).card := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image hAsub)
  have hGcount : 1 ≤ (((A * A).image (realGridIndex δ)).card : ℝ) * C * δ ^ σ :=
    (hAF.grid_card_lower hδ hAne).trans (by gcongr)
  have hGlow := grid_power_lower hδ (Nat.cast_nonneg _) hCb hGcount
  exact ninth_power_growth hδ hδ1 hηg hg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hn hGlow hPlun (by simpa only [Real.rpow_zero] using hbudgetP δ hδ hsP)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
