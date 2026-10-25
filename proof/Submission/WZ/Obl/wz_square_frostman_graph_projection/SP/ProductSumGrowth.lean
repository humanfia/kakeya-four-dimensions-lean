-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ProductSumGrowth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.UnitProductSumGrowth
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealNormalization
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ProductNormalizationNumerics

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- A sum of two products has a uniform power gain for a nonconcentrated
subset of the unit interval with exponent between one half and `1-ε`. -/
theorem product_sum_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ η gain δ₀ : ℝ, 0 < η ∧ 0 < gain ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 2 ≤ σ → σ ≤ 1 - ε →
        1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A : Finset ℝ, A.Nonempty → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C σ A →
          CoverLower δ (↑(A * A + A * A) : Set ℝ) (δ ^ (-σ - gain)) := by
  classical
  obtain ⟨ηU, gainU, rU, hηU, hgainU, hrU, hrU1, hunit⟩ := unit_product_sum_growth ε hε
  let g := min gainU 1
  have hg : 0 < g := lt_min hgainU (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  let κ := min (ηU / 100) (min (g / 1000) (1 / 10000))
  have hκ : 0 < κ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hκη : κ ≤ ηU / 100 := min_le_left _ _
  have hκg : κ ≤ g / 1000 := (min_le_right _ _).trans (min_le_left _ _)
  have hκ1 : κ ≤ 1 / 10000 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨dC, hdC, hdC1, hcut⟩ := exists_monomial_bound 128 (a := κ) (b := 0) hκ
  obtain ⟨dR, hdR, hdR1, hscale⟩ := exists_monomial_bound (1 / rU)
    (a := 1 - 200 * κ) (b := 0) (by linarith)
  refine ⟨κ, g / 2, min dC dR, hκ, by positivity, lt_min hdC hdR,
    (min_le_left _ _).trans hdC1, ?_⟩
  intro δ σ C hδ hδs hσ hσmax hC hCb A hAne hA hAF m cc hcov
  have hδ1 : δ ≤ 1 := (hδs.trans (min_le_left _ _)).trans hdC1
  have hsmall : 128 * δ ^ κ ≤ 1 := by
    simpa only [Real.rpow_zero] using hcut δ hδ (hδs.trans (min_le_left _ _))
  have hb := ring_scale_budget hδ hδ1 hκ hκ1 hσ hCb hsmall
  obtain ⟨c, hc, d, hd, hcd⟩ := hAF.exists_separated_pair hAne hb.1 hb.2.2
  let t := A.max' hAne
  have htA : t ∈ A := Finset.max'_mem A hAne
  have hmax (a : ℝ) (ha : a ∈ A) : a ≤ t := Finset.le_max' A a ha
  have hsize : δ ^ (100 * κ) ≤ t := hcd.trans (abs_le.mpr
    ⟨by linarith [(hA c hc).1, hmax d hd], by linarith [(hA d hd).1, hmax c hc]⟩)
  have ht : 0 < t := (Real.rpow_pos_of_pos hδ _).trans_le hsize
  have ht1 : t ≤ 1 := (hA t htA).2
  let B := A.image (fun a => a / t)
  have hB1 : (1 : ℝ) ∈ B := by
    exact Finset.mem_image.mpr ⟨t, htA, div_self ht.ne'⟩
  have hB (b : ℝ) (hb : b ∈ B) : b ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨div_nonneg (hA a ha).1 ht.le, (div_le_one ht).mpr (hmax a ha)⟩
  let ρ := δ / t ^ 2
  have hρ : 0 < ρ := div_pos hδ (by positivity)
  have hρbound : ρ ≤ δ ^ (1 - 200 * κ) := product_normalized_mesh_upper hδ ht hsize
  have hρU : ρ ≤ rU := by
    apply hρbound.trans
    have hh := hscale δ hδ (hδs.trans (min_le_right _ _))
    rw [Real.rpow_zero] at hh
    have hh' : δ ^ (1 - 200 * κ) / rU ≤ 1 := by convert hh using 1 <;> ring
    have hh'' := (div_le_iff₀ hrU).mp hh'
    simpa only [one_mul] using hh''
  have hρ1 : ρ ≤ 1 := hρU.trans hrU1
  have hscale' : δ ≤ t * ρ := by
    have hid : t * ρ = δ / t := by dsimp [ρ]; field_simp
    rw [hid]
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hBF : RealFiniteFrostman ρ C σ B := hAF.div_image hδ ht ht1 (by linarith) (by linarith) hscale'
  have hCρ : C ≤ ρ ^ (-ηU) := hCb.trans
    (product_normalized_error hδ hδ1 hρ hρbound hηU hκ1 hκη)
  have hcoverB := Covers.div_product_sum ht hcov
  have hcount := hunit ρ σ C hρ hρU hσ hσmax hC hCρ B hB1 hB hBF m _ hcoverB
  have hcount' : ρ ^ (-σ - g) ≤ (m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge hρ hρ1
      (by have := min_le_left gainU (1 : ℝ); dsimp [g]; linarith)).trans hcount
  exact (product_normalized_gain hδ hδ1 hρ hρbound hκ (by linarith) (by linarith)
    hg hg1 hκg).trans hcount'

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
