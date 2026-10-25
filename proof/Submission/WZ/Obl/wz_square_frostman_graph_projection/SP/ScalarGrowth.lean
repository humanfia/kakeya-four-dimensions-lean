-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarGrowth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarPacking
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.WeakProductGrowth

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
open scoped Pointwise

/-- A net covering both additive and product enlargements must grow. The
Frostman hypothesis on the original summand is enough; none is assumed
on the set being enlarged. -/
theorem scalar_enlargement_grows (ε β : ℝ) (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ η g δ₀ : ℝ, 0 < η ∧ 0 < g ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ α : ℝ, 0 < δ → δ ≤ δ₀ → 0 ≤ α → α ≤ 1 - ε →
        ∀ R S U : Finset ℝ, R.Nonempty → S.Nonempty →
          (∀ r ∈ R, r ∈ Set.Icc (0 : ℝ) 1) →
          (∀ a ∈ R, ∀ b ∈ R, a ≠ b → δ ≤ dist a b) →
          (R.card : ℝ) ≤ δ ^ (-α - η) →
          RealFiniteFrostman δ (δ ^ (-g)) β S →
          RealCoverBound (2 * δ) (R + S) (U.card : ℝ) →
          RealCoverBound (2 * δ) (R * R + R * R) (U.card : ℝ) →
          δ ^ (-g) * (R.card : ℝ) ≤ (U.card : ℝ) := by
  obtain ⟨η, r₀, hη, hr₀, hr₀1, hprod⟩ := weak_product_growth ε β hε hβ
  let g := η / 4
  have hg : 0 < g := by dsimp [g]; positivity
  obtain ⟨d, hd, hd1, hcut⟩ := exists_power_bound 144 hg
  refine ⟨η, g, min r₀ (min d (1 / 2)), hη, hg, by positivity,
    (min_le_right _ _).trans ((min_le_right _ _).trans (by norm_num)), ?_⟩
  intro δ α hδ hδs hα0 hα R S U hR hS hRb hRsep hRcard hSF hsum hmul
  have hδr : δ ≤ r₀ := hδs.trans (min_le_left _ _)
  have hδd : δ ≤ d := hδs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδlt : δ < 1 := lt_of_le_of_lt
    (hδs.trans ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num)
  have hδ1 : δ ≤ 1 := hδlt.le
  have hconst : 144 ≤ δ ^ (-g) := hcut δ hδ hδd
  have hp : 0 < δ ^ (-g) := Real.rpow_pos_of_pos hδ _
  by_contra hfail
  have hUc : (U.card : ℝ) ≤ δ ^ (-g) * (R.card : ℝ) := le_of_lt (lt_of_not_ge hfail)
  have hsum' : RealCoverBound (2 * δ) (R + S) (δ ^ (-g) * (R.card : ℝ)) :=
    hsum.mono Finset.Subset.rfl hUc
  have hRF := frostman_of_small_sum R S hδ hp hβ.le hβ1 hp.le hS hSF hRsep hsum'
  have hcoeff : 144 * δ ^ (-g) * δ ^ (-g) ≤ δ ^ (-η) := by
    calc
      _ ≤ δ ^ (-g) * δ ^ (-g) * δ ^ (-g) := by gcongr
      _ = δ ^ (-(3 * g)) := by rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by dsimp [g]; linarith)
  have hRF' : RealFiniteFrostman δ (δ ^ (-η)) β R := hRF.weaken hδ hcoeff
  have hC : 1 ≤ δ ^ (-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hlower := hprod δ β α (δ ^ (-η)) hδ hδr le_rfl hα0 hα hC le_rfl R hR hRb hRF' hRsep hRcard
  obtain ⟨m, cc, hc, hm⟩ := hmul
  obtain ⟨n, centers, hcov, hn⟩ := hc.refine_radius hδ (by linarith : δ ≤ 2 * δ)
  have hn' : (n : ℝ) ≤ 6 * (U.card : ℝ) := by
    have hid : 2 * δ / δ = 2 := by field_simp
    rw [hid] at hn
    nlinarith
  have hlow := hlower n centers hcov
  have hupper : (n : ℝ) ≤ δ ^ (-(2 * g)) * (R.card : ℝ) := by
    calc
      (n : ℝ) ≤ 6 * (U.card : ℝ) := hn'
      _ ≤ δ ^ (-g) * (δ ^ (-g) * (R.card : ℝ)) := by gcongr; linarith
      _ = _ := by rw [← mul_assoc, ← Real.rpow_add hδ]; congr 2; ring
  have hRc : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.mpr hR
  have hstrict : δ ^ (-(2 * g)) * (R.card : ℝ) < δ ^ (-η) * (R.card : ℝ) := by
    apply mul_lt_mul_of_pos_right _ hRc
    exact Real.rpow_lt_rpow_of_exponent_gt hδ hδlt (by dsimp [g]; linarith)
  exact (not_le_of_gt hstrict) (hlow.trans hupper)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
