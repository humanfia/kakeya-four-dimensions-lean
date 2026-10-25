-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.CartesianScalarExpansion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ProductSumGrowth
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ScalarExpansionNumerics
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealFrostmanTruncation

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- A Cartesian product has a projection with a uniform power gain in any
normalized Frostman family of scalars of the same exponent. -/
theorem cartesian_scalar_expansion (ε : ℝ) (hε : 0 < ε) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 2 ≤ σ → σ ≤ 1 - ε →
        1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A S : Finset ℝ, A.Nonempty → S.Nonempty →
          (∀ s ∈ S, s ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C σ A → RealFiniteFrostman δ C σ S →
          (∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) →
          (A.card : ℝ) ≤ δ ^ (-σ - η) →
          ∃ t ∈ S, CoverLower δ
            ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(A ×ˢ A) : Set (ℝ × ℝ)))
            (δ ^ (-η) * (A.card : ℝ)) := by
  classical
  obtain ⟨ηS, g, rS, hηS, hg, hrS, hrS1, hexpand⟩ := product_sum_growth ε hε
  let κ := min (ηS / 2) (min (g / 10000) (1 / 10000))
  have hκ : 0 < κ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hκη : 2 * κ ≤ ηS := by have := min_le_left (ηS / 2) (min (g / 10000) (1 / 10000)); dsimp [κ]; linarith
  have hκg : 10000 * κ ≤ g := by
    have hh := (min_le_right (ηS / 2) (min (g / 10000) (1 / 10000))).trans (min_le_left _ _)
    dsimp [κ]
    linarith
  have hκ1 : κ ≤ 1 / 10000 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨dC, hdC, hdC1, hconstants⟩ := exists_power_bound 52488 hκ
  refine ⟨κ, min rS (min dC (1 / 2)), hκ, lt_min hrS (lt_min hdC (by norm_num)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (by norm_num)), ?_⟩
  intro δ σ C hδ hδs hσ hσmax hC hCb A S hAne hSne hS hAF hSF hsep hcard
  have hδr : δ ≤ rS := hδs.trans (min_le_left _ _)
  have hδC : δ ≤ dC := hδs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδhalf : δ ≤ 1 / 2 := hδs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by linarith
  have hδlt : δ < 1 := by linarith
  have hconst : 52488 ≤ δ ^ (-κ) := hconstants δ hδ hδC
  have hcut := scalar_cutoff_budget hδ hδ1 hκ hκ1 hσ hCb hconst
  obtain ⟨B, hBS, hBne, hBlow, hBcard, hBF⟩ :=
    hSF.trim_zero hδ (by linarith) hcut.1 hSne (fun s hs => (hS s hs).1) hcut.2.2
  have hBunit (s : ℝ) (hs : s ∈ B) : s ∈ Set.Icc (0 : ℝ) 1 := hS s (hBS hs)
  have h2C : 2 * C ≤ δ ^ (-ηS) := by
    calc
      2 * C ≤ δ ^ (-κ) * δ ^ (-κ) :=
        mul_le_mul ((by norm_num : (2 : ℝ) ≤ 52488).trans hconst) hCb (by linarith) (by positivity)
      _ = δ ^ (-2 * κ) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (-ηS) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hBlower := hexpand δ σ (2 * C) hδ hδr hσ hσmax (by linarith) h2C B hBne hBunit hBF
  by_contra hgood
  have hsmall (s : ℝ) (hs : s ∈ B) : SmallScalarProjection δ A (δ ^ (-κ)) s := by
    have hnot : ¬ CoverLower δ
        ((fun p : ℝ × ℝ => p.1 + s * p.2) '' (↑(A ×ˢ A) : Set (ℝ × ℝ)))
        (δ ^ (-κ) * (A.card : ℝ)) := fun h => hgood ⟨s, hBS hs, h⟩
    unfold CoverLower at hnot
    push_neg at hnot
    obtain ⟨m, cc, hc, hm⟩ := hnot
    refine ⟨m, cc, ?_, hm.le⟩
    intro x hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hc ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  let H := scalarAlgebraBound (δ ^ (100 * κ)) (δ ^ (-κ))
  have hH : 0 < H := scalar_algebra_bound_pos (by positivity) (by positivity)
  have hHb : H ≤ δ ^ (-1000 * κ) := scalar_algebra_power_bound hδ hδ1 hκ
    (by positivity) le_rfl hconst
  have hbudget := scalar_expansion_collision_budget hδ hδ1 hκ hκ1 hσ
    (by linarith) hH.le hCb hHb hconst
  have hK : 1 ≤ δ ^ (-κ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  obtain ⟨m, cc, hcov, hm⟩ := product_sum_scalar_cover_of_family A B hδ
    (by positivity : 0 < δ ^ (100 * κ)) hcut.2.1 hK hbudget.1 hbudget.2.1
    (by linarith) hAne hBne hAF hsep
    (fun s hs => ⟨hBlow s hs, (hBunit s hs).2⟩) hsmall hbudget.2.2
  have hcount : δ ^ (-σ - g) ≤ (m : ℝ) := hBlower m cc hcov
  have hupper : (m : ℝ) ≤ δ ^ (-σ - 5002 * κ) := hm.trans
    (scalar_expansion_cover_upper hδ hH.le (Nat.cast_nonneg _) hHb hcard hconst)
  have hstrict : δ ^ (-σ - 5002 * κ) < δ ^ (-σ - g) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδlt (by linarith)
  exact (not_le_of_gt hstrict) (hcount.trans hupper)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
