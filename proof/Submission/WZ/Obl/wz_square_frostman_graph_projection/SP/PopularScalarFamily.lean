-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.PopularScalarFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PopularMultiplierGrids
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GridIntersectionSum

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

theorem RealFiniteFrostman.weaken {δ C D σ : ℝ} {A : Finset ℝ}
    (h : RealFiniteFrostman δ C σ A) (hδ : 0 < δ) (hCD : C ≤ D) :
    RealFiniteFrostman δ D σ A := by
  intro x r hr
  have hrp : 0 < r := hδ.trans_le hr
  exact (h x r hr).trans (by gcongr)

/-- Small sum and product covers produce a nonconcentrated family of
small-projection scalars. -/
theorem popular_scalar_family (A : Finset ℝ) {δ c K C σ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hK : 0 < K) (hC : 1 ≤ C) (hA : A.Nonempty)
    (hAb : ∀ a ∈ A, c ≤ a ∧ a ≤ 1)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hAF : RealFiniteFrostman δ C σ A)
    (hAdd : RealCoverBound δ (A + A) (K * (A.card : ℝ)))
    (hMul : RealCoverBound δ (A * A) (K * (A.card : ℝ))) :
    let d := c ^ 2 / (384 * K)
    0 < d ∧ d ≤ 1 ∧ 1 ≤ C / d ∧ RealFiniteFrostman δ (C / d) σ A ∧
      ∃ S : Finset ℝ, S.Nonempty ∧ (∀ s ∈ S, c ≤ s ∧ s ≤ 1) ∧
        RealFiniteFrostman δ (C / d) σ S ∧
        ∀ s ∈ S, SmallScalarProjection δ A (108 * K ^ 2 / (c * d)) s := by
  classical
  dsimp only
  let d := c ^ 2 / (384 * K)
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨m, cc, hcov, hm⟩ := hMul
  obtain ⟨a₀, ha₀, T, hTA, hTcard, hT⟩ := popular_multiplier_grids A hδ hc hK hA hAb hsep cc hcov hm
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hTc : (T.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hTA
  have hd1 : d ≤ 1 := by dsimp [d]; nlinarith
  have hTne : T.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < T.card := (mul_pos hd hAp).trans_le hTcard
    exact_mod_cast hh
  have ha₀p : 0 < a₀ := hc.trans_le (hAb a₀ ha₀).1
  have ha₀1 : a₀ ≤ 1 := (hAb a₀ ha₀).2
  have hCD : C ≤ C / d := (le_div_iff₀ hd).mpr (by nlinarith)
  have hD : 1 ≤ C / d := hC.trans hCD
  have hTF : RealFiniteFrostman δ (C / d) σ T := hAF.subset hδ (by linarith) hd hTA hTcard
  let S := T.image (fun a => a / a₀)
  have hS (s : ℝ) (hs : s ∈ S) : c ≤ s ∧ s ≤ 1 := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    have hab := hAb a (hTA ha)
    constructor
    · apply (le_div_iff₀ ha₀p).mpr
      nlinarith
    · exact (div_le_one ha₀p).mpr (hT a ha).1
  refine ⟨hd, hd1, hD, hAF.weaken hδ hCD, S, hTne.image _, hS,
    hTF.div_image_same_scale hδ ha₀p ha₀1, ?_⟩
  intro s hs
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
  have hab := hAb a (hTA ha)
  exact common_multiplier_small_projection A hδ hc (hAb a₀ ha₀).1 ha₀1
    (hc.le.trans hab.1) hab.2 hd hK.le hA hAdd (hT a ha).2

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
