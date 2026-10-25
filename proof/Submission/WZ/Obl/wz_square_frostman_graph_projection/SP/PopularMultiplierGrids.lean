-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.PopularMultiplierGrids.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.FiniteFamilyEnergy
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.OrderedWeightedSelection
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GridCoverCard
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScaledGridCount

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise BigOperators

/-- A small product set gives many multipliers whose product grids have
large intersections with one fixed grid. The anchor dominates all the
selected multipliers, so their ratios lie in the unit interval. -/
theorem popular_multiplier_grids (A : Finset ℝ) {δ c K : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hK : 0 < K) (hA : A.Nonempty)
    (hAb : ∀ a ∈ A, c ≤ a ∧ a ≤ 1)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers δ (↑(A * A) : Set ℝ) cc)
    (hm : (m : ℝ) ≤ K * (A.card : ℝ)) :
    ∃ a₀ ∈ A, ∃ S : Finset ℝ, S ⊆ A ∧
      (c ^ 2 / (384 * K)) * (A.card : ℝ) ≤ (S.card : ℝ) ∧
      ∀ a ∈ S, a ≤ a₀ ∧ (c ^ 2 / (384 * K)) * (A.card : ℝ) ≤
        (((A.image (fun x => a₀ * x)).image (realGridIndex δ) ∩
          (A.image (fun x => a * x)).image (realGridIndex δ)).card : ℝ) := by
  classical
  letI : Nonempty A := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  let F (a : A) := (A.image (fun x => (a : ℝ) * x)).image (realGridIndex δ)
  let Z := (A * A).image (realGridIndex δ)
  have hsub (a : A) : F a ⊆ Z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨(a : ℝ) * b, Finset.mul_mem_mul a.2 hb, rfl⟩
  have hrow (a : A) : (c / 4) * (Fintype.card A : ℝ) ≤ ((F a).card : ℝ) := by
    have hh := scaled_grid_card_lower hδ (hc.trans_le (hAb a a.2).1) (hAb a a.2).2 A hsep
    have hm := mul_le_mul_of_nonneg_right (hAb a a.2).1 (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
    simp only [Fintype.card_coe]
    dsimp [F]
    nlinarith
  have hcap (a : A) : ((F a).card : ℝ) ≤ (Fintype.card A : ℝ) := by
    simp only [Fintype.card_coe]
    exact_mod_cast (Finset.card_image_le).trans (Finset.card_image_le (s := A))
  have hZ : (Z.card : ℝ) ≤ (6 * K) * (Fintype.card A : ℝ) := by
    have hh := grid_image_card_le_cover hδ (A * A) cc hcov
    simp only [Fintype.card_coe]
    dsimp [Z]
    nlinarith
  have he := finite_family_energy_lower F Z (by positivity : 0 ≤ c / 4)
    (by positivity : 0 < 6 * K) hsub hrow hZ
  let E := c ^ 2 / (96 * K)
  let w (a b : A) : ℝ := (F a ∩ F b).card
  have hE : 0 < E := by dsimp [E]; positivity
  have henergy : E * (Fintype.card A : ℝ) ^ 3 ≤ ∑ a : A, ∑ b : A, w a b := by
    convert he using 1 <;> dsimp [E, w] <;> field_simp <;> ring
  have hw (a b : A) : 0 ≤ w a b := Nat.cast_nonneg _
  have hsymm (a b : A) : w a b = w b a := by dsimp [w]; rw [Finset.inter_comm]
  have hbound (a b : A) : w a b ≤ (Fintype.card A : ℝ) :=
    (show w a b ≤ ((F a).card : ℝ) by dsimp [w]; exact_mod_cast Finset.card_le_card Finset.inter_subset_left).trans (hcap a)
  obtain ⟨a₀, T, hTcard, hT⟩ := ordered_weighted_selection (fun a : A => (a : ℝ)) w hE hw hsymm hbound henergy
  let S := T.image (fun a : A => (a : ℝ))
  have hSc : S.card = T.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hSA : S ⊆ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact b.2
  have hcoef : E / 4 = c ^ 2 / (384 * K) := by dsimp [E]; field_simp; ring
  simp only [Fintype.card_coe, hcoef] at hTcard hT
  refine ⟨a₀, a₀.2, S, hSA, ?_, ?_⟩
  · simpa only [hSc] using hTcard
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact hT b hb

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
