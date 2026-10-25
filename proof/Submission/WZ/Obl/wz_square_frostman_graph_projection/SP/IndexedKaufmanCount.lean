-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.IndexedKaufmanCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.FamilyGain
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.PowerBudget
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.RadialFrostman

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

theorem IndexedFrostman.mono_constant {I : Type*} [Fintype I] {f : I → Plane}
    {δ C D : ℝ} (hf : IndexedFrostman δ C f) (hδ : 0 ≤ δ) (hCD : C ≤ D) :
    IndexedFrostman δ D f := by
  intro x r hr
  exact (hf x r hr).trans (by gcongr; exact hδ.trans hr)

theorem indexed_kaufman_projection_count (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ C d : ℝ, 0 < δ → δ ≤ δ₀ → 1 ≤ C → 0 < d →
      ∀ (I : Type) [Fintype I] (f : I → Plane) (F : Finset Plane) (T : I → Finset Plane),
        ClosedFiniteFrostman δ C F → IndexedFrostman δ C f →
        (∀ i, ‖f i‖ = 1) → (∀ i, T i ⊆ F) → (∃ i, (T i).Nonempty) →
        d * (Fintype.card I : ℝ) * (F.card : ℝ) ≤ ∑ i, ((T i).card : ℝ) →
        ∃ i, ∀ (m : ℕ) (cc : Fin m → ℝ),
          Covers δ ((fun x => inner ℝ (f i) x) '' (↑(T i) : Set Plane)) cc →
            d ^ 2 * δ ^ (ε - 1) ≤ C ^ 2 * (m : ℝ) := by
  let γ : ℝ := 1 - min (ε / 2) (1 / 2)
  have hγ : 0 ≤ γ := by dsimp [γ]; linarith [min_le_right (ε / 2) (1 / 2 : ℝ)]
  have hγ1 : γ < 1 := by
    dsimp [γ]
    have hp : 0 < min (ε / 2) (1 / 2 : ℝ) := by positivity
    linarith
  have hslack : 0 < ε + γ - 1 := by dsimp [γ]; linarith [min_le_left (ε / 2) (1 / 2 : ℝ)]
  obtain ⟨δ₀, hδ₀, hδ₀1, hbudget⟩ :=
    exists_monomial_bound (8 * energyConstant γ) (a := ε + γ - 1) (b := 0) hslack
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ C d hδ hsmall hC hd I _ f F T hF hf hunit hT hne hden
  obtain ⟨i, hi⟩ := indexed_kaufman_energy_gain T hF hf hδ (hsmall.trans hδ₀1) hC hd
    hunit hγ hγ1 hT hne hden
  refine ⟨i, ?_⟩
  intro m cc hcov
  have hg := hi m cc hcov
  have hb : 8 * energyConstant γ * δ ^ (ε + γ - 1) ≤ 1 := by
    simpa only [Real.rpow_zero] using hbudget δ hδ hsmall
  calc d ^ 2 * δ ^ (ε - 1) ≤
      ((8 * C ^ 2 * energyConstant γ * δ ^ γ) * (m : ℝ)) * δ ^ (ε - 1) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
    _ = (C ^ 2 * (m : ℝ)) * (8 * energyConstant γ * δ ^ (ε + γ - 1)) := by
      rw [show ε + γ - 1 = γ + (ε - 1) by ring, Real.rpow_add hδ]
      ring
    _ ≤ (C ^ 2 * (m : ℝ)) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := mul_one _

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
