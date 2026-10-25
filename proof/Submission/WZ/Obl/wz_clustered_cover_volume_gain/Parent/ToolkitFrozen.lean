-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.ToolkitFrozen.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorFrozen
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.ConvexSlab
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.ConvexBox
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CordobaSlab

/-!
# A frozen-ready convex-geometry toolkit for WZ §§4–9, with its proof

`toolkitFrozen` (3146 characters, only Mathlib and `ChallengeDeps` names, checked standalone with
`autoImplicit` off) is the conjunction of
1. WZ Proposition 4.6 (factoring convex sets) for unit `ρ`-tubes in `ball 0 R` (`factorFrozen`);
2. WZ Lemma 4.9: a convex body with a `τ`-share of its volume in a slab of half-width `s` lies in the
   concentric slab of half-width `48 s / τ` (`ConvexSlab.subset_slab`);
3. every convex body `ball p r ⊆ W ⊆ ball 0 R` lies in a box `P a b c p e`, `0 < a ≤ b ≤ c`, with
   `a b c ≤ 1728 vol W` (`Factor.box_approx_general`; a substitute for John's ellipsoid);
4. WZ Lemma 5.7: for `δ × 1 × 1` slabs `P δ 1 1 (z j) (e j)` with Katz–Tao constant `m` and
   `l`-dense measurable shadings, `l² δ #F ≤ 3456 (⌊log₂(1/δ)⌋₊ + 2) m vol(⋃ Y_j)`
   (`Factor.cordoba_slabs`).
It binds the tube `T` and the box `P` by defining equations, as the other frozen types of o019.
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- The convex-geometry toolkit. -/
def toolkitFrozen : Prop :=
  ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ P, P = (fun (a b c : ℝ) (z : LeanEval.Analysis.WangZahlKakeya.Space) (e : LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space) => {p : LeanEval.Analysis.WangZahlKakeya.Space | |e (p - z) 0| ≤ a / 2 ∧ |e (p - z) 1| ≤ b / 2 ∧ |e (p - z) 2| ≤ c / 2}) → (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space), 0 < N → (∀ k, ‖w k‖ = 1) → (∀ k, T ρ (y k) (w k) ⊆ Metric.ball 0 R) → ∃ (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → LeanEval.Analysis.WangZahlKakeya.Space) (e : Fin L → LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space), (N : ℝ) ≤ C * ((N : ℝ) / ρ) ^ ε * U.card ∧ 0 < m ∧ ρ ≤ a ∧ a ≤ b ∧ b ≤ 2 * R ∧ (∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) ∧ (∀ i, m * (a * b * (2 * R)) ≤ C * ((N : ℝ) / ρ) ^ ε * (Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i)} * ρ ^ 2)) ∧ (∀ k ∈ U, 1 ≤ Set.ncard {i | T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i)} ∧ (Set.ncard {i | T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i)} : ℝ) ≤ C * ((N : ℝ) / ρ) ^ ε) ∧ (∀ V, Convex ℝ V → ENNReal.ofReal (Set.ncard {i | P a b (2 * R) (z i) (e i) ⊆ V} * (a * b * (2 * R))) ≤ ENNReal.ofReal (C * ((N : ℝ) / ρ) ^ ε) * MeasureTheory.volume V) ∧ ∀ i V, Convex ℝ V → ENNReal.ofReal (Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i) ∩ V} * (a * b * (2 * R))) ≤ ENNReal.ofReal (C * ((N : ℝ) / ρ) ^ ε * Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i)}) * MeasureTheory.volume V) ∧ (∀ (U : Set LeanEval.Analysis.WangZahlKakeya.Space) (ν : LeanEval.Analysis.WangZahlKakeya.Space) (t₀ s τ : ℝ), Convex ℝ U → 0 < MeasureTheory.volume U → MeasureTheory.volume U ≠ ⊤ → 0 < s → 0 < τ → ENNReal.ofReal τ * MeasureTheory.volume U ≤ MeasureTheory.volume (U ∩ {p | |inner ℝ ν p - t₀| ≤ s}) → U ⊆ {p | |inner ℝ ν p - t₀| ≤ 48 * s / τ}) ∧ (∀ (W : Set LeanEval.Analysis.WangZahlKakeya.Space) (p : LeanEval.Analysis.WangZahlKakeya.Space) (r R : ℝ), Convex ℝ W → 0 < r → Metric.ball p r ⊆ W → W ⊆ Metric.ball 0 R → ∃ (a b c : ℝ) (e : LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space), 0 < a ∧ a ≤ b ∧ b ≤ c ∧ W ⊆ P a b c p e ∧ ENNReal.ofReal (a * b * c) ≤ 1728 * MeasureTheory.volume W) ∧ (∀ (n : ℕ) (F : Finset (Fin n)) (δ m l : ℝ) (z : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (e : Fin n → LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < δ → δ ≤ 1 → 0 < m → 0 ≤ l → (∀ j ∈ F, MeasurableSet (Y j) ∧ Y j ⊆ P δ 1 1 (z j) (e j) ∧ ENNReal.ofReal (l * δ) ≤ MeasureTheory.volume (Y j)) → (∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {j | j ∈ F ∧ P δ 1 1 (z j) (e j) ⊆ W} * δ) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → l ^ 2 * δ * F.card ≤ 3456 * ((⌊Real.logb 2 (1 / δ)⌋₊ : ℝ) + 2) * m * (MeasureTheory.volume (⋃ j ∈ F, Y j)).toReal)

theorem toolkit_frozen : toolkitFrozen := by
  intro T hT P hP
  refine ⟨factor_frozen T hT P hP, ?_, ?_, ?_⟩
  · intro U ν t₀ s τ hU hpos hfin hs hτ hconc
    exact ConvexSlab.subset_slab hU hpos hfin hs hτ hconc
  · intro W p r R hW hr hball hWb
    subst hP
    exact box_approx_general hW hr hball hWb
  · intro n F δ m l z e Y hδ hδ1 hm hl hY hKT
    subst hP
    classical
    have hKT' : ∀ W, Convex ℝ W → ENNReal.ofReal
        ((F.filter fun j => box δ 1 1 (z j) (e j) ⊆ W).card * δ) ≤
          ENNReal.ofReal m * volume W := by
      intro W hW
      have h := hKT W hW
      change ENNReal.ofReal ((Set.ncard {j | j ∈ F ∧ box δ 1 1 (z j) (e j) ⊆ W} : ℝ) * δ) ≤
        ENNReal.ofReal m * volume W at h
      have hcard : Set.ncard {j | j ∈ F ∧ box δ 1 1 (z j) (e j) ⊆ W} =
          (F.filter fun j => box δ 1 1 (z j) (e j) ⊆ W).card := by
        rw [← Set.ncard_coe_finset, Finset.coe_filter]
      rw [hcard] at h
      exact h
    exact cordoba_slabs F hδ hδ1 hm hl z e Y hY hKT'

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor
