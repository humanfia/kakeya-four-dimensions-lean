-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_c2_regularization.Glue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_c2_regularization.BoundedSlope

/-!
# Glue helpers for `WangZahlLot.wz_grains_c2_regularization`

The frozen premise `L σ` and the premise of `wz_multiscale_c2_extraction` (the same examples
with the slope bounded by three on `[-1, 1]`), written with named conditions whose bodies
unfold to the frozen ones. The only mathematical step is the proved isometry of
`BoundedSlope.lean`.
-/

namespace WangZahlLot.Obl.wz_grains_c2_regularization

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_separated_cover_refinement (Dense Strong Tube Dilate)
open scoped ENNReal

/-- The separated all-scale covers `S` of the frozen statement, with its conjunctions
associated as there (`Strong` groups the first six of them). -/
def StrongF (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ ρ : ℝ, r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧
    ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space,
      (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
        (1 / 2 : ENNReal) * volume (Tube ρ (z j) (w j))) ∧
      (∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j, ∃ i, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j j', (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ) ≤
        δ ^ (-η) * (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j') (w j')} : ℝ)) ∧
      (∀ j, ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) ∧
          Tube δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) *
          (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ)) * volume W) ∧
      (∀ i j j', Tube δ (x i) (v i) ⊆ Dilate ρ (z j) (w j) →
        Tube δ (x i) (v i) ⊆ Dilate ρ (z j') (w j') → j = j')

theorem strong_of_strongF {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : StrongF η δ n x v) : Strong η δ n x v := by
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, h1, h2, h3, h4, h5, h6, h7⟩ := h r hδr hr1
  exact ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩

theorem strongF_of_strong {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Strong η δ n x v) : StrongF η δ n x v := by
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := h r hδr hr1
  exact ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, h1, h2, h3, h4, h5, h6, h7⟩

/-- The frozen premise `L σ`: Lipschitz global-grains examples. -/
def LipschitzExamplesF (σ : ℝ) : Prop :=
  ∀ η d₀ : ℝ, 0 < η → 0 < d₀ → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d₀ ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Dense η δ n x v Y ∧ StrongF η δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
      ∃ (f : ℝ → ℝ) (P : Space → Space), LipschitzWith 1 f ∧ Grains σ δ (δ ^ (-η)) v Y f P

/-- The premise of `wz_multiscale_c2_extraction`: the same examples with `|f| ≤ 3` on
`[-1, 1]`. -/
def BoundedLipschitzExamplesF (σ : ℝ) : Prop :=
  ∀ η d₀ : ℝ, 0 < η → 0 < d₀ → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d₀ ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Dense η δ n x v Y ∧ StrongF η δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
      ∃ (f : ℝ → ℝ) (P : Space → Space),
        (LipschitzWith 1 f ∧ ∀ z : ℝ, z ∈ Icc (-1) 1 → |f z| ≤ 3) ∧
          Grains σ δ (δ ^ (-η)) v Y f P

/-- Step 0 of the proof: an isometry bounds the slope by three (`BoundedSlope.lean`). -/
theorem bounded_examples {σ : ℝ} (h : LipschitzExamplesF σ) : BoundedLipschitzExamplesF σ := by
  intro η d₀ hη hd₀
  obtain ⟨δ, hδ, hδd, hδmax, n, x, v, Y, hD, hS, hC, hV, f, P, hf, hG⟩ := h η d₀ hη hd₀
  obtain ⟨e, g, hg, hgb, ⟨hD', hS', hC', hV'⟩, hG'⟩ :=
    bounded_slope_representative hδ ⟨hD, strong_of_strongF hS, hC, hV⟩ hf hG
  exact ⟨δ, hδ, hδd, hδmax, n, _, _, _, hD', strongF_of_strong hS', hC', hV', g, _,
    ⟨hg, hgb⟩, hG'⟩

end WangZahlLot.Obl.wz_grains_c2_regularization
