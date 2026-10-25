-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.LevelTwo.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PrismCompact
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PlanarGeometry
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file LevelTwo.lean), namespace renamed.

/-!
# Level ii: the estimate `F` for the prisms themselves

`level_two`: `PrismFrostmanEstimate σ ω` (through `prism_frostman_all_scales`) applied with
`s = a`, `t = b` to prisms `prism a b (c j) (e₁ j) (e₂ j) (e₃ j)` meeting `ball 0 1`. The shape
hypotheses of the estimate (convexity, measurability, the two boxes, `ball 0 10`) hold for every
such prism; pairwise half-overlap, the Frostman count and the quadratic container count are
kept as hypotheses on the prism family.
-/

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

lemma prism_subset_ball_ten {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1) {c e₁ e₂ e₃ : Space}
    (he : Orthonormal ℝ ![e₁, e₂, e₃]) (hmeet : (prism a b c e₁ e₂ e₃ ∩ ball 0 1).Nonempty) :
    prism a b c e₁ e₂ e₃ ⊆ ball 0 10 := by
  obtain ⟨x, hxP, hxB⟩ := hmeet
  intro y hy
  rw [mem_ball_zero_iff] at hxB ⊢
  have h1 := prism_norm_sub_le hab hb he hy
  have h2 := prism_norm_sub_le hab hb he hxP
  calc ‖y‖ = ‖(y - c) - (x - c) + x‖ := by congr 1; abel
    _ ≤ ‖y - c‖ + ‖x - c‖ + ‖x‖ := (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ < 10 := by linarith

lemma prism_inner_box {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c e₁ e₂ e₃ : Space) :
    {y | |inner ℝ e₁ (y - c)| ≤ a / 10 ∧ |inner ℝ e₂ (y - c)| ≤ b / 10 ∧
      |inner ℝ e₃ (y - c)| ≤ (1 / 10 : ℝ)} ⊆ prism a b c e₁ e₂ e₃ := by
  rintro y ⟨h1, h2, h3⟩
  exact ⟨h1.trans (by linarith), h2.trans (by linarith), h3.trans (by norm_num)⟩

lemma prism_outer_box {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c e₁ e₂ e₃ : Space) :
    prism a b c e₁ e₂ e₃ ⊆ {y | |inner ℝ e₁ (y - c)| ≤ 10 * a ∧
      |inner ℝ e₂ (y - c)| ≤ 10 * b ∧ |inner ℝ e₃ (y - c)| ≤ (10 : ℝ)} := by
  rintro y ⟨h1, h2, h3⟩
  exact ⟨h1.trans (by linarith), h2.trans (by linarith), h3.trans (by norm_num)⟩

/-- Level ii: `PrismFrostmanEstimate` for a family of `a × b × 1` prisms meeting `ball 0 1`. -/
theorem level_two {σ ω : ℝ} (hσ : 0 ≤ σ) (hω : 0 ≤ ω) (hF : PrismFrostmanEstimate σ ω)
    {e : ℝ} (he : 0 < e) :
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1 →
    ∀ (q : ℕ) (c e₁ e₂ e₃ : Fin q → Space) (Z : Fin q → Set Space),
    0 < q → (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) →
    (∀ j, (prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩ ball 0 1).Nonempty) →
    (∀ j k, j ≠ k → volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩
        prism a b (c k) (e₁ k) (e₂ k) (e₃ k)) ≤
      (1 / 2 : ENNReal) * volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j))) →
    (∀ j, MeasurableSet (Z j)) → (∀ j, Z j ⊆ prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
    ENNReal.ofReal (a ^ η * q * a * b) ≤ ∑ j, volume (Z j) →
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {j | prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ U}) ≤
        ENNReal.ofReal (a ^ (-η) * q) * volume U) →
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {j | prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ U}) *
          ENNReal.ofReal ((a * b) ^ 2) ≤
        ENNReal.ofReal (a ^ (-η)) * (volume U) ^ 2) →
    ENNReal.ofReal (A * a ^ e * b ^ ω * (q * (a * b) ^ 2) ^ (σ / 2)) ≤
      volume (⋃ j, Z j) := by
  obtain ⟨A, hA, η, hη, hest⟩ := prism_frostman_all_scales hσ hω hF e he
  refine ⟨A, hA, η, hη, ?_⟩
  intro a b ha hab hb1 q c e₁ e₂ e₃ Z hq hframe hmeet hover hZm hZP hmass hfrost hquad
  exact hest a b ha hab hb1 q (fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) Z c e₁ e₂ e₃ hq
    hframe (fun j => prism_convex a b (c j) (e₁ j) (e₂ j) (e₃ j))
    (fun j => (prism_isClosed a b (c j) (e₁ j) (e₂ j) (e₃ j)).measurableSet)
    (fun j => prism_inner_box ha.le (ha.le.trans hab) (c j) (e₁ j) (e₂ j) (e₃ j))
    (fun j => prism_outer_box ha.le (ha.le.trans hab) (c j) (e₁ j) (e₂ j) (e₃ j))
    (fun j => prism_subset_ball_ten hab hb1 (hframe j) (hmeet j)) hover hZm hZP hmass
    hfrost hquad

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
