-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.AllScales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Estimates

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_endpoint_bootstrap

/-- The all-scales condition exactly as frozen in the dependency. -/
def AllScalesCover (δ η : ℝ) {n : ℕ} (x v : Fin n → Space) : Prop :=
  ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧
    ρ ≤ δ ^ (-η) * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space,
    (∀ j, ‖w j‖ = 1) ∧
    (∀ j j', j ≠ j' → volume (tube ρ (z j) (w j) ∩ tube ρ (z j') (w j')) ≤
      (1 / 2 : ENNReal) * volume (tube ρ (z j) (w j))) ∧
    (∀ i, ∃! j, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)) ∧
    (∀ j, ∃ i, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)) ∧
    (∀ j j', (Set.ncard {i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)} : ℝ) ≤
      δ ^ (-η) * (Set.ncard {i | tube δ (x i) (v i) ⊆ tube ρ (z j') (w j')} : ℝ)) ∧
    (∀ j, ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧
        tube δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤
      ENNReal.ofReal (δ ^ (-η) *
        (Set.ncard {i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)} : ℝ)) * volume W)

/-- The explicit all-scales volume premise of this obligation. -/
def AllScalesVolume : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ η x v Y → AllScalesCover δ η x v →
    ENNReal.ofReal (a * δ ^ ε) ≤ volume (⋃ i, Y i)

/-- The all-scales condition weakens as its allowed loss increases. -/
theorem AllScalesCover.mono {δ η η' : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η') (h : AllScalesCover δ η x v) :
    AllScalesCover δ η' x v := by
  have hpow : δ ^ (-η) ≤ δ ^ (-η') :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)
  intro ρ₀ hδρ hρ1
  obtain ⟨ρ, hρ₀ρ, hρ, hρbound, k, hk, z, w, hw, hdist, hpart, hsurj, hbal, hF⟩ :=
    h ρ₀ hδρ hρ1
  refine ⟨ρ, hρ₀ρ, hρ, hρbound.trans ?_, k, hk, z, w, hw, hdist, hpart, hsurj, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right hpow (hδ.le.trans hδρ)
  · intro j j'
    apply (hbal j j').trans
    exact mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
  · intro j W hW
    apply (hF j W hW).trans
    gcongr

end WangZahlLot.Obl.wz_restricted_uniform_improvement
