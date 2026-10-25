-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.StrongIteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.StrongBase
import Submission.WZ.Obl.wz_multiscale_finite_tower.Iteration
import Submission.WZ.Obl.wz_multiscale_finite_tower.Slack

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The strengthened finite-depth induction statement. -/
def StrongDepthProperty (σ ω : ℝ) (q : ℕ) : Prop :=
  ∀ ε D : ℝ, 0 < ε → 0 < D →
    ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ n x v Y,
      Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y →
      VolumeBound σ ω κ α d n Y ∨ (d ≤ D ∧
      ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M L : ℝ),
      Admissible d ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
      ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
      StrongTower d (d ^ (-ε)) (meshExponent ω q) (2 ^ q) m x' v')

lemma strong_depth_property_zero {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 ≤ ω) : StrongDepthProperty σ ω 0 := by
  intro ε D hε hD
  simpa only [meshExponent_zero, pow_zero] using strong_depth_zero hσ hσ1 hω ε D hε hD

lemma StrongDepthProperty.forget {σ ω : ℝ} {q : ℕ} (h : StrongDepthProperty σ ω q)
    (hω : ω ≤ 1) : DepthProperty σ ω q := by
  intro ε D hε hD
  obtain ⟨α, hα, κ, hκ, η, hη, hprop⟩ := h ε D hε hD
  refine ⟨α, hα, κ, hκ, η, hη, ?_⟩
  intro d hd hd100 n x v Y hA
  rcases hprop d hd hd100 n x v Y hA with hV | ⟨hdD, m, x', v', Y', M, L, hA', hU, hM, hT⟩
  · exact Or.inl hV
  · refine Or.inr ⟨hdD, m, x', v', Y', M, L, hA', hU, hM, ?_⟩
    exact hT.forget.mono hd (by linarith) le_rfl (meshExponent_le hω q) le_rfl

/-- Only the geometric successor theorem remains once the strengthened invariant is available. -/
theorem all_depths_of_strong_step {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hstep : ∀ q, StrongDepthProperty σ ω q → StrongDepthProperty σ ω (q + 1)) :
    ∀ q, DepthProperty σ ω q := by
  have h : ∀ q, StrongDepthProperty σ ω q :=
    Nat.rec (strong_depth_property_zero hσ hσ1 hω) hstep
  exact fun q => (h q).forget hω1

end WangZahlLot.Obl.wz_multiscale_finite_tower
