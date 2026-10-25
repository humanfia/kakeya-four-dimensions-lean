-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_estimate_equivalence.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_estimate_equivalence.Reverse
import Submission.WZ.Obl.wz_estimate_equivalence.Descent
import Submission.WZ.Obl.wz_estimate_equivalence.Restricted
import Submission.WZ.Obl.wz_frostman_all_scales_volume
import Submission.WZ.Obl.wz_small_slab_error_removal
import Submission.WZ.Obl.wz_restricted_uniform_improvement
import Submission.WZ.Obl.wz_estimate_equivalence.Starting
import Submission.WZ.Obl.wz_estimate_equivalence.Endpoints

namespace WangZahlLot.Obl.wz_estimate_equivalence

/-- Iterate the restricted improvement, removing the slab restriction at each step. -/
theorem forward_positive {σ ω : ℝ} (hσ : 0 < σ) (hσmax : σ ≤ (1 / 2 : ℝ))
    (hω : 0 < ω) (hD : D σ ω) : E σ ω := by
  apply e_of_uniform_descent (e_starting hσ.le hσmax)
  intro t ht
  obtain ⟨α, hα, hαt, hstep⟩ :=
    WangZahlLot.wz_restricted_uniform_improvement σ ω t
      WangZahlLot.wz_frostman_all_scales_volume hσ hσmax hω ht
  refine ⟨α, hα, ?_⟩
  intro ω' hω' hE
  exact WangZahlLot.wz_small_slab_error_removal σ (ω' - α) hσ hσmax
    (by linarith) (hstep ω' hω' hD hE)

end WangZahlLot.Obl.wz_estimate_equivalence

theorem WangZahlLot.wz_estimate_equivalence : ∀ σ ω : ℝ, 0 ≤ σ → σ ≤ (1 / 2 : ℝ) → 0 ≤ ω → ((∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})} : ℕ) : ℝ)) ≤ ENNReal.ofReal ((δ ^ (-η)) * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (a * δ ^ ((ω) + ε) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-((σ) : ℝ))) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)) ↔ (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (m) * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})} : ℕ) : ℝ)) ≤ ENNReal.ofReal ((l) * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (a * δ ^ ((ω) + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) * (m ^ (- (3 / 2 : ℝ)) * l * ((n : ℝ) * δ)) ^ (-((σ) : ℝ))) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i))) := by
  intro σ ω hσ hσmax hω
  change WangZahlLot.Obl.wz_estimate_equivalence.D σ ω ↔
    WangZahlLot.Obl.wz_estimate_equivalence.E σ ω
  constructor
  · exact WangZahlLot.Obl.wz_estimate_equivalence.e_of_d_of_positive_implication
      (fun _ _ hs hsmax hw =>
        WangZahlLot.Obl.wz_estimate_equivalence.forward_positive hs hsmax hw)
      σ ω hσ hσmax hω
  · exact WangZahlLot.Obl.wz_estimate_equivalence.d_of_e hσ
