-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.Bridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_restricted_uniform_improvement.AllScales
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Uniform

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement

open WangZahlLot.Obl.wz_endpoint_bootstrap

/-- Only pointwise geometric improvement remains after the order-theoretic
uniformization. Its constants and decrement may depend on the current exponent. -/
def PointwiseImprovement : Prop :=
  ∀ σ ω u : ℝ, AllScalesVolume → 0 < σ → σ ≤ 1 / 2 → 0 < ω → ω < u →
    Estimate σ ω → Full σ u → ∃ g : ℝ, 0 < g ∧ Restricted σ (u - g)

theorem uniform_of_pointwise (hpoint : PointwiseImprovement) :
    ∀ σ ω t : ℝ, AllScalesVolume → 0 < σ → σ ≤ 1 / 2 → 0 < ω → 0 < t →
      ∃ α : ℝ, 0 < α ∧ α ≤ t / 2 ∧ ∀ u : ℝ, ω + t ≤ u →
        Estimate σ ω → Full σ u → Restricted σ (u - α) := by
  intro σ ω t hA hσ hσ1 hω ht
  classical
  by_cases hD : Estimate σ ω
  · obtain ⟨α, hα, hαt, h⟩ := uniform_improvement_of_pointwise
      (fun u hu hE => hpoint σ ω u hA hσ hσ1 hω hu hD hE) t ht
    exact ⟨α, hα, hαt, fun u hu _ hE => h u hu hE⟩
  · exact ⟨t / 2, by positivity, le_rfl, fun _ _ hD' _ => (hD hD').elim⟩

/-- The exact frozen proposition follows from the pointwise geometric statement.
This bridge also checks that the readable estimates have exactly the required normalization. -/
theorem frozen_of_pointwise (hpoint : PointwiseImprovement) : ∀ σ ω t : ℝ, (fun (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop → Prop) => (fun (J : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop) => (fun (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) => (fun (d : ℝ → ℝ → Prop) => (fun (e : ℝ → ℝ → Prop) => (fun (r : ℝ → ℝ → Prop) => (fun (A : Prop) => A → 0 < σ → σ ≤ (1/2 : ℝ) → 0 < ω → 0 < t → ∃ α : ℝ, 0 < α ∧ α ≤ t/2 ∧ ∀ ω' : ℝ, ω+t ≤ ω' → d σ ω → e σ ω' → r σ (ω'-α)) (J (fun ε a η δ => ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y ((∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → LeanEval.Analysis.WangZahlKakeya.Space, (∀ j, ‖w j‖ = 1) ∧ (∀ j j', j ≠ j' → MeasureTheory.volume (T ρ (z j) (w j) ∩ T ρ (z j') (w j')) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T ρ (z j) (w j))) ∧ (∀ i, ∃! j, T δ (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j, ∃ i, T δ (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j j', (Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j) (w j)} : ℝ) ≤ δ ^ (-η) * (Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j') (w j')} : ℝ)) ∧ (∀ j, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j) (w j) ∧ T δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η) * (Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j) (w j)} : ℝ)) * MeasureTheory.volume W)) → ENNReal.ofReal (a * δ ^ ε) ≤ MeasureTheory.volume (⋃ i, Y i))))) (fun s w => J (fun ε a η δ => ∀ m : ℝ, 1 ≤ m → Q η δ m (δ ^ (-η)) (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (N * δ)) ^ (-s))))) (fun s w => J (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * (N * δ)) ^ (-s))))) (fun s w => J (fun ε a η δ => Q η δ (δ ^ (-η)) (δ ^ (-η)) (fun N => a * δ ^ (w + ε) * (N * δ ^ 2) * (N * δ) ^ (-s))))) (fun η δ m l f => ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y ((∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ ENNReal.ofReal (l * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (f n) ≤ MeasureTheory.volume (⋃ i, Y i)))) (fun P => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → P ε a η δ)) (fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i)) → P)) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v))) := by
  simpa only [PointwiseImprovement, AllScalesVolume, AllScalesCover, Full, Restricted,
    Admissible, Estimate, WangZahlLot.Obl.wz_endpoint_bootstrap.Dense, Katz, Frostman, tube, and_imp] using uniform_of_pointwise hpoint

end WangZahlLot.Obl.wz_restricted_uniform_improvement
