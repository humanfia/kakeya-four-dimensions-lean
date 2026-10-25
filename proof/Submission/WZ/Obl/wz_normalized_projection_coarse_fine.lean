-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Support
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_normalized_projection_coarse_fine`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_normalized_projection_coarse_fine/`
belong to this obligation.
-/

theorem WangZahlLot.wz_normalized_projection_coarse_fine : ((fun N : (ℝ → ℝ) → Prop => ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ f : ℝ → ℝ, N f → |f 0| ≤ 1 → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)), (∀ i, ‖q i‖ ≤ 10) → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → MeasureTheory.lintegral MeasureTheory.volume (fun p : ℝ × ℝ => (Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - (q i 0 + q i 1 * f p.2 + q i 2 * p.2 * f p.2)| ≤ δ} (fun _ => (1 : ENNReal)) p)) ^ (3/2 : ℝ)) ≤ ENNReal.ofReal (δ ^ (-ε))) (fun f : ℝ → ℝ => ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ))) → ((fun T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (F : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (N : (ℝ → ℝ) → Prop) (P : (ℝ → ℝ) → Set LeanEval.Analysis.WangZahlKakeya.Space → Set (ℝ × ℝ)) => ∀ ε κ : ℝ, 0 < ε → ε < 1 → 0 < κ → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y → (∀ i, (1/2 : ℝ) ≤ |v i 2|) → F η δ n x v → ∀ f : ℝ → ℝ, N f → |f 0| ≤ 1 → ∃ ρ : ℝ, δ ^ (1 - ε ^ 2) < ρ ∧ ρ < 1 ∧ ∃ Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space, (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧ ENNReal.ofReal (δ ^ κ * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Z i)) ∧ ENNReal.ofReal ((δ / ρ) ^ ε) * MeasureTheory.volume (Metric.thickening ρ (P f (⋃ i, Z i))) ≤ MeasureTheory.volume (P f (⋃ i, Z i))) (fun η δ n x v Y => 0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, T δ (x i) (v i) ⊆ Metric.ball 0 1) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧ (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ T δ (x i) (v i)) ∧ ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))) (fun η δ n x v => ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * MeasureTheory.volume W) (fun f : ℝ → ℝ => ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) (fun (f : ℝ → ℝ) (E : Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun p : LeanEval.Analysis.WangZahlKakeya.Space => (p 0 + f (p 2) * p 1, p 2)) '' E)) (fun (δ : ℝ) (x v : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening δ (segment ℝ x (x + v)))) := by
  intro hC
  have hC' : WangZahlLot.Obl.wz_normalized_projection_coarse_fine.CinematicEstimate := by
    intro e he
    obtain ⟨ηC, hηC, dC, hdC, hmoment⟩ := hC e he
    refine ⟨ηC, hηC, dC, hdC, ?_⟩
    intro τ hτ hτC hτsmall f hf hf0 n q hnorm hsep hcount
    simpa only [WangZahlLot.Obl.wz_normalized_projection_coarse_fine.multiplicity,
      WangZahlLot.Obl.wz_normalized_projection_coarse_fine.graphStrip, zero_mul, add_zero] using
      hmoment τ hτ hτC hτsmall f hf hf0 n q hnorm hsep hcount
  exact WangZahlLot.Obl.wz_normalized_projection_coarse_fine.full_comparison_of_small_comparisons
    (fun ε hε hεsmall =>
      WangZahlLot.Obl.wz_normalized_projection_coarse_fine.small_comparison_of_cinematic hC' hε hεsmall)
