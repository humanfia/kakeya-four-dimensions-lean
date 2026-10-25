-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_balanced_refinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_tower_balanced_refinement.Proof
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_tower_balanced_refinement`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_tower_balanced_refinement`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_tower_balanced_refinement/`
belong to this obligation.
-/

theorem WangZahlLot.wz_tower_balanced_refinement : ∀ (B : ℕ) (ε : ℝ), ∀ μ, μ = ((MeasureTheory.volume : MeasureTheory.Measure LeanEval.Analysis.WangZahlKakeya.Space)) → ∀ e, e = (ENNReal.ofReal) → ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p+q))) → ∀ K, K = (fun (d L : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ W, Convex ℝ W → e (Set.ncard {i | T d (x i) (v i) ⊆ W} * d^2) ≤ e L * μ W) → ∀ F, F = (fun (d L : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖=1 → 0<r → e (Set.ncard {i | T d (x i) (v i) ⊆ Metric.ball 0 1 ∩ {p | |inner ℝ u p-t| ≤ r}}) ≤ e (L*n) * μ (Metric.ball 0 1 ∩ {p | |inner ℝ u p-t| ≤ r})) → ∀ A, A = (fun (d η M L : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) => 0<n ∧ (∀ i, ‖v i‖=1 ∧ T d (x i) (v i) ⊆ Metric.ball 0 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T d (x i) (v i)) ∧ (∀ i j, i≠j → μ (T d (x i) (v i) ∩ T d (x j) (v j)) ≤ 1/2 * μ (T d (x i) (v i))) ∧ e (d^η*n*d^2) ≤ ∑ i, μ (Y i) ∧ K d M n x v ∧ F d L n x v) → ∀ H, H = (fun (b : Bool) (d L g : ℝ) (B n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∃ J : ℕ, 1≤J ∧ J≤B ∧ ∃ (r : ℕ → ℝ) (N : ℕ → ℕ) (y w : ∀ j, Fin (N j) → LeanEval.Analysis.WangZahlKakeya.Space) (f : ∀ j, Fin (N (j+1)) → Fin (N j)), r 0=1 ∧ r J=d ∧ N 0=1 ∧ (∃ u : Fin n ≃ Fin (N J), ∀ i, y J (u i)=x i ∧ w J (u i)=v i) ∧ (∀ j, j≤J → ∀ k, ‖w j k‖=1) ∧ (∀ j, j<J → 0<r (j+1) ∧ r (j+1)<r j ∧ d^g*r j≤r (j+1) ∧ ∀ i, T (r (j+1)) (y (j+1) i) (w (j+1) i) ⊆ T (r j) (y j (f j i)) (w j (f j i))) ∧ (if b then ∀ j, j≤J → K (r j) L (N j) (y j) (w j) else ∀ j, j<J → ∀ k W, Convex ℝ W → e (Set.ncard {i | f j i=k ∧ T (r (j+1)) (y (j+1) i) (w (j+1) i) ⊆ W} * (r (j+1))^2) ≤ e L * μ W)) → 0<ε → ∃ θ : ℝ, 0<θ ∧ θ≤ε/2 ∧ ∃ d₀ : ℝ, 0<d₀ ∧ ∀ δ : ℝ, 0<δ → δ≤1/100 → δ≤d₀ → ∀ g : ℝ, 0<g → g≤ε/2 → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) (M L : ℝ), A δ θ M L n x v Y → H true δ (δ^(-θ)) g B n x v → ∃ (m : ℕ) (x' v' : Fin m → LeanEval.Analysis.WangZahlKakeya.Space) (Y' : Fin m → Set LeanEval.Analysis.WangZahlKakeya.Space) (M' L' : ℝ), A δ ε M' L' m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧ e (δ^(ε/2))*(∑ i, μ (Y i)) ≤ ∑ j, μ (Y' j) ∧ ∀ ρ₀ : ℝ, δ≤ρ₀ → ρ₀≤1 → ∃ ρ : ℝ, ρ₀≤ρ ∧ ρ<δ^(-ε)*ρ₀ ∧ ∃ (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin m → Fin N), (∀ k, ‖w k‖=1) ∧ (∀ j, T δ (x' j) (v' j) ⊆ T ρ (y (f j)) (w (f j))) ∧ (∀ k k', (Set.ncard {j | f j=k} : ℝ) ≤ δ^(-ε)*Set.ncard {j | f j=k'}) ∧ K ρ (δ^(-ε)) N y w := by
  intro B ε μ rfl e rfl T rfl K rfl F rfl A rfl H rfl hε
  exact WangZahlLot.Obl.wz_tower_balanced_refinement.balanced_refinement B ε hε
