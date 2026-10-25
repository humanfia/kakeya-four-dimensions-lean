-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_multiscale_finite_tower.FiniteTower
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyRestriction
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyGain
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyPreparation
import Submission.WZ.Obl.wz_multiscale_finite_tower.ClosedRegularization
import Submission.WZ.Obl.wz_multiscale_finite_tower.BalancedRepresentativeCovers
import Submission.WZ.Obl.wz_multiscale_finite_tower.InsertPartitions
import Submission.WZ.Obl.wz_multiscale_finite_tower.EdgeControl
import Submission.WZ.Obl.wz_multiscale_finite_tower.GroupRetention
import Submission.WZ.Obl.wz_multiscale_finite_tower.GroupedCertificate
import Submission.WZ.Obl.wz_multiscale_finite_tower.UniformInsertion
import Submission.WZ.Obl.wz_multiscale_finite_tower.Iteration
import Submission.WZ.Obl.wz_multiscale_finite_tower.Dyadic
import Submission.WZ.Obl.wz_multiscale_finite_tower.LogLoss
import Submission.WZ.Obl.wz_multiscale_finite_tower.Products
import Submission.WZ.Obl.wz_multiscale_finite_tower.Selection
import Submission.WZ.Obl.wz_multiscale_finite_tower.StrongIteration
import Submission.WZ.Obl.wz_multiscale_finite_tower.Slabs
import Submission.WZ.Obl.wz_multiscale_finite_tower.Cardinality
import Submission.WZ.Obl.wz_multiscale_finite_tower.Cells
import Submission.WZ.Obl.wz_multiscale_finite_tower.Direct
import Submission.WZ.Obl.wz_multiscale_finite_tower.GridTransfer
import Submission.WZ.Obl.wz_multiscale_finite_tower.Physical
import Submission.WZ.Obl.wz_multiscale_finite_tower.PhysicalEstimates
import Submission.WZ.Obl.wz_multiscale_finite_tower.PhysicalAlternative
import Submission.WZ.Obl.wz_multiscale_finite_tower.CellClasses
import Submission.WZ.Obl.wz_multiscale_finite_tower.GridRegularization
import Submission.WZ.Obl.wz_multiscale_finite_tower.MultipleGrids
import Submission.WZ.Obl.wz_multiscale_finite_tower.DyadicMeshes
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedCovers
import Submission.WZ.Obl.wz_multiscale_finite_tower.CountComparison
import Submission.WZ.Obl.wz_multiscale_finite_tower.RepresentativeSlabs
import Submission.WZ.Obl.wz_multiscale_finite_tower.BalancedPruning
import Submission.WZ.Obl.wz_multiscale_finite_tower.AxisShift
import Submission.WZ.Obl.wz_multiscale_finite_tower.AxisShiftCounts
import Submission.WZ.Obl.wz_multiscale_finite_tower.ScalarAlignment
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedInitialization
import Submission.WZ.Obl.wz_multiscale_finite_tower.WeightedSeparation
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedPreparation
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedFinal
import Submission.WZ.Obl.wz_multiscale_finite_tower.Hierarchy
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyBase
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_multiscale_finite_tower`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_multiscale_finite_tower`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_multiscale_finite_tower/`
belong to this obligation.
-/

theorem WangZahlLot.wz_multiscale_finite_tower : ∀ σ ω : ℝ, ∀ μ, μ = ((MeasureTheory.volume : MeasureTheory.Measure LeanEval.Analysis.WangZahlKakeya.Space)) → ∀ e, e = (ENNReal.ofReal) → ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p+q))) → ∀ K, K = (fun (d L : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ W, Convex ℝ W → e (Set.ncard {i | T d (x i) (v i) ⊆ W} * d^2) ≤ e L * μ W) → ∀ F, F = (fun (d L : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖=1 → 0<r → e (Set.ncard {i | T d (x i) (v i) ⊆ Metric.ball 0 1 ∩ {p | |inner ℝ u p-t| ≤ r}}) ≤ e (L*n) * μ (Metric.ball 0 1 ∩ {p | |inner ℝ u p-t| ≤ r})) → ∀ A, A = (fun (d η M L : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) => 0<n ∧ (∀ i, ‖v i‖=1 ∧ T d (x i) (v i) ⊆ Metric.ball 0 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T d (x i) (v i)) ∧ (∀ i j, i≠j → μ (T d (x i) (v i) ∩ T d (x j) (v j)) ≤ 1/2 * μ (T d (x i) (v i))) ∧ e (d^η*n*d^2) ≤ ∑ i, μ (Y i) ∧ K d M n x v ∧ F d L n x v) → ∀ H, H = (fun (b : Bool) (d L g : ℝ) (B n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∃ J : ℕ, 1≤J ∧ J≤B ∧ ∃ (r : ℕ → ℝ) (N : ℕ → ℕ) (y w : ∀ j, Fin (N j) → LeanEval.Analysis.WangZahlKakeya.Space) (f : ∀ j, Fin (N (j+1)) → Fin (N j)), r 0=1 ∧ r J=d ∧ N 0=1 ∧ (∃ u : Fin n ≃ Fin (N J), ∀ i, y J (u i)=x i ∧ w J (u i)=v i) ∧ (∀ j, j≤J → ∀ k, ‖w j k‖=1) ∧ (∀ j, j<J → 0<r (j+1) ∧ r (j+1)<r j ∧ d^g*r j≤r (j+1) ∧ ∀ i, T (r (j+1)) (y (j+1) i) (w (j+1) i) ⊆ T (r j) (y j (f j i)) (w j (f j i))) ∧ (if b then ∀ j, j≤J → K (r j) L (N j) (y j) (w j) else ∀ j, j<J → ∀ k W, Convex ℝ W → e (Set.ncard {i | f j i=k ∧ T (r (j+1)) (y (j+1) i) (w (j+1) i) ⊆ W} * (r (j+1))^2) ≤ e L * μ W)) → ∀ Q, Q = (fun (κ α d : ℝ) (n : ℕ) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) => e (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ μ (⋃ i, Y i)) → 0<σ → σ≤1/2 → 0<ω → ω≤1 → (∀ ε : ℝ, 0<ε → ∃ a : ℝ, 0<a ∧ ∃ η : ℝ, 0<η ∧ ∀ δ : ℝ, 0<δ → δ≤1/100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ n x v Y, A δ η m l n x v Y → e (a*δ^(ω+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2 : ℝ))*l*(n*δ))^(-σ)) ≤ μ (⋃ i, Y i)) → (∀ ζ : ℝ, 0<ζ → ∃ α : ℝ, 0<α ∧ ∃ κ : ℝ, 0<κ ∧ ∃ η : ℝ, 0<η ∧ ∀ δ : ℝ, 0<δ → δ≤1/100 → ∀ n x v Y, A δ η (δ^(-η)) (δ^(-η)) n x v Y → Q κ α δ n Y ∨ ∃ (S : Finset (Fin n)) (Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℝ) (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧ e (δ^ζ)*(∑ i, μ (Y i)) ≤ ∑ i ∈ S, μ (Z i) ∧ δ^(1-ω/100)≤ρ ∧ ρ≤δ^(ω/100) ∧ (∀ k, ‖w k‖=1) ∧ (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ K ρ (δ^(-ζ)) N y w ∧ F ρ (δ^(-ζ)) N y w ∧ ∀ k (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖=1 → 0<r → e (Set.ncard {i | i ∈ S ∧ f i=k ∧ T δ (x i) (v i) ⊆ T (2*ρ) (y k-(1/2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p-t|≤r}}) * μ (T (2*ρ) (y k-(1/2 : ℝ) • w k) (2 • w k)) ≤ e (δ^(-ζ)*Set.ncard {i | i ∈ S ∧ f i=k}) * μ (T (2*ρ) (y k-(1/2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p-t|≤r})) → ∀ (q : ℕ) (ε D : ℝ), 0<ε → 0<D → ∃ α : ℝ, 0<α ∧ ∃ κ : ℝ, 0<κ ∧ ∃ η : ℝ, 0<η ∧ ∀ δ : ℝ, 0<δ → δ≤1/100 → ∀ n x v Y, A δ η (δ^(-η)) (δ^(-η)) n x v Y → Q κ α δ n Y ∨ (δ≤D ∧ ∃ (m : ℕ) (x' v' : Fin m → LeanEval.Analysis.WangZahlKakeya.Space) (Y' : Fin m → Set LeanEval.Analysis.WangZahlKakeya.Space) (M L : ℝ), A δ ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧ e (δ^ε)*(∑ i, μ (Y i)) ≤ ∑ j, μ (Y' j) ∧ H false δ (δ^(-ε)) (2*(1-ω/100)^q) (2^q) m x' v' ) := by
  intro σ ω μ hμ e he T hT K hK F hF A hA H hH Q hQ
  subst μ
  subst e
  subst T
  subst K
  subst F
  subst A
  subst H
  subst Q
  intro hσ hσ1 hω hω1 hE hOne q
  exact WangZahlLot.Obl.wz_multiscale_finite_tower.finite_tower_all_depths
    hE hOne hσ.le hσ1 hω hω1 q
