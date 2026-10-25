-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_furstenberg_bush_line_count
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs
import Submission.WZ.Obl.wz_osw_thin_tubes_bootstrap.FromSingleScale
import Submission.WZ.Obl.wz_osw_thin_tubes_bootstrap.RichStripSet
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_osw_thin_tubes_bootstrap`

The Orponen-Shmerkin-Wang bootstrapping step (s = 1).

* `wz_furstenberg_bush_line_count` (child): the epsilon-improved Furstenberg estimate in
  dual counting form (the only sum-product input);
* `WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.frostman_rich_strip_count` (proved here,
  files `RichStripSet`, `RichStrip`, `StripCount`, `StripCode`, `Geometry`, by session
  x0394): the L^2 count of rich strips for a 1-Frostman set;
* `wz_osw_single_scale_heavy_pairs` (child): the two statements above imply the
  single-scale heavy-pair estimate `P2Statement`;
* `WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.o141_of_P2` (proved here, files
  `FromSingleScale`, `SingleScale`, `Removal`, `Numerics`, by session x0394): the
  single-scale estimate implies this theorem (removal of the pairs lying in heavy strips,
  summed over dyadic scales).

The premises of the implication child are verbatim copies of the statements of the
Furstenberg child and of `frostman_rich_strip_count`, and its conclusion is `P2Statement`
verbatim, so the proof is application.
-/

theorem WangZahlLot.wz_osw_thin_tubes_bootstrap : ∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ TT, TT = (fun (δ σ K c : ℝ) (G G' : Set (EuclideanSpace ℝ (Fin 2))) => ∃ T : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), T ⊆ G ×ˢ G' ∧ (1 - c) * G.ncard * G'.ncard ≤ (T.ncard : ℝ) ∧ ∀ b ∈ G, ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 → ∀ r : ℝ, δ ≤ r → ({b' | (b, b') ∈ T ∧ |inner ℝ (b' - b) e| < r}.ncard : ℝ) ≤ K * r ^ σ * G'.ncard) → ∀ ε : ℝ, 0 < ε → ∃ τ M δ₀ : ℝ, 0 < τ ∧ 1 ≤ M ∧ 0 < δ₀ ∧ ∀ δ σ c K C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → 0 < c → c < 1 / 10 → 1 ≤ K → 1 ≤ C → ∀ G G' : Set (EuclideanSpace ℝ (Fin 2)), Fr δ C G → Fr δ C G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → TT δ σ K c G G' → TT δ σ K c G' G → TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G G' ∧ TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G' G := by
  exact WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.o141_of_P2
    (WangZahlLot.wz_osw_single_scale_heavy_pairs WangZahlLot.wz_furstenberg_bush_line_count
      WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.frostman_rich_strip_count)
