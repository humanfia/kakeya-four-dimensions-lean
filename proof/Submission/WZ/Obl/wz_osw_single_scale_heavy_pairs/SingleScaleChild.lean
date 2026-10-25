-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.SingleScaleChild.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.OfA

/-!
# The single-scale child of the split of o141

`single_scale_heavy_pairs`: the Furstenberg bush estimate and the rich-strip count
(literal statements of the split of o141, session x0397) imply the single-scale
heavy-pair estimate `P2Statement` (literal).  This is the statement of the child
`wz_osw_single_scale_heavy_pairs`; its rich-strip premise is not even needed,
since `frostman_rich_strip_count` proves it.
-/

namespace WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

theorem single_scale_heavy_pairs : (∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → ∀ (P : Set (EuclideanSpace ℝ (Fin 2))) (D : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), P.Finite → P.Nonempty → D.Finite → (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) → (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) → (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') → (∀ p ∈ P, ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ → ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) → ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧ r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ)) → (∃ A : ℝ, 0 < A ∧ ∀ r C l : ℝ, 0 < r → r ≤ 1 → 1 ≤ C → 0 < l → ∀ (Y : Set (EuclideanSpace ℝ (Fin 2))) (J : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Y.Finite → Y.Nonempty → (∀ y ∈ Y, ‖y‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((Y ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ * Y.ncard) → J.Finite → (∀ q ∈ J, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 ∧ l * Y.ncard ≤ ({y ∈ Y | |inner ℝ (y - q.1) q.2| < r}.ncard : ℝ)) → (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) → l ^ 2 * J.ncard ≤ A * C * (1 + Real.log (1 / r))) → ∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ ε : ℝ, 0 < ε → ∃ τ θ η r₀ : ℝ, 0 < τ ∧ 0 < θ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ δ r σ K C : ℝ, 0 < δ → δ ≤ r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → 1 ≤ K → K ≤ r ^ (-η) → 1 ≤ C → C ≤ r ^ (-η) → ∀ (G G' : Set (EuclideanSpace ℝ (Fin 2))) (E : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Fr δ C G → Fr δ C G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → E ⊆ G ×ˢ G' → (∀ b ∈ G, ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 → ∀ ρ : ℝ, δ ≤ ρ → ({b' | (b, b') ∈ E ∧ |inner ℝ (b' - b) e| < ρ}.ncard : ℝ) ≤ K * ρ ^ σ * G'.ncard) → ({q ∈ E | ∃ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 ∧ |inner ℝ (q.2 - q.1) e| < r ∧ r ^ (σ + τ) * G'.ncard ≤ ({b' | (q.1, b') ∈ E ∧ |inner ℝ (b' - q.1) e| < r}.ncard : ℝ)}.ncard : ℝ) ≤ r ^ θ * G.ncard * G'.ncard := by
  intro hA hB
  obtain ⟨AB, hAB, h⟩ := hB
  exact P2_of_furstenberg_richstrip (furstenberg_internal_of_A hA)
    ⟨AB, hAB, fun r C hr hr1 hC l hl Y J hY hYne hY4 hFr hJ hJmem hJsep =>
      h r C l hr hr1 hC hl Y J hY hYne hY4 hFr hJ hJmem hJsep⟩

end WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
