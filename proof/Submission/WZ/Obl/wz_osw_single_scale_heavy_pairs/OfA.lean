-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.OfA.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.FromFurstenberg

/-!
# o141 from the Furstenberg bush estimate, in the literal form of the split

`o141_of_A` takes the Furstenberg bush estimate exactly as frozen by the split of
o141 (session x0397), whose bushes are only asked to be `r`-separated (not up to
sign); the configuration built in `SingleScaleCore` is separated up to sign, so
the adapter only forgets that.
-/

namespace WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

theorem furstenberg_internal_of_A (h : ∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → ∀ (P : Set (EuclideanSpace ℝ (Fin 2))) (D : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), P.Finite → P.Nonempty → D.Finite → (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) → (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) → (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') → (∀ p ∈ P, ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ → ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) → ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧ r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ ε₀ ηA rA : ℝ, 0 < ε₀ ∧ 0 < ηA ∧ 0 < rA ∧
      ∀ r σ : ℝ, 0 < r → r ≤ rA → 1 / 4 ≤ σ → σ ≤ 1 - ε → FurstenbergAt r σ ε₀ ηA := by
  intro ε hε
  obtain ⟨ε₀, η, r₀, hε₀, hη, hr₀, hA⟩ := h ε hε
  refine ⟨ε₀, η, r₀, hε₀, hη, hr₀, ?_⟩
  intro r σ hr hrr₀ hσ1 hσ2 P D hPfin hPne hP4 hPfr hDfin hDmem hbush hsep hKT
  exact hA r σ hr hrr₀ hσ1 hσ2 P D hPfin hPne hDfin hP4 hPfr hDmem hbush
    (fun p e e' he he' hne => (hsep p e e' he he' hne).1) hKT

/-- o141 from the Furstenberg bush estimate (literal form of the split). -/
theorem o141_of_A (h : ∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → ∀ (P : Set (EuclideanSpace ℝ (Fin 2))) (D : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), P.Finite → P.Nonempty → D.Finite → (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) → (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) → (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') → (∀ p ∈ P, ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ → ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) → ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧ r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ)) : ∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ TT, TT = (fun (δ σ K c : ℝ) (G G' : Set (EuclideanSpace ℝ (Fin 2))) => ∃ T : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), T ⊆ G ×ˢ G' ∧ (1 - c) * G.ncard * G'.ncard ≤ (T.ncard : ℝ) ∧ ∀ b ∈ G, ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 → ∀ r : ℝ, δ ≤ r → ({b' | (b, b') ∈ T ∧ |inner ℝ (b' - b) e| < r}.ncard : ℝ) ≤ K * r ^ σ * G'.ncard) → ∀ ε : ℝ, 0 < ε → ∃ τ M δ₀ : ℝ, 0 < τ ∧ 1 ≤ M ∧ 0 < δ₀ ∧ ∀ δ σ c K C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → 0 < c → c < 1 / 10 → 1 ≤ K → 1 ≤ C → ∀ G G' : Set (EuclideanSpace ℝ (Fin 2)), Fr δ C G → Fr δ C G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → TT δ σ K c G G' → TT δ σ K c G' G → TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G G' ∧ TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G' G :=
  o141_of_furstenberg (furstenberg_internal_of_A h)

end WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
