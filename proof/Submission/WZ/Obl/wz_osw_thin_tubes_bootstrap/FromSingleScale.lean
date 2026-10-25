-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.FromSingleScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_thin_tubes_bootstrap.SingleScale

/-!
# o141 from the single-scale heavy-pair estimate

`P2Statement` is the single-scale estimate, literally as frozen in the
conclusion of the single-scale child of the split of o141 (session x0397); `o141_of_P2` proves the frozen statement of o141
from it, applying `one_direction` to `(G, G')` and to `(G', G)`.
-/

namespace WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap

/-- The single-scale heavy-pair estimate (closed form). -/
def P2Statement : Prop :=
  ∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ ε : ℝ, 0 < ε → ∃ τ θ η r₀ : ℝ, 0 < τ ∧ 0 < θ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ δ r σ K C : ℝ, 0 < δ → δ ≤ r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → 1 ≤ K → K ≤ r ^ (-η) → 1 ≤ C → C ≤ r ^ (-η) → ∀ (G G' : Set (EuclideanSpace ℝ (Fin 2))) (E : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Fr δ C G → Fr δ C G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → E ⊆ G ×ˢ G' → (∀ b ∈ G, ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 → ∀ ρ : ℝ, δ ≤ ρ → ({b' | (b, b') ∈ E ∧ |inner ℝ (b' - b) e| < ρ}.ncard : ℝ) ≤ K * ρ ^ σ * G'.ncard) → ({q ∈ E | ∃ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 ∧ |inner ℝ (q.2 - q.1) e| < r ∧ r ^ (σ + τ) * G'.ncard ≤ ({b' | (q.1, b') ∈ E ∧ |inner ℝ (b' - q.1) e| < r}.ncard : ℝ)}.ncard : ℝ) ≤ r ^ θ * G.ncard * G'.ncard

theorem o141_of_P2 (h : P2Statement) : ∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ TT, TT = (fun (δ σ K c : ℝ) (G G' : Set (EuclideanSpace ℝ (Fin 2))) => ∃ T : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), T ⊆ G ×ˢ G' ∧ (1 - c) * G.ncard * G'.ncard ≤ (T.ncard : ℝ) ∧ ∀ b ∈ G, ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 → ∀ r : ℝ, δ ≤ r → ({b' | (b, b') ∈ T ∧ |inner ℝ (b' - b) e| < r}.ncard : ℝ) ≤ K * r ^ σ * G'.ncard) → ∀ ε : ℝ, 0 < ε → ∃ τ M δ₀ : ℝ, 0 < τ ∧ 1 ≤ M ∧ 0 < δ₀ ∧ ∀ δ σ c K C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → 0 < c → c < 1 / 10 → 1 ≤ K → 1 ≤ C → ∀ G G' : Set (EuclideanSpace ℝ (Fin 2)), Fr δ C G → Fr δ C G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → TT δ σ K c G G' → TT δ σ K c G' G → TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G G' ∧ TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G' G := by
  intro Fr hFr TT hTT ε hε
  obtain ⟨τ₀, θ, η, r₀, hτ₀, hθ, hη, hr₀, hSS⟩ := h Fr hFr ε hε
  subst hFr hTT
  have hSS' : SingleScaleAt ε τ₀ θ η r₀ :=
    fun δ r σ K C h1 h2 h3 h4 h5 h6 h7 h8 h9 G G' hG hG' hsep E hE hthin =>
      hSS δ r σ K C h1 h2 h3 h4 h5 h6 h7 h8 h9 G G' E hG hG' hsep hE hthin
  obtain ⟨τ, M, hτ, hM, hdir⟩ := one_direction hε hτ₀ hθ hη hr₀ hSS'
  refine ⟨τ, M, 1, hτ, hM, one_pos, ?_⟩
  intro δ σ c K C hδ _ hσ1 hσ2 hc hc1 hK hC G G' hG hG' hsep hTT1 hTT2
  obtain ⟨T, hT, hdense, hthin⟩ := hTT1
  obtain ⟨T₂, hT₂, hdense₂, hthin₂⟩ := hTT2
  exact ⟨hdir δ σ c K C hδ hσ1 hσ2 hc hc1 hK hC G G' hG hG' hsep T hT hdense hthin,
    hdir δ σ c K C hδ hσ1 hσ2 hc hc1 hK hC G' G hG' hG
      (fun b hb b' hb' => by rw [dist_comm]; exact hsep b' hb' b hb) T₂ hT₂ hdense₂ hthin₂⟩

end WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap
