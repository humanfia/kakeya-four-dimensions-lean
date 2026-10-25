-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.CountedGain
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_frostman_quadratic_flat_gain`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_frostman_quadratic_flat_gain/`
belong to this obligation.

The proof is the counted flat gain `X264.countedGain_of_estimateE` (session x0264's work on o072,
carried over by x0305/x0443 on o038 as `flatGainQ_holds`), copied into `X264/` with its namespace
renamed.
-/

theorem WangZahlLot.wz_frostman_quadratic_flat_gain : ∀ σ ω' : ℝ, (fun (B : Set (EuclideanSpace ℝ (Fin 3))) => (fun (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) => (fun (o : ℝ → ENNReal) => (fun (T : ℝ → (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → Set (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (J : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop) => (fun (K : ℝ → ℝ → ℝ → (n : ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) => (fun (e : ℝ → ℝ → Prop) => (fun (SC : ℝ → ℝ → ℝ → (k : ℕ) → (Fin k → Set (EuclideanSpace ℝ (Fin 3))) → Prop) => 0 < σ → σ ≤ 1/2 → 0 < ω' → e σ ω' → ∀ ζ₂ : ℝ, 0 < ζ₂ → ∃ α : ℝ, 0 < α ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ ζ₃ : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₀ → ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (x v : Fin n → (EuclideanSpace ℝ (Fin 3))) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), H η δ n x v Y ((∀ i, o (δ ^ η * δ ^ 2) ≤ μ (Y i)) → SC ζ₂ ζ₃ δ n (fun i => T δ (x i) (v i)) → o (a * δ ^ (ω' - α + ε) * (n * δ ^ 4) ^ (σ / 2)) ≤ μ (⋃ i, Y i))) (fun ζ₂ ζ₃ δ k A => ∃ a b : ℝ, δ ≤ a ∧ a ≤ δ ^ (ζ₂ / 200) * b ∧ b ≤ 1 ∧ ∃ (p : ℕ) (c e₁ e₂ e₃ : Fin p → (EuclideanSpace ℝ (Fin 3))), (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧ (fun (P : Fin p → Set (EuclideanSpace ℝ (Fin 3))) => (∀ i, ∃ j, A i ⊆ P j) ∧ (∀ j j', (Set.ncard {i | A i ⊆ P j} : ℝ) ≤ δ ^ (-ζ₃) * Set.ncard {i | A i ⊆ P j'}) ∧ (∀ U : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o (Set.ncard {j | P j ⊆ U}) ≤ o (δ ^ (-ζ₃) * p) * μ U) ∧ (∀ j (U : Set (EuclideanSpace ℝ (Fin 3))), Convex ℝ U → o (Set.ncard {i | A i ⊆ P j ∧ A i ⊆ U}) * μ (P j) ≤ o (δ ^ (-ζ₃) * Set.ncard {i | A i ⊆ P j}) * μ U) ∧ (∀ j (U : Set (EuclideanSpace ℝ (Fin 3))), Convex ℝ U → o (Set.ncard {j' | P j' ⊆ Metric.thickening b (P j) ∧ P j' ⊆ U}) * μ (P j) ≤ o (δ ^ (-ζ₃)) * μ U) ∧ (∀ U : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o (Set.ncard {j | P j ⊆ U}) * o ((a * b) ^ 2) ≤ o (δ ^ (-ζ₃)) * (μ U) ^ 2)) (fun j => {y | |inner ℝ (e₁ j) (y - c j)| ≤ a ∧ |inner ℝ (e₂ j) (y - c j)| ≤ b ∧ |inner ℝ (e₃ j) (y - c j)| ≤ 1}))) (fun s w => J (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * (N * δ)) ^ (-s))))) (fun η δ m l f => ∀ (n : ℕ) (x v : Fin n → (EuclideanSpace ℝ (Fin 3))) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), H η δ n x v Y (K δ m l n x v (o (f n) ≤ μ (⋃ i, Y i))))) (fun δ m l n x v P => (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ o m * μ W) → (∀ (u : (EuclideanSpace ℝ (Fin 3))) (t r : ℝ), ‖u‖ = 1 → 0 < r → o (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ o (l * n) * μ (B ∩ {p | |inner ℝ u p - t| ≤ r})) → P)) (fun P => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → P ε a η δ)) (fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i j, i ≠ j → μ (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * μ (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → P)) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) ENNReal.ofReal) MeasureTheory.volume) (Metric.ball 0 1) := by
  intro σ ω'
  beta_reduce
  intro hσ hσ1 hω' he ζ₂ hζ₂
  have hE : WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.EstimateE σ ω' := he
  obtain ⟨α, hα, ζ₀, hζ₀, H⟩ :=
    WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.countedGain_of_estimateE
      hσ hσ1 hω' hζ₂ hE
  refine ⟨α, hα, ζ₀, hζ₀, ?_⟩
  intro ζ₃ hζ₃ hζ₃₀ ε hε
  obtain ⟨A, hA, η, hη, δ₀, hδ₀, H2⟩ := H ζ₃ hζ₃ hζ₃₀ ε hε
  refine ⟨A, hA, η, hη, δ₀, hδ₀, ?_⟩
  intro δ hδ hδδ₀ n x v Y hn hv hB hov hYm hYT hsum hdens hSC
  obtain ⟨a, b, hδa, hab, hb1, p, c, e₁, e₂, e₃, hon, h1, h2, h3, h4, h5, hQ⟩ := hSC
  exact H2 δ hδ hδδ₀ n x v Y hn hv hB hov hYm hYT hsum hdens a b hδa hab hb1 p c e₁ e₂ e₃ hon
    ⟨h1, h2, h3, h4, h5⟩ hQ
