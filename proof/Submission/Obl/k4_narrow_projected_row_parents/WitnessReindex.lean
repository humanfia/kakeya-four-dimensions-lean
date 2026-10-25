import Submission.Obl.k4_narrow_projected_row_parents.Reindex
import Submission.Obl.k4_narrow_projected_row_parents.WitnessExponent

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Filter

variable {α : Type} [MeasurableSpace α]

/-- Reindexing a witness on a limiting-width subsequence normalizes its own
index map to the identity. The strict width gap restores narrowness on this
whole subsequence. -/
theorem Model.NarrowWitness.on_exponent_subsequence {cfg : Model α}
    {L a m s B : ℝ} {τ φ : ℕ → ℕ} {H : ℕ → ℝ}
    {ρ' : ℕ → Measure (α × ℝ)} {β : ℕ → ℝ → ℝ} {n' : ℕ → ℝ → ℕ}
    {C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α}
    {tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ}
    {u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ}
    {G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ}
    (hv : Model.Valid cfg) (hw : Model.NarrowWitness cfg L a m s τ H ρ' β n' C tag u v G)
    (hφ : StrictMono φ) (hB : cfg.ℓ * s < B)
    (hfit : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      cfg.N (τ (φ k)) ^ (-B - δ) ≤ β (φ k) s ∧
      β (φ k) s ≤ cfg.N (τ (φ k)) ^ (-B + δ)) :
    Model.NarrowWitness (cfg.reindex (τ ∘ φ)) L a m s id
      (H ∘ φ) (ρ' ∘ φ) (fun k => β (φ k)) (fun k => n' (φ k))
      (fun k => C (φ k)) (fun k => tag (φ k)) (fun k => u (φ k))
      (fun k => v (φ k)) (fun k => G (φ k)) := by
  refine ⟨strictMono_id, fun k => hw.loss (φ k),
    fun ε hε => hφ.tendsto_atTop.eventually (hw.loss_subpower ε hε),
    fun k => hw.retained (φ k), fun k => hw.slice (φ k), ?_⟩
  let δ : ℝ := (B - cfg.ℓ * s) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨δ, hδ, ?_⟩
  apply Filter.Eventually.frequently
  filter_upwards [hfit δ hδ] with k hk
  change cfg.N (τ (φ k)) ^ δ * β (φ k) s < cfg.N (τ (φ k)) ^ (-cfg.ℓ * s)
  have hN : 0 < cfg.N (τ (φ k)) := by linarith [hv.scale (τ (φ k))]
  calc cfg.N (τ (φ k)) ^ δ * β (φ k) s
      ≤ cfg.N (τ (φ k)) ^ δ * cfg.N (τ (φ k)) ^ (-B + δ) :=
        mul_le_mul_of_nonneg_left hk.2 (Real.rpow_nonneg hN.le _)
    _ = cfg.N (τ (φ k)) ^ (-cfg.ℓ * s - (B - cfg.ℓ * s) / 2) := by
      rw [← Real.rpow_add hN]
      congr 1
      dsimp [δ]
      ring
    _ < cfg.N (τ (φ k)) ^ (-cfg.ℓ * s) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith [hv.scale (τ (φ k))]) (by linarith)

end Submission.Obl.k4_narrow_projected_row_parents
