import Submission.Obl.k4_narrow_projected_row_parents.FrontVelocity
import Submission.Obl.k4_narrow_projected_row_parents.ScalePlan
import Submission.Obl.k4_narrow_projected_row_parents.WitnessReindex

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Filter

/-- The analytic velocity-list comparison on an already normalized exponent
sequence. All further choices and transfers belong to `narrowFront_of_exponent_velocity`. -/
def ExponentVelocityComparison (C₀ : ℝ) : Prop :=
  Match → ∀ (α : Type) [MeasurableSpace α] (cfg : Model α), Model.Valid cfg →
    ∀ L a s : ℝ, 2 < L → 0 < a → a ≤ s → s ≤ 2 * a →
    ∀ (H : ℕ → ℝ) (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ)
      (n' : ℕ → ℝ → ℕ) (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
      (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
      (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
      (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),
      Model.NarrowWitness cfg L a ((L + 1) * a) s id H ρ' β n' C tag u v G →
      ∀ B : ℝ, cfg.ℓ * s < B → B ≤ cfg.ℓ * s + L * a →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
        cfg.N k ^ (-B - δ) ≤ β k s ∧ β k s ≤ cfg.N k ^ (-B + δ)) →
      ∀ r e mesh : ℝ, s < r → r < cfg.U → cfg.ℓ * r < B → B < (cfg.κ + cfg.ℓ) * r →
        0 < e → e < B - cfg.ℓ * r → e + cfg.ℓ * r < mesh →
        C₀ * (r + B + (L + 1) * a + s) ≤ mesh →
        cfg.Candidates ∨ VelocityLists cfg r mesh e

/-- Exponent extraction, the uniform depth budget and the return to the original
sequence reduce the frozen front theorem to one normalized analytic comparison. -/
theorem narrowFront_of_exponent_velocity {C₀ : ℝ} (hC₀ : 2 ≤ C₀)
    (hcmp : ExponentVelocityComparison C₀) : NarrowFront := by
  intro hRow hMatch α _ cfg hv
  refine ⟨fun L => narrowLambda cfg.S cfg.κ cfg.ℓ C₀ L,
    fun L _ => narrowLambda_palette hv.palette_pos, ?_⟩
  intro L hL _hlay a s ha haU has hs2 τ H ρ' β n' C tag u v G hw
  have hs : 0 < s := ha.trans_le has
  obtain ⟨φ, hφ, B, hB, hBA, hfit⟩ := hw.has_exponent hv (by linarith) ha.le hs.le
  obtain ⟨sc⟩ := exists_narrow_scales hv.rate_pos hv.transverse_pos hC₀ hL ha has hs2 hB hBA haU
  let ψ : ℕ → ℕ := τ ∘ φ
  have hψ : StrictMono ψ := hw.mono.comp hφ
  let cfg' : Model α := cfg.reindex ψ
  have hv' : Model.Valid cfg' := hv.reindex hψ.tendsto_atTop
  have hw' := hw.on_exponent_subsequence hv hφ hB hfit
  have hfit' : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      cfg'.N k ^ (-B - δ) ≤ β (φ k) s ∧ β (φ k) s ≤ cfg'.N k ^ (-B + δ) := hfit
  have hr : 0 < sc.r := hs.trans sc.projected_lt
  have hrU : sc.r < cfg.U := sc.deep_lt.trans sc.below
  have hegap : sc.e < B - cfg.ℓ * sc.r := by rw [sc.error_eq]; linarith [sc.transverse_gap]
  rcases hcmp hMatch α cfg' hv' L a s hL ha has hs2 (H ∘ φ) (ρ' ∘ φ)
    (fun k => β (φ k)) (fun k => n' (φ k)) (fun k => C (φ k))
    (fun k => tag (φ k)) (fun k => u (φ k)) (fun k => v (φ k)) (fun k => G (φ k))
    hw' B hB hBA hfit' sc.r sc.e sc.mesh sc.projected_lt hrU sc.transverse_gap sc.spatial_gap
    sc.error_pos hegap sc.mesh_slope (by rw [sc.mesh_eq]) with hc | hvl
  · exact Or.inl (candidates_of_reindex hψ.tendsto_atTop hc)
  · have hrows : RowParents cfg' sc.r := rowParents_of_velocityLists hRow cfg' hv' hr
      sc.error_pos sc.error_mesh sc.room hvl
    exact Or.inr ⟨sc.r, hr, hrU,
      rowParents_of_reindex (fun k => by linarith [hv.scale k]) hψ hrows⟩

end Submission.Obl.k4_narrow_projected_row_parents
