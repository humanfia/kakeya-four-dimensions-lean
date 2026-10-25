-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.PathHistories
import Submission.Obl.k4_finite_affine_parent_sources.FiniteVectorVelocityCodes
import Submission.Obl.k4_finite_affine_parent_sources.ContinuousLikelihoodPreparation

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open scoped Classical

noncomputable section

local instance (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- The fixed-law likelihood window for the ACTUAL supplied path histories
and ORIGINAL planar velocity bins. All reference denominators are the
original source masses, and every later retained submeasure keeps the cap. -/
theorem path_original_likelihood_window
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sgrid : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sgrid δ₀ Mp Dp σ)
    (μ : Measure (Fin W × Incidence)) [IsProbabilityMeasure μ]
    (level : ℕ → ℕ) (hlevel : Monotone level) (hle : ∀ i, level i ≤ m - 1)
    (velocity : (Fin W × Incidence) → Fin 2 → ℝ) (hvelocity : Measurable velocity)
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ y ∂μ, ∀ e, |velocity y e| ≤ R)
    (J : ℕ) (hJ : 0 < J) (N : ℝ) (hN : 1 < N) :
    ∃ n : ℕ, 0 < n ∧ ∃ (code : (Fin W × Incidence) → Fin n)
      (terminal : Fin n → Option (Fin p.C))
      (palette : Fin n → (Fin 2 → {j : ℤ // j ∈ Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋})),
      Measurable code ∧
      (∀ᵐ y ∂μ, terminal (code y) = p.terminalCode m y ∧
        ∀ e, (palette (code y) e : ℤ) = ⌊velocity y e / δ⌋) ∧
      ∃ i < J, ∃ D : Set (Fin W × Incidence), MeasurableSet D ∧
        1 - Real.sqrt ((Real.log ((Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋).card ^ 2 + 1 : ℕ) /
          J + 1) / Real.log N) ≤ μ.real D ∧
        ∀ ρ : Measure (Fin W × Incidence), ρ ≤ μ.restrict D →
        ∀ (h : Option (Fin p.C)) z,
          ρ.real {y | (p.ancestorCode (level (i + 1)) (terminal (code y)), palette (code y)) = (h, z)} ≤
            N ^ Real.sqrt ((Real.log ((Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋).card ^ 2 + 1 : ℕ) /
              J + 1) / Real.log N) *
              μ.real {y | p.ancestorCode (level (i + 1)) (terminal (code y)) = h} *
              (μ.real {y | (p.ancestorCode (level i) (terminal (code y)), palette (code y)) =
                (p.ancestorCode (level i) h, z)} /
                μ.real {y | p.ancestorCode (level i) (terminal (code y)) = p.ancestorCode (level i) h}) := by
  classical
  obtain ⟨n, hn, code, terminal, palette, hcode, hdecode, hrep, hcard⟩ :=
    exists_history_vector_velocity_code 2 μ (p.terminalCode m) hp.measurable_terminalCode
      velocity hvelocity δ R hδ hR hbound
  let history : ℕ → Fin n → Option (Fin p.C) :=
    fun i e => p.ancestorCode (level i) (terminal e)
  let parent : ℕ → Option (Fin p.C) → Option (Fin p.C) := fun i => p.ancestorCode (level i)
  have hrefine : ∀ i e, history i e = parent i (history (i + 1) e) := by
    intro i e
    obtain ⟨y, -, hterminal, -⟩ := hrep e
    dsimp only [history, parent]
    rw [hterminal]
    exact hp.history_refines (hlevel (Nat.le_succ i)) (hle (i + 1)) y
  let M := (Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋).card ^ 2 + 1
  have hM : 1 ≤ M := by omega
  have hpalette : ∀ e,
      ((Finset.univ.filter (fun e' => 0 < μ.real (code ⁻¹' {e'}) ∧
        history 0 e' = history 0 e)).image palette).card ≤ M := by
    intro e
    exact (hcard _).trans (Nat.le_succ _)
  obtain ⟨i, hi, D, hD, hmass, hcap⟩ := original_balanced_likelihood_window
    μ code hcode history parent palette hrefine hM hJ hpalette N hN
  exact ⟨n, hn, code, terminal, palette, hcode, hdecode, i, hi, D, hD, hmass, hcap⟩

end

end Submission.Obl.k4_finite_affine_parent_sources
