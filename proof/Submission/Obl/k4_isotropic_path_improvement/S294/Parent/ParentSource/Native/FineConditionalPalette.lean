-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FineConditionalPalette, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FineConditionalPalette.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FineConditionalPalette.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FineConditionalPalette.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineOriginalCaps

/-! Each whole original selected fine history has its OWN fixed velocity
law. This gives exact original numerators, a full-prior cap with coefficient
one, and the intrinsic strip breadth. No continuous observation factorization
or common palette across different fine histories is asserted. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
  (F : PaletteFamily Q i stop a A θ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

/-- Full original fine-prior domination against the fixed fine-history
velocity law. There is no entropy domination coefficient A here. -/
theorem PaletteFamily.fine_original_conditional_velocity_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (b f : Fin p.C) (hb : F.active b) (hf : p.lev f = stop) (hfγ : p.γ f = p.γ b)
    (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : MeasurableSet V) :
    ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f V) ≤
      (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) *
        F.fineVelocityLaw b (F.coding.code f) V := by
  rw [← F.fine_velocity_original_mass hd hp hHE hH b hb f hf hfγ V hV, mul_comm]
  exact mul_le_mul' (F.fine_original_source_mass_le_full hd hp b f hf hfγ) le_rfl

/-- Measurable sets of the actual discrete control palette have the same
original full-prior cap. The palette is fixed for this original fine history. -/
theorem PaletteFamily.fine_original_conditional_palette_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (b f : Fin p.C) (hb : F.active b) (hf : p.lev f = stop) (hfγ : p.γ f = p.γ b)
    (V : Set (ℤ × ℤ)) (hV : MeasurableSet V) :
    ((d.ν k (p.γ b)).prod volume)
        (F.fineOriginalEvent b f ((fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) ⁻¹' V)) ≤
      (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) *
        ((F.fineVelocityLaw b (F.coding.code f)).map
          (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v)) V := by
  have hm : Measurable (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) :=
    measurable_euclidean_velocityPalette id measurable_id a
  rw [Measure.map_apply hm hV]
  exact F.fine_original_conditional_velocity_cap hd hp hHE hH b f hb hf hfγ _ (hV.preimage hm)

/-- A later incidence restriction does not change the reference palette or
its original numerator ceiling. Its denominator remains the full fine prior. -/
theorem PaletteFamily.restricted_fine_conditional_palette_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (b f : Fin p.C) (hb : F.active b) (hf : p.lev f = stop) (hfγ : p.γ f = p.γ b)
    (J : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : MeasurableSet V) :
    ((d.ν k (p.γ b)).prod volume) (J ∩ F.fineOriginalEvent b f V) ≤
      (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) *
        F.fineVelocityLaw b (F.coding.code f) V :=
  (measure_mono inter_subset_right).trans
    (F.fine_original_conditional_velocity_cap hd hp hHE hH b f hb hf hfγ V hV)

/-- Once an entry has a genuine full-prior floor, its SAME original law has
relative velocity caps against the earlier fine-history palette. -/
theorem PaletteFamily.fine_conditional_palette_after_full_floor (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (b f : Fin p.C) (hb : F.active b) (hf : p.lev f = stop) (hfγ : p.γ f = p.γ b)
    (J : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hJ : J ⊆ F.fineOriginalEvent b f univ)
    (δ : ENNReal) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞)
    (hfloor : δ * (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
      d.ν k (p.γ f) (p.A f)) ≤ ((d.ν k (p.γ b)).prod volume) J)
    (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : MeasurableSet V) :
    ((d.ν k (p.γ b)).prod volume) (J ∩ (p.normalizedVelocity b ⁻¹' V)) ≤
      δ⁻¹ * ((d.ν k (p.γ b)).prod volume) J * F.fineVelocityLaw b (F.coding.code f) V := by
  have href : ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f) ≤
      δ⁻¹ * ((d.ν k (p.γ b)).prod volume) J := by
    have h := mul_le_mul' (le_refl δ⁻¹) hfloor
    rw [← mul_assoc, ENNReal.inv_mul_cancel hδ0 hδtop, one_mul] at h
    exact h
  have hsub : J ∩ (p.normalizedVelocity b ⁻¹' V) ⊆ F.fineOriginalEvent b f V := by
    intro x hx
    exact ⟨(hJ hx.1).1, (hJ hx.1).2.1, hx.2⟩
  exact (measure_mono hsub).trans
    ((F.fine_original_conditional_velocity_cap hd hp hHE hH b f hb hf hfγ V hV).trans
      (mul_le_mul' href le_rfl))

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
