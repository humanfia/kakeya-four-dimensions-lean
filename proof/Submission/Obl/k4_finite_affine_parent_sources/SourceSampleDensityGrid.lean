import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionSample
import Submission.Obl.k4_finite_affine_parent_sources.SourceDensityMasks
import Submission.Obl.k4_finite_affine_parent_sources.ProfileNumerics

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- An arbitrary original finite grid can be indexed by a finite initial segment. -/
theorem exists_indexed_depth_grid (Q : Finset ℝ) :
    ∃ (G : ℕ) (r : Fin G → ℝ), (∀ j, r j ∈ Q) ∧ ∀ a ∈ Q, ∃ j, r j = a := by
  classical
  let e := Fintype.equivFin {a : ℝ // a ∈ Q}
  refine ⟨Fintype.card {a : ℝ // a ∈ Q}, fun j => (e.symm j).val,
    fun j => (e.symm j).property, ?_⟩
  intro a ha
  exact ⟨e ⟨a, ha⟩, by simp⟩

/-- The original selection mask supplies the pure-density mask on any enumeration. -/
theorem selectionMask_densMask {Nk L S τd τa Bw : ℝ} {f : ℝ → ℝ}
    {g : ℝ → Observation → ENNReal} {G : ℝ → Observation × (Fin 2 → ℤ) → ENNReal}
    {Qd Qa : Finset ℝ} {x : Incidence}
    (h : SelectionMask Nk L S τd τa f Bw g G Qd Qa x)
    {J : ℕ} (r : Fin J → ℝ) (hr : ∀ j, r j ∈ Qd) :
    x ∈ densMask g Bw Nk τd f r := by
  exact mem_iInter.mpr (fun j => h.1 (r j) (hr j))

/-- Rounding composed depths in the original grid pays only its prescribed mesh
and twice the original flat-profile error. -/
theorem selected_profile_cover {J : ℕ} {r : Fin J → ℝ} {Qd : Finset ℝ}
    {L hd r₀ unit T d₁ δ₀ : ℝ} {f : ℝ → ℝ}
    (hgrid : ∀ t, 0 ≤ t → t ≤ L → ∃ a ∈ Qd, t ≤ a ∧ a ≤ t + hd)
    (hQd : ∀ a ∈ Qd, 0 ≤ a ∧ a ≤ L)
    (honto : ∀ a ∈ Qd, ∃ j, r j = a)
    (hflat : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    (hr₀ : 0 ≤ r₀) (hr₀L : r₀ ≤ L)
    (hroom : ∀ s : ℝ, 0 ≤ s → s ≤ T → 0 ≤ r₀ + unit * L * s ∧ r₀ + unit * L * s ≤ L) :
    ∀ s : ℝ, 0 ≤ s → s ≤ T → ∃ j, r₀ + unit * L * s ≤ r j ∧
      r j ≤ r₀ + unit * L * s + hd ∧
      f r₀ + d₁ * (r j - r₀) - 2 * (δ₀ * L) ≤ f (r j) := by
  intro s hs0 hsT
  obtain ⟨a, ha, hlo, hhi⟩ := hgrid _ (hroom s hs0 hsT).1 (hroom s hs0 hsT).2
  obtain ⟨j, hj⟩ := honto a ha
  refine ⟨j, hj ▸ hlo, hj ▸ hhi, ?_⟩
  have hp := flat_profile_difference f d₁ L δ₀ hflat r₀ a hr₀ hr₀L (hQd a ha).1 (hQd a ha).2
  rw [hj]
  linarith [(abs_le.mp hp).1]

end

end Submission.Obl.k4_finite_affine_parent_sources
