-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeWindow, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeWindow.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeWindow.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeWindow.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeWindow.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePreparation

/-! The actual angular-prepared residual supplies one fixed probability law
and a good packet-history/physical-velocity likelihood window. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)

theorem PreparedAngularPath.world_mass_le_one (hd : d.Valid) (hHE : ∀ w, H w ⊆ d.E k w)
    (w : Fin (d.W k)) : ((d.ν k w).prod volume) (Q.residual w) ≤ 1 := by
  have hs : Q.residual w ⊆ d.E k w :=
    (Q.residual_subset w).trans ((Q.base_subset w).trans (hHE w))
  calc
    _ = d.μ k w (Q.residual w) := (d.μ_apply_eq k w (Q.residual_measurable w) hs).symm
    _ ≤ d.μ k w univ := measure_mono (subset_univ _)
    _ ≤ 1 := hd.selected_incidence_mass_le_one k w

theorem PreparedAngularPath.probability (hd : d.Valid) (hHE : ∀ w, H w ⊆ d.E k w)
    (hκ : 0 < p.κ) : IsProbabilityMeasure Q.law := by
  obtain ⟨hω, hsum, _⟩ := hd.weights k
  exact preparedResidualLaw_probability (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
    hω hsum (Q.world_mass_le_one hd hHE) (by positivity) Q.original_mass

theorem PreparedAngularPath.good_velocity_window (hd : d.Valid)
    (hHE : ∀ w, H w ⊆ d.E k w) (hκ : 0 < p.κ) (hF : ∀ b, MeasurableSet (p.F b))
    (q C : ℕ) (hC : 1 ≤ C) (A : Finset ℕ)
    (hA : ∀ j ∈ A, j < q ∧ j + C ≤ q)
    (σvel ue τent α : ℝ) (hσvel : 0 ≤ σvel) (hue : 0 ≤ ue)
    (hτent : 0 ≤ τent) (hα : 0 ≤ α) (hK : d.K k ≤ d.N k ^ σvel)
    (hbudget : (C : ℝ) * (2 * Real.log 10 + 2 * (σvel + ue) * Real.log (d.N k)) + (q : ℝ) <
      (A.card : ℝ) * (τent * Real.log (d.N k) * α)) :
    ∃ i ∈ A, Submission.Obl.k4_matching_cofinal_palette_selection.badMass
      Q.law (labelledSupport Q.residual) (finitePacketHistory p.lev p.γ p.F)
      (fun z => velocityPalette (d.N k ^ (-ue)) (fun j => v z.2.1 j))
      C i (d.N k ^ τent) ≤ ENNReal.ofReal α := by
  obtain ⟨hω, hsum, _⟩ := hd.weights k
  have hVm : Measurable (fun z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) =>
      fun j => v z.2.1 j) := by
    apply Measurable.of_eval
    intro j
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).comp
      Submission.Obl.k4_dk4_smoothed_problem.Framework.continuous_planarVelocity).measurable.comp
        (measurable_fst.comp measurable_snd)
  exact prepared_histories_good_velocity_window (fun w => (d.ν k w).prod volume)
    (d.ω k) Q.residual hω hsum (Q.world_mass_le_one hd hHE) Q.residual_measurable
    (by positivity) Q.original_mass p.lev p.γ p.F hF _ hVm q C hC A hA
    (d.N k) σvel ue τent α (le_trans (by norm_num) (hd.1 k)) hσvel hue hτent hα
    (fun w z hz j => (Q.velocity_bound w z (Q.residual_subset w hz) j).trans hK) hbudget

end Certificate

/-- Uniform preparation and entropy-window selection from EXACTLY the frozen
path and residual assumptions, under one original prepared law throughout. -/
theorem ProblemData.Valid.prepare_native_angular_window_exact {T : Type*} [Fintype T]
    {d : ProblemData} (hd : d.Valid) (κ₁ : ℝ) (m : ℕ) (hm : 0 < m)
    (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (u : T → ℝ)
    (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L) (τ : ℝ) (hτ : 0 < τ)
    (q C : ℕ) (hC : 1 ≤ C) (A : Finset ℕ) (hA : ∀ j ∈ A, j < q ∧ j + C ≤ q)
    (σvel ue τent α : ℝ) (hσvel : 0 < σvel) (hue : 0 ≤ ue)
    (hτent : 0 ≤ τent) (hα : 0 ≤ α)
    (hgap : 2 * (C : ℝ) * (σvel + ue) < (A.card : ℝ) * (τent * α)) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      ∃ Q : PreparedAngularPath d k p m H u τ, ∃ i ∈ A,
        Submission.Obl.k4_matching_cofinal_palette_selection.badMass
          Q.law (labelledSupport Q.residual) (finitePacketHistory p.lev p.γ p.F)
          (fun z => velocityPalette (d.N k ^ (-ue)) (fun j => v z.2.1 j))
          C i (d.N k ^ τent) ≤ ENNReal.ofReal α := by
  obtain ⟨σ, hσ, hprep⟩ := hd.prepare_native_angular_path_exact κ₁ m hm s δ₀ Mp Dp u hu τ hτ
  have hK := hd.2.2.1.2 σvel hσvel
  have hbudget := eventually_velocity_window_budget d.N hd.tendsto A q C σvel ue τent α hgap
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hprep, hK, hbudget] with k hprepk hKk hbudgetk
  intro p hp H hH hcover hmass
  obtain ⟨Q⟩ := hprepk p hp H hH hcover hmass
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  obtain ⟨i, hi, hgood⟩ := Q.good_velocity_window hd (hp.residual_subset_event H hcover)
    (lt_of_lt_of_le zero_lt_one hp.1) hF q C hC A hA σvel ue τent α hσvel.le hue hτent hα hKk hbudgetk
  exact ⟨Q, i, hi, hgood⟩


/-- Uniform preparation and entropy-window selection from EXACTLY the frozen
path and residual assumptions, under one original prepared law throughout. -/
theorem ProblemData.Valid.prepare_native_angular_window {T : Type*} [Fintype T]
    {d : ProblemData} (hd : d.Valid) (κ₁ : ℝ) (m : ℕ) (hm : 0 < m)
    (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (u : T → ℝ)
    (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L) (τ : ℝ) (hτ : 0 < τ)
    (q C : ℕ) (hC : 1 ≤ C) (A : Finset ℕ) (hA : ∀ j ∈ A, j < q ∧ j + C ≤ q)
    (σvel ue τent α : ℝ) (hσvel : 0 < σvel) (hue : 0 ≤ ue)
    (hτent : 0 ≤ τent) (hα : 0 ≤ α)
    (hgap : 2 * (C : ℝ) * (σvel + ue) < (A.card : ℝ) * (τent * α)) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
      (∀ i, i < m → p.r i ≤ d.L) →
      ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      ∃ Q : PreparedAngularPath d k p m H u τ, ∃ i ∈ A,
        Submission.Obl.k4_matching_cofinal_palette_selection.badMass
          Q.law (labelledSupport Q.residual) (finitePacketHistory p.lev p.γ p.F)
          (fun z => velocityPalette (d.N k ^ (-ue)) (fun j => v z.2.1 j))
          C i (d.N k ^ τent) ≤ ENNReal.ofReal α := by
  obtain ⟨σ, hσ, hk⟩ := hd.prepare_native_angular_window_exact κ₁ m hm s δ₀ Mp Dp u hu τ hτ
    q C hC A hA σvel ue τent α hσvel hue hτent hα hgap
  refine ⟨σ, hσ, hk.mono ?_⟩
  intro k hk p hp _ H hH hcover hmass
  exact hk p hp H hH hcover hmass

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
