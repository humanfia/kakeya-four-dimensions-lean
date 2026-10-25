-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeParentCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeParentCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeParentCaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeParentCaps.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeParentCaps.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeWindow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.BallCaps

/-! Fixed reference angular caps pass to heavy current coarse posteriors.
Their omission budget uses the original full-assignment/time budget. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

noncomputable def PreparedAngularPath.currentParentLaw (b : Fin p.C) :
    Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  (d.μ k (p.γ b)).restrict (Q.residual (p.γ b) ∩ p.F b)

theorem PreparedAngularPath.current_parent_eq_original (hHE : ∀ w, H w ⊆ d.E k w)
    (hF : ∀ b, MeasurableSet (p.F b)) (b : Fin p.C) :
    Q.currentParentLaw b = ((d.ν k (p.γ b)).prod volume).restrict (Q.residual (p.γ b) ∩ p.F b) := by
  have hm : MeasurableSet (Q.residual (p.γ b) ∩ p.F b) :=
    (Q.residual_measurable (p.γ b)).inter (hF b)
  have hs : Q.residual (p.γ b) ∩ p.F b ⊆ d.E k (p.γ b) :=
    inter_subset_left.trans ((Q.residual_subset (p.γ b)).trans
      ((Q.base_subset (p.γ b)).trans (hHE (p.γ b))))
  dsimp only [currentParentLaw, ProblemData.μ]
  rw [Measure.restrict_restrict hm, inter_eq_left.mpr hs]

theorem PreparedAngularPath.current_parent_cond_eq_original (hHE : ∀ w, H w ⊆ d.E k w)
    (hF : ∀ b, MeasurableSet (p.F b)) (b : Fin p.C) :
    ProbabilityTheory.cond (Q.currentParentLaw b) univ =
      ProbabilityTheory.cond ((d.ν k (p.γ b)).prod volume) (Q.residual (p.γ b) ∩ p.F b) := by
  rw [Q.current_parent_eq_original hHE hF b, cond_restrict_univ]

/-- Even the prepared reference is charged to the FULL original old
assignment and its old time block. -/
theorem PreparedAngularPath.reference_mass_le_full (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) :
    d.pathAngularReference k p Q.base Q.mask b univ ≤
      ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) * d.ν k (p.γ b) (p.A b) := by
  let := (hd.weights k).2.2 (p.γ b)
  have hsub : d.pathPacketEvents k p Q.base (p.γ b) b ⊆ p.A b ×ˢ p.block b := by
    intro z hz
    have hzb : z ∈ p.F b := by simpa using hz.2
    have hFz := (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.2.2.2.1 z hzb
    exact ⟨hFz.2.1, hFz.2.2.1⟩
  calc
    _ ≤ ((d.μ k (p.γ b)).restrict (d.pathPacketEvents k p Q.base (p.γ b) b)) univ :=
      Measure.restrict_le_self univ
    _ = d.μ k (p.γ b) (d.pathPacketEvents k p Q.base (p.γ b) b) := Measure.restrict_apply_univ _
    _ ≤ ((d.ν k (p.γ b)).prod volume) (d.pathPacketEvents k p Q.base (p.γ b) b) :=
      Measure.restrict_le_self _
    _ ≤ ((d.ν k (p.γ b)).prod volume) (p.A b ×ˢ p.block b) := measure_mono hsub
    _ = _ := by rw [Measure.prod_prod, p.volume_block]; ring

theorem PreparedAngularPath.reference_level_budget (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (i : ℕ) :
    (∑ b, (if p.lev b = i then ENNReal.ofReal (d.ω k (p.γ b)) else 0) *
      d.pathAngularReference k p Q.base Q.mask b univ) ≤ 1 := by
  classical
  obtain ⟨hω, hsum, hν⟩ := hd.weights k
  apply le_trans _ (hp.full_reference_mass_le_one hν hω hsum i)
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : p.lev b = i
  · simp only [ite_eq_left hb]
    exact mul_le_mul le_rfl (by simpa only [hb] using Q.reference_mass_le_full hd hp b)
      zero_le zero_le
  · simp only [ite_eq_right hb, zero_mul, le_refl]

/-- The actual native current posterior has a normalized velocity ball cap
as soon as it retains the stated fraction of the SAME old parent reference. -/
theorem PreparedAngularPath.parent_ball_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (b : Fin p.C) (t : T)
    {θ : ENNReal} (hθ : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hcurrent : Q.currentParentLaw b univ ≠ 0)
    (hfloor : θ * d.pathAngularReference k p Q.base Q.mask b univ ≤ Q.currentParentLaw b univ)
    {r : ℝ} (hscale : p.κ * r ≤ δ (d.N k) (u t))
    (center : EuclideanSpace ℝ (Fin 2)) :
    ProbabilityTheory.cond ((d.ν k (p.γ b)).prod volume) (Q.residual (p.γ b) ∩ p.F b)
      {z | ‖((2 : ℝ) ^ p.T (p.lev b))⁻¹ •
        Matrix.toEuclideanLin (p.Q b)⁻¹ (v z.1 - p.u b) - center‖ ≤ r} ≤
      100 * ((ENNReal.ofReal (d.N k ^ (-d.S * u t + 2 * τ)) *
        (angularPreparationEpsilon m p.κ)⁻¹) * θ⁻¹) := by
  let μcur := Q.currentParentLaw b
  have htop : μcur univ ≠ ∞ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞)
    change ((d.μ k (p.γ b)).restrict (Q.residual (p.γ b) ∩ p.F b)) univ ≤ 1
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (subset_univ _)).trans (hd.selected_incidence_mass_le_one k _)
  have hbin (i : Fin 2 → ℤ) : ProbabilityTheory.cond μcur univ
      {q | (fun j => ⌊v q.1 j / δ (d.N k) (u t)⌋) = i} ≤
      (ENNReal.ofReal (d.N k ^ (-d.S * u t + 2 * τ)) *
        (angularPreparationEpsilon m p.κ)⁻¹) * θ⁻¹ :=
    conditional_cap_of_reference_floor μcur (d.pathAngularReference k p Q.base Q.mask b)
      (Q.parent_domination b) hθ hθtop hcurrent htop hfloor _ (Q.angular_cap t b i)
  have hball := hp.normalized_velocity_ball_cap b (ProbabilityTheory.cond μcur univ)
    (a := δ (d.N k) (u t)) (by unfold δ; positivity) hscale _ hbin center
  have hF (a : Fin p.C) : MeasurableSet (p.F a) :=
    (hp.2.2.2.2.2.2.2 a).2.2.2.2.2.2.2.2.2.1
  dsimp only [μcur] at hball
  rw [Q.current_parent_cond_eq_original hHE hF b] at hball
  exact hball

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
