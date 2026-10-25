-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PathAngularPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PathAngularPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PathAngularPreparation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PathAngularPreparation.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/PathAngularPreparation.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.AngularPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.TerminalLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Problem
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.IncidenceTransport

/-! Original angular density ceilings yield fixed parent angular-bin caps.
Every omission is charged to the terminal observation's old packet list. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem angular_ratio_of_density_bounds {N F S u τ : ℝ} (hN : 0 < N)
    {g G : ENNReal} (hg : ENNReal.ofReal (N ^ (-F - τ)) ≤ g)
    (hG : G ≤ ENNReal.ofReal (N ^ (-F - S * u + τ))) :
    G ≤ ENNReal.ofReal (N ^ (-S * u + 2 * τ)) * g := by
  calc
    G ≤ ENNReal.ofReal (N ^ (-F - S * u + τ)) := hG
    _ = ENNReal.ofReal (N ^ (-S * u + 2 * τ)) *
        ENNReal.ofReal (N ^ (-F - τ)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
      congr 2
      ring
    _ ≤ _ := mul_le_mul le_rfl hg zero_le zero_le

theorem ProblemData.Valid.selected_incidence_finite {d : ProblemData} (h : d.Valid)
    (k : ℕ) (w : Fin (d.W k)) : IsFiniteMeasure (d.μ k w) := by
  let := (h.weights k).2.2 w
  rcases h with ⟨_, _, _, _, _, _, _, _, hf, _⟩
  obtain ⟨M, D, hf⟩ := hf
  have hE := (hf k).2.2.2.1 w
  exact Submission.Obl.k4_dyadic_crop_affine_laws.Framework.finite_selected_incidence
    (d.ν k w) (d.E k w) hE.2.2.2.2.2.2.2.2.1

/-- Simultaneous fixed-parent angular caps for the frozen path. `H` may be
any previously cleaned residual; its original measure and weights are kept. -/
theorem ProblemData.Valid.prepare_path_angular_family_of_list {T : Type*}
    {d : ProblemData} (hd : d.Valid) (k : ℕ) (p : PathData (d.W k))
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (u : T → ℝ) (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L)
    (τ : ℝ) (H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hH : ∀ w, MeasurableSet (H w))
    (lst : Fin (d.W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin p.C))
    (hlist : ∀ w o, ((lst w o).card : ℝ) ≤ m * p.κ)
    (hknown : ∀ w b q, q ∈ H w ∩ (if p.γ b = w then p.F b else ∅) →
      b ∈ lst w (obs (d.B k w) (δ (d.N k) d.L) q))
    (hpure : ∀ w q, q ∈ H w →
      ENNReal.ofReal (d.N k ^ (-d.f d.L - τ)) ≤
        d.g k w d.L (obs (d.B k w) (δ (d.N k) d.L) q))
    (hangular : ∀ t w q, q ∈ H w →
      d.G k w (u t) (d.angularObs (u t) k w q) ≤
        ENNReal.ofReal (d.N k ^ (-d.f d.L - d.S * u t + τ)))
    (ε : ENNReal) (hε : ε ≠ 0) (hεtop : ε ≠ ∞) (w : Fin (d.W k)) :
    ∃ A : Fin p.C → Set (EuclideanSpace ℝ (Fin 3) × ℤ),
      (∀ b, MeasurableSet (A b)) ∧
      (∑ b, (d.μ k w).restrict (H w ∩ (if p.γ b = w then p.F b else ∅))
        {q | obs (d.B k w) (δ (d.N k) d.L) q ∉ A b}) ≤
          ε * ENNReal.ofReal (m * p.κ) * d.μ k w univ ∧
      ∀ t b i, (((d.μ k w).restrict (H w ∩ (if p.γ b = w then p.F b else ∅))).restrict
          (obs (d.B k w) (δ (d.N k) d.L) ⁻¹' A b))
          {q | (fun j => ⌊v q.1 j / δ (d.N k) (u t)⌋) = i} ≤
        (ENNReal.ofReal (d.N k ^ (-d.S * u t + 2 * τ)) * ε⁻¹) *
          (((d.μ k w).restrict (H w ∩ (if p.γ b = w then p.F b else ∅))).restrict
            (obs (d.B k w) (δ (d.N k) d.L) ⁻¹' A b)) univ := by
  classical
  let := hd.selected_incidence_finite k w
  have hN : 1 ≤ d.N k := le_trans (by norm_num) (hd.1 k)
  let obsL := obs (d.B k w) (δ (d.N k) d.L)
  have hobs : Measurable obsL :=
    Submission.Obl.k4_dk4_smoothed_problem.Framework.measurable_pureObservation _ _
  let F : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
    fun b => H w ∩ (if p.γ b = w then p.F b else ∅)
  have hF (b : Fin p.C) : MeasurableSet (F b) := by
    apply (hH w).inter
    split
    · exact (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
    · exact MeasurableSet.empty
  have hpred : ∀ b q, q ∈ F b → b ∈ lst w (obsL q) := hknown w
  let ang : T → ((ℕ × (Fin 6 → ℝ)) × ℝ) → (Fin 2 → ℤ) :=
    fun t q j => ⌊v q.1 j / δ (d.N k) (u t)⌋
  have hang (t : T) : Measurable (ang t) := by
    exact measurable_snd.comp
      (Submission.Obl.k4_dk4_smoothed_problem.Framework.measurable_angularObservation
        (d.B k w) (δ (d.N k) d.L) (δ (d.N k) (u t)))
  have hL : 0 < d.L := hd.2.2.2.1
  have hg := hd.2.2.2.2.2.2.2.2.2.1 k w d.L hL.le le_rfl
  have hG := hd.2.2.2.2.2.2.2.2.2.2.1
  exact prepare_arbitrary_listed_angular_family (d.μ k w) (volume.prod Measure.count)
    obsL hobs F hF (lst w) (m * p.κ) (hlist w)
    (d.g k w d.L) hg.1 hg.2 hpred ang hang (fun t => d.G k w (u t))
    (fun t => (hG k w (u t) (hu t).1 (hu t).2).1)
    (fun t => ENNReal.ofReal (d.N k ^ (-d.S * u t + 2 * τ)))
    (fun t => (hG k w (u t) (hu t).1 (hu t).2).2)
    (fun t b q hq => angular_ratio_of_density_bounds (lt_of_lt_of_le zero_lt_one hN)
      (hpure w q hq.1) (hangular t w q hq.1)) ε hε hεtop


/-- Simultaneous fixed-parent angular caps for the frozen path. `H` may be
any previously cleaned residual; its original measure and weights are kept. -/
theorem ProblemData.Valid.prepare_path_angular_family {T : Type*}
    {d : ProblemData} (hd : d.Valid) (k : ℕ) (p : PathData (d.W k))
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hrL : ∀ i, i < m → p.r i ≤ d.L)
    (u : T → ℝ) (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L)
    (τ : ℝ) (H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hH : ∀ w, MeasurableSet (H w))
    (hpure : ∀ w q, q ∈ H w →
      ENNReal.ofReal (d.N k ^ (-d.f d.L - τ)) ≤
        d.g k w d.L (obs (d.B k w) (δ (d.N k) d.L) q))
    (hangular : ∀ t w q, q ∈ H w →
      d.G k w (u t) (d.angularObs (u t) k w q) ≤
        ENNReal.ofReal (d.N k ^ (-d.f d.L - d.S * u t + τ)))
    (ε : ENNReal) (hε : ε ≠ 0) (hεtop : ε ≠ ∞) (w : Fin (d.W k)) :
    ∃ A : Fin p.C → Set (EuclideanSpace ℝ (Fin 3) × ℤ),
      (∀ b, MeasurableSet (A b)) ∧
      (∑ b, (d.μ k w).restrict (H w ∩ (if p.γ b = w then p.F b else ∅))
        {q | obs (d.B k w) (δ (d.N k) d.L) q ∉ A b}) ≤
          ε * ENNReal.ofReal (m * p.κ) * d.μ k w univ ∧
      ∀ t b i, (((d.μ k w).restrict (H w ∩ (if p.γ b = w then p.F b else ∅))).restrict
          (obs (d.B k w) (δ (d.N k) d.L) ⁻¹' A b))
          {q | (fun j => ⌊v q.1 j / δ (d.N k) (u t)⌋) = i} ≤
        (ENNReal.ofReal (d.N k ^ (-d.S * u t + 2 * τ)) * ε⁻¹) *
          (((d.μ k w).restrict (H w ∩ (if p.γ b = w then p.F b else ∅))).restrict
            (obs (d.B k w) (δ (d.N k) d.L) ⁻¹' A b)) univ := by
  have hN : 1 ≤ d.N k := le_trans (by norm_num) (hd.1 k)
  have hknown : ∀ w b q, q ∈ H w ∩ (if p.γ b = w then p.F b else ∅) →
      b ∈ terminalPacketList p (d.N k) d.L m w (obs (d.B k w) (δ (d.N k) d.L) q) := by
    intro w b q hq
    by_cases hb : p.γ b = w
    · have hqb : q ∈ p.F b := by simpa only [ite_eq_left hb] using hq.2
      simpa only [hb] using hp.terminalPacketList_mem hN hrL b q hqb
    · simp only [ite_eq_right hb, mem_inter_iff, mem_empty_iff_false, and_false] at hq
  exact hd.prepare_path_angular_family_of_list k p κ₁ m s δ₀ Mp Dp σ hp u hu τ H hH
    (terminalPacketList p (d.N k) d.L m)
    (terminalPacketList_card p (d.N k) d.L m hp.2.2.2.2.2.1) hknown
    hpure hangular ε hε hεtop w

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
