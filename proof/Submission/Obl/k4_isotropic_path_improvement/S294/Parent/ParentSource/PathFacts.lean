-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PathFacts, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PathFacts.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PathFacts.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PathFacts.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Interface
import Submission.Obl.k4_fixed_menu_density_pruning.ParentIncidences
import Submission.Lib.K4XInterface.Basic

/-!
# Consequences of the exact frozen path

Terminal residual incidences remain in their actual ancestors, under the
same world label. Observation lists can be read from the terminal observation.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Event := Line × ℝ
abbrev BaseObservation := EuclideanSpace ℝ (Fin 3) × ℤ

section Path

variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    {κ : ℝ} {C : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Event}
    {lst : ℕ → Fin W → BaseObservation → Finset (Fin C)}
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ
      C lev par γ j c u Q R A F lst)

include hp

/-- The line and event sets of every frozen path packet are measurable. -/
theorem path_packet_measurable (b : Fin C) :
    MeasurableSet (A b) ∧ MeasurableSet (F b) := by
  have hch := (hp.2.2.2.2.2.2.2 b).2.2
  exact ⟨hch.2.2.2.2.2.2.1, hch.2.2.2.2.2.2.2.1⟩

/-- Frozen incidences belong to their packet's lines and closed time block. -/
theorem path_packet_support (b : Fin C) {p : Event} (h : p ∈ F b) :
    p ∈ E (γ b) ∧ p.1 ∈ A b ∧
    p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
      (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
    B (γ b) / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv 3 (R b))| := by
  rcases (hp.2.2.2.2.2.2.2 b).2.2 with ⟨_, _, _, _, _, _, _, _, _, _, hF, _⟩
  exact hF p h

/-- Every terminal residual incidence lies in a packet at each earlier level,
with its original world label. -/
theorem path_residual_level_cover
    {H : Fin W → Set Event}
    (hH : ∀ w, H w ⊆ {p | ∃ b, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b})
    (i : ℕ) (hi : i < m) (w : Fin W) :
    H w ⊆ {p | ∃ b, lev b = i ∧ γ b = w ∧ p ∈ F b} := by
  have hparents : ∀ b, 0 < lev b →
      lev (par b) + 1 = lev b ∧ γ (par b) = γ b ∧
      A b ⊆ A (par b) ∧ F b ⊆ F (par b) := by
    intro b hb
    rcases (hp.2.2.2.2.2.2.2 b).2.2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hex⟩
    have hpar := hex.2.2.2.2.2 hb
    exact ⟨hpar.1, hpar.2.1, hpar.2.2.1, hpar.2.2.2.1⟩
  have hlev : ∀ b, 0 < lev b → lev (par b) + 1 = lev b :=
    fun b hb => (hparents b hb).1
  have hγ : ∀ b, 0 < lev b → γ (par b) = γ b :=
    fun b hb => (hparents b hb).2.1
  have hF : ∀ b, 0 < lev b → F b ⊆ F (par b) :=
    fun b hb => (hparents b hb).2.2.2
  intro p h
  obtain ⟨b, hb, hw, hpb⟩ := hH w h
  have hib : i ≤ lev b := by omega
  obtain ⟨haw, hsub⟩ :=
    k4_fixed_menu_density_pruning.forestAncestor_incidence_subset
      lev par γ F hlev hγ hF b i hib
  exact ⟨forestAncestor lev par b i, forestAncestor_level hlev b i hib,
    haw.trans hw, hsub hpb⟩

/-- Coarse path lists may be evaluated using only a terminal observation. -/
theorem path_list_from_terminal (hN : 1 ≤ Nk) (b : Fin C)
    (hr : 0 ≤ r (lev b)) (hrL : r (lev b) ≤ L) {p : Event} (h : p ∈ F b) :
    b ∈ lst (lev b) (γ b)
      (Submission.Lib.K4XInterface.coarsenObs
        (Submission.Lib.K4XInterface.depthIdx Nk L -
          Submission.Lib.K4XInterface.depthIdx Nk (r (lev b)))
        (obs (B (γ b)) (δ Nk L) p)) := by
  have heq := Submission.Lib.K4XInterface.gobs_coarsen hN hr hrL (B (γ b)) p
  change obs (B (γ b)) (δ Nk (r (lev b))) p =
    Submission.Lib.K4XInterface.coarsenObs
      (Submission.Lib.K4XInterface.depthIdx Nk L -
        Submission.Lib.K4XInterface.depthIdx Nk (r (lev b)))
      (obs (B (γ b)) (δ Nk L) p) at heq
  rw [← heq]
  rcases (hp.2.2.2.2.2.2.2 b).2.2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hex⟩
  exact hex.2.2.2.2.1 p h

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
