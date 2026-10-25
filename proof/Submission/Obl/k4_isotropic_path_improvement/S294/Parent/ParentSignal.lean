-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSignal, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSignal.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
-- Original-problem adapters from this LOT tree, o265, session x1030,
-- branch x1030, commit 381c4e41,
-- Submission/Obl/k4_staged_weak_breadth_discovery/ParentSignal.lean.
-- The general signal lemmas are now imported from accepted K4GlobalParentSignal.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface
import Submission.Lib.K4GlobalParentSignal

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace ParentSignal

export Submission.Lib.K4GlobalParentSignal
  (rate hasDerivAt_signal rate_eq_coefficients abs_rate_le signal_variation
   goodLines isClosed_goodLines measurableSet_goodLines regularEvents
   measurableSet_regularEvents restrict_goodLines hidden_curvature_global
   normalized_hidden_curvature globalCoefficients continuous_globalCoefficients
   measurable_globalCoefficients measurableSet_bounded_globalCoefficients
   global_signal global_rate globalCoefficients_bound)

section OriginalProblem

variable {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Ln}
    {E : (k : ℕ) → Fin (W k) → Set Ev}
    {P : (k : ℕ) → Fin (W k) → Po}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Ob → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Ob × (Fin 2 → ℤ)) → ENNReal}

/-- The global parent in the exact frozen problem has all the signal
bounds above under its unchanged original prior. -/
theorem original_parent_bounds (hpb : pb N K L d S η W ω ν E P B f g G)
    (k : ℕ) (w : Fin (W k)) :
    (P k w).totalDegree ≤ 2 ∧ IsProbabilityMeasure (ν k w) ∧
    (∀ᵐ l ∂ν k w, l ∈ goodLines (P k w) (K k) (B k w)) ∧
    (∀ᵐ l ∂ν k w, ∀ t ∈ Icc (0 : ℝ) 1, |rate (P k w) l t| ≤ 24 * K k) ∧
    (∀ z : Fin 4 → ℝ,
      |MvPolynomial.eval z (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (P k w)))| ≤
        K k * (B k w) ^ 2) := by
  rcases hpb with ⟨_, _, _, _, _, _, _, _, hrest⟩
  obtain ⟨M, D, hdata⟩ := hrest.1
  rcases (hdata k).2.2.2.1 w with
    ⟨hν, _, _, _, hdegree, _, _, _, _, _, _, hline, _⟩
  have hgood : ∀ᵐ l ∂ν k w, l ∈ goodLines (P k w) (K k) (B k w) := by
    filter_upwards [hline] with l hl
    intro t ht
    exact (hl t ht).2
  have : IsProbabilityMeasure (ν k w) := hν
  refine ⟨hdegree, hν, hgood, ?_, hidden_curvature_global (ν k w) hdegree hgood⟩
  filter_upwards [hgood] with l hl
  exact fun t ht => abs_rate_le hdegree (fun s hs => (hl s hs).1) ht

/-- Parent regularity can be imposed after any measurable or nonmeasurable
event selection without changing its original product law. -/
theorem original_restrict_goodLines (hpb : pb N K L d S η W ω ν E P B f g G)
    (k : ℕ) (w : Fin (W k)) (F : Set Ev) :
    ((ν k w).prod volume).restrict
        (F ∩ Prod.fst ⁻¹' goodLines (P k w) (K k) (B k w)) =
      ((ν k w).prod volume).restrict F :=
  restrict_goodLines (ν k w) (original_parent_bounds hpb k w).2.2.1 F

/-- The event derivative floor comes from the original counted law and
passes to every retained subset of the original event. -/
theorem original_counted_regularity (hpb : pb N K L d S η W ω ν E P B f g G)
    (k : ℕ) (w : Fin (W k)) (F : Set Ev) (hF : F ⊆ E k w) :
    0 < B k w ∧
      (∀ᵐ p ∂((ν k w).prod volume).restrict F,
        p ∈ regularEvents (P k w) (K k) (B k w)) := by
  rcases hpb with ⟨_, _, _, _, _, _, _, _, hrest⟩
  obtain ⟨M, D, hdata⟩ := hrest.1
  rcases (hdata k).2.2.2.1 w with
    ⟨_, hB, _, _, _, _, _, _, _, _, _, _, hreg⟩
  exact ⟨hB, hreg.filter_mono (ae_mono (Measure.restrict_mono hF le_rfl))⟩

/-- Whole-line parent bounds and the counted derivative floor can both be
made pointwise on a retained original event, with exactly zero mass loss. -/
theorem prepare_original_events (hpb : pb N K L d S η W ω ν E P B f g G)
    (k : ℕ) (w : Fin (W k)) (F : Set Ev) (hFm : MeasurableSet F) (hF : F ⊆ E k w) :
    ∃ F' : Set Ev, MeasurableSet F' ∧ F' ⊆ F ∧
      ((ν k w).prod volume).restrict F' = ((ν k w).prod volume).restrict F ∧
      ∀ p ∈ F', p.1 ∈ goodLines (P k w) (K k) (B k w) ∧
        p ∈ regularEvents (P k w) (K k) (B k w) := by
  let F' := regularEvents (P k w) (K k) (B k w) ∩
    (F ∩ Prod.fst ⁻¹' goodLines (P k w) (K k) (B k w))
  have hregMeas := measurableSet_regularEvents (P k w) (K k) (B k w)
  refine ⟨F', hregMeas.inter
    (hFm.inter ((measurableSet_goodLines _ _ _).preimage measurable_fst)),
    (fun _ hp => hp.2.1), ?_, fun _ hp => ⟨hp.2.2, hp.1⟩⟩
  change ((ν k w).prod volume).restrict
    (regularEvents (P k w) (K k) (B k w) ∩
      (F ∩ Prod.fst ⁻¹' goodLines (P k w) (K k) (B k w))) = _
  rw [← Measure.restrict_restrict hregMeas, original_restrict_goodLines hpb]
  exact Measure.restrict_eq_self_of_ae_mem (original_counted_regularity hpb k w F hF).2

end OriginalProblem

end ParentSignal

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
