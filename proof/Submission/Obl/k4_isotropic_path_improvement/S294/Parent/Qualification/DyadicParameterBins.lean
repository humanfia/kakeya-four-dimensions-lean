-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DyadicParameterBins, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/DyadicParameterBins.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/DyadicParameterBins.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/DyadicParameterBins.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterZoom
import Submission.Lib.K4XInterface.Basic

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory

noncomputable section

def parameterCode {n : ℕ} (w : ℝ) (c : Fin n → ℝ) : Fin n → ℤ :=
  fun i => ⌊c i / w⌋

theorem measurable_parameterCode {n : ℕ} (w : ℝ) : Measurable (parameterCode (n := n) w) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_pi_apply i : Measurable (fun c : Fin n → ℝ => c i)).div_const w).floor

def dyadicParameterWidth (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

theorem dyadicParameterWidth_pos (n : ℕ) : 0 < dyadicParameterWidth n := by
  dsimp [dyadicParameterWidth]
  positivity

def coarsenParameterCode {m : ℕ} (n : ℕ) (q : Fin m → ℤ) : Fin m → ℤ :=
  fun i => q i / (2 : ℤ) ^ n

/-- Exact dyadic alignment, imported from the accepted floor-quotient
identity. No partial fine bin crosses an old parameter-bin boundary. -/
theorem coarsen_parameterCode {m : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (c : Fin m → ℝ) :
    coarsenParameterCode n (parameterCode (ρ * dyadicParameterWidth n) c) =
      parameterCode ρ c := by
  funext i
  have hreal : (c i / (ρ * dyadicParameterWidth n)) / (2 : ℝ) ^ n = c i / ρ := by
    dsimp [dyadicParameterWidth]
    field_simp
  have h := Submission.Lib.K4XInterface.floor_div_two_pow
    (c i / (ρ * dyadicParameterWidth n)) n
  rw [hreal] at h
  exact h.symm

/-- One actual occurrence in an old world certifies that its whole
aligned fine parameter bin belongs to that SAME original world. -/
theorem original_parameter_fiber_subset {Λ : Type*} {m : ℕ}
    (c : Λ → Fin m → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (coarse fine : Fin m → ℤ) (witness : Λ)
    (hcoarse : parameterCode ρ (c witness) = coarse)
    (hfine : parameterCode (ρ * dyadicParameterWidth n) (c witness) = fine) :
    {l | parameterCode (ρ * dyadicParameterWidth n) (c l) = fine} ⊆
      {l | parameterCode ρ (c l) = coarse} := by
  have hparent : coarsenParameterCode n fine = coarse := by
    rw [← hfine, coarsen_parameterCode ρ hρ, hcoarse]
  intro l hl
  change parameterCode ρ (c l) = coarse
  rw [← coarsen_parameterCode ρ hρ n (c l), hl, hparent]

theorem exists_dyadicParameterWidth (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ n : ℕ, r / 2 ≤ dyadicParameterWidth n ∧ dyadicParameterWidth n ≤ r := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n + 1, ?_, ?_⟩
  · have hpow : (1 / 2 : ℝ) ^ (n + 1) = dyadicParameterWidth (n + 1) := by
      simp [dyadicParameterWidth, inv_pow]
    rw [← hpow, pow_succ]
    linarith
  · simpa [dyadicParameterWidth, inv_pow] using hn.le

def parameterLevel (r : ℝ) : ℕ :=
  if h : 0 < r ∧ r ≤ 1 then (exists_dyadicParameterWidth r h.1 h.2).choose else 0

theorem parameterLevel_width (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    r / 2 ≤ dyadicParameterWidth (parameterLevel r) ∧
      dyadicParameterWidth (parameterLevel r) ≤ r := by
  unfold parameterLevel
  rw [dif_pos ⟨hr, hr1⟩]
  exact (exists_dyadicParameterWidth r hr hr1).choose_spec

/-- The actual pieces are aligned ORIGINAL coefficient bins. Their
geometry is measured only after the fixed original parameter zoom. -/
def zoomParameterPiece {Λ : Type*} (ρ : ℝ) (c : Λ → Fin 7 → ℝ) (r : ℝ) (l : Λ) :
    Fin 7 → ℤ := parameterCode (ρ * dyadicParameterWidth (parameterLevel r)) (c l)

theorem measurable_zoomParameterPiece {Λ : Type*} [MeasurableSpace Λ]
    (ρ : ℝ) {c : Λ → Fin 7 → ℝ} (hc : Measurable c) (r : ℝ) :
    Measurable (zoomParameterPiece ρ c r) := (measurable_parameterCode _).comp hc

theorem zoomParameterPiece_diameter {Λ : Type*} (ρ : ℝ) (hρ : 0 < ρ)
    (c : Λ → Fin 7 → ℝ) (center : Fin 7 → ℝ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    {l l' : Λ} (h : zoomParameterPiece ρ c r l = zoomParameterPiece ρ c r l') :
    ‖zoomCoefficients ρ center (c l) - zoomCoefficients ρ center (c l')‖ ≤ r := by
  exact (zoom_piece_diameter ρ (dyadicParameterWidth (parameterLevel r)) hρ
    (dyadicParameterWidth_pos _) center (c l) (c l') (fun i => congrFun h i)).trans
      (parameterLevel_width r hr hr1).2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
