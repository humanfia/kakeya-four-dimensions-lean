-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ZoomResidualPalettes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ZoomResidualPalettes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ZoomResidualPalettes.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ZoomResidualPalettes.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ResidualLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic
import Submission.Lib.K4CommonLocalChoice
import Submission.Obl.k4_scalar_heavy_intercept_selection.InterceptLists
import Submission.Lib.K4QuadraticSheets.JetBins


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set
open scoped BigOperators

noncomputable section

/-- Full coefficient diameter controls the actual residual. No
choice of unshifted coefficient bins in the new zoom is needed. -/
theorem residual_difference_of_coefficient_diameter (c c' : Fin 7 → ℝ)
    (F : ℝ → Fin 2 → ℝ) (t u s ρ K : ℝ) (hs : 0 ≤ s) (hρs : ρ ≤ s) (hK : 1 ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hgap : |t-u| ≤ s)
    (hdiam : ∀ i, |c i - c' i| ≤ s) (hc : ∀ i, |c i| ≤ K) (hc' : ∀ i, |c' i| ≤ K)
    (hFu : ‖F u‖ ≤ K) (hrow : ‖F t - F u‖ ≤ K * (|t-u| + ρ)) :
    |zR F c t - zR F c' u| ≤ 11 * K ^ 2 * s := by
  let a : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![c 0,c 1,c 2]
  let a' : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![c' 0,c' 1,c' 2]
  have ha (j : Fin 3) : |a j - a' j| ≤ s := by
    fin_cases j
    · exact hdiam 0
    · exact hdiam 1
    · exact hdiam 2
  have hv (i : Fin 2) : |zv c i - zv c' i| ≤ s := by
    fin_cases i
    · exact hdiam 4
    · exact hdiam 6
  have hvel (i : Fin 2) : |zv c i| ≤ K := by
    fin_cases i
    · exact hc 4
    · exact hc 6
  have hrows (i : Fin 2) : |F t i - F u i| ≤ 2 * K * s := by
    have hh := (norm_le_pi_norm (F t - F u) i).trans hrow
    change |F t i - F u i| ≤ _ at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add hgap hρs) (by linarith)).trans_eq
      (by ring))
  have hh := residual_derivative_variation a a' (zv c) (zv c') (F t) (F u)
    t u s K hs hK ha hv hvel (fun i => (norm_le_pi_norm _ i).trans hFu) hrows
    (by simpa only [abs_of_nonneg ht.1] using ht.2) hgap (hc' 2)
  have hid : zR F c t - zR F c' u =
      (a 1 + 2 * t * a 2 - ∑ j, F t j * zv c j) -
        (a' 1 + 2 * u * a' 2 - ∑ j, F u j * zv c' j) := by
    simp [a,a',zR,zv,dotProduct,Fin.sum_univ_two]
    ring
  rw [hid]
  exact hh

/-- Construct the actual residual-bin table inside every full
parameter block and every zoomed physical cell. The accepted arbitrary
diameter-to-list theorem supplies the ENTIRE original-family lists. -/
theorem exists_original_parameter_residual_lists {Λ I : Type*} (E : Set (Λ × ℝ))
    (c : Λ → Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (block : Λ → I)
    (s ρ K : ℝ) (hs : 0 < s) (hρs : ρ ≤ s) (hK : 1 ≤ K)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ z ∈ E, ∀ i, |c z.1 i| ≤ K) (hF : ∀ z ∈ E, ‖F z.2‖ ≤ K)
    (hdiam : ∀ z ∈ E, ∀ z' ∈ E, block z.1 = block z'.1 →
      ∀ i, |c z.1 i - c z'.1 i| ≤ s)
    (hrow : ∀ z ∈ E, ∀ z' ∈ E, ‖F z.2 - F z'.2‖ ≤ K * (|z.2-z'.2| + ρ)) :
    ∃ table : I × (Fin 4 → ℤ) → Finset ℤ,
      (∀ q, ((table q).card : ℝ) ≤ 22 * K ^ 2 + 5) ∧
      ∀ z ∈ E, ⌊zR F (c z.1) z.2 / s⌋ ∈
        table (block z.1,Submission.Lib.K4CommonLocalChoice.cell s (zpos (c z.1) z.2)) := by
  let state := fun z : Λ × ℝ =>
    (block z.1,Submission.Lib.K4CommonLocalChoice.cell s (zpos (c z.1) z.2))
  have hd : ∀ z ∈ E, ∀ z' ∈ E, state z = state z' →
      |zR F (c z.1) z.2 - zR F (c z'.1) z'.2| ≤ (11 * K ^ 2) * s := by
    intro z hz z' hz' hstate
    have hb := congrArg Prod.fst hstate
    have htcode := congrFun (congrArg Prod.snd hstate) 0
    change ⌊z.2 / s⌋ = ⌊z'.2 / s⌋ at htcode
    exact residual_difference_of_coefficient_diameter (c z.1) (c z'.1) F z.2 z'.2 s ρ K
      hs.le hρs hK (htime z hz)
      (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hs htcode).le
      (hdiam z hz z' hz' hb) (hcoeff z hz) (hcoeff z' hz') (hF z' hz') (hrow z hz z' hz')
  obtain ⟨table,hcard,hknown⟩ :=
    Submission.Obl.k4_scalar_heavy_intercept_selection.intercept_bin_lists_of_diameter E state
      (fun z => zR F (c z.1) z.2) hs (by positivity : 0 ≤ 11 * K ^ 2) hd
  exact ⟨table,fun q => (hcard q).trans_eq (by ring),hknown⟩

/-- An actual finite full-parameter-block palette in a zoomed cell
gives the residual list for each original fine velocity bin. -/
theorem exists_velocity_conditioned_residual_lists {Λ I V : Type*} [DecidableEq I]
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (block : Λ → I) (velocity : Λ → V) (s ρ K blocks : ℝ)
    (hs : 0 < s) (hρs : ρ ≤ s) (hK : 1 ≤ K)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ z ∈ E, ∀ i, |c z.1 i| ≤ K) (hF : ∀ z ∈ E, ‖F z.2‖ ≤ K)
    (hdiam : ∀ z ∈ E, ∀ z' ∈ E, block z.1 = block z'.1 →
      ∀ i, |c z.1 i - c z'.1 i| ≤ s)
    (hrow : ∀ z ∈ E, ∀ z' ∈ E, ‖F z.2 - F z'.2‖ ≤ K * (|z.2-z'.2| + ρ))
    (palette : (Fin 4 → ℤ) × V → Finset I)
    (hpalette : ∀ q, ((palette q).card : ℝ) ≤ blocks)
    (hknown : ∀ z ∈ E, block z.1 ∈
      palette (Submission.Lib.K4CommonLocalChoice.cell s (zpos (c z.1) z.2),velocity z.1)) :
    ∃ table : (Fin 4 → ℤ) × V → Finset ℤ,
      (∀ q, ((table q).card : ℝ) ≤ blocks * (22 * K ^ 2 + 5)) ∧
      ∀ z ∈ E, ⌊zR F (c z.1) z.2 / s⌋ ∈
        table (Submission.Lib.K4CommonLocalChoice.cell s (zpos (c z.1) z.2),velocity z.1) := by
  classical
  obtain ⟨localTable,hcard,hlocal⟩ := exists_original_parameter_residual_lists E c F block s ρ K
    hs hρs hK htime hcoeff hF hdiam hrow
  let table : (Fin 4 → ℤ) × V → Finset ℤ := fun q =>
    (palette q).biUnion fun i => localTable (i,q.1)
  refine ⟨table,?_,?_⟩
  · intro q
    calc
      ((table q).card : ℝ) ≤ ∑ i ∈ palette q, ((localTable (i,q.1)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ palette q, (22 * K ^ 2 + 5) := Finset.sum_le_sum fun i _ => hcard _
      _ = ((palette q).card : ℝ) * (22 * K ^ 2 + 5) := by simp; ring
      _ ≤ blocks * (22 * K ^ 2 + 5) := mul_le_mul_of_nonneg_right (hpalette q) (by positivity)
  · intro z hz
    exact Finset.mem_biUnion.mpr ⟨block z.1,hknown z hz,hlocal z hz⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
