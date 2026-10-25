-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalZoomBlockVisits, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalZoomBlockVisits.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalZoomBlockVisits.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalZoomBlockVisits.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomEntryFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomTimeRow
import Submission.Obl.k4_scalar_coefficient_clustering.Grid
import Submission.Obl.k4_scalar_initial_true_horizon.FiniteCardBound
import Submission.Lib.K4IncidenceWitnesses
import Submission.Obl.k4_matching_homogeneous_records.Offsets


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set

noncomputable section

def zoomBlockVisitConstant : ℝ := 4*(17 : ℝ)^4

def originalZoomBlock {Λ : Type*} (c : Λ → Fin 7 → ℝ) (ρ s : ℝ) (l : Λ) :
    (Fin 7 → ℤ) × (Fin 7 → ℤ) := (parameterCode ρ (c l),parameterCode (ρ*s) (c l))

/-- Dyadic alignment makes the tagged (coarse,fine) original block
fiber exactly the FULL original fine-bin fiber, including every old tag. -/
theorem original_zoom_block_fiber_eq_fine {Λ : Type*} (c : Λ → Fin 7 → ℝ)
    (ρ s : ℝ) (hρ : 0 < ρ) (n : ℕ) (hs : s=dyadicParameterWidth n) (l₀ : Λ) :
    {l | originalZoomBlock c ρ s l=originalZoomBlock c ρ s l₀} =
      {l | parameterCode (ρ*s) (c l)=parameterCode (ρ*s) (c l₀)} := by
  have hparent (l : Λ) : coarsenParameterCode n (parameterCode (ρ*s) (c l))=parameterCode ρ (c l) := by
    rw [hs]
    exact coarsen_parameterCode ρ hρ n (c l)
  ext l
  simp only [mem_ofPred_eq,originalZoomBlock,Prod.mk.injEq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_,h⟩
    rw [← hparent l,h,hparent l₀]

/-- A literal old beta=rho*s block has zoomed coefficient diameter s
inside its SAME original rho world. -/
theorem canonical_zoom_block_diameter {Λ : Type*} (c : Λ → Fin 7 → ℝ)
    (ρ s : ℝ) (hρ : 0 < ρ) (hs : 0 < s) (l l' : Λ)
    (hblock : originalZoomBlock c ρ s l=originalZoomBlock c ρ s l') :
    ‖canonicalZoomCoefficients c ρ l-canonicalZoomCoefficients c ρ l'‖ ≤ s := by
  have hw := congrArg Prod.fst hblock
  have hb := congrArg Prod.snd hblock
  have hh := zoom_piece_diameter ρ s hρ hs
    (parameterCenter ρ (parameterCode ρ (c l))) (c l) (c l') (fun i => congrFun hb i)
  simpa only [canonicalZoomCoefficients,show parameterCode ρ (c l')=parameterCode ρ (c l) from hw.symm] using hh

/-- Actual cells visited by all original trajectories of one beta block
in its original parameter zoom. Time has width s, not beta: the whole
arbitrary line family visits at most C/s cells, with NO rho inverse. -/
theorem original_zoom_block_cell_lists {Λ : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (ρ s : ℝ)
    (hρ : 0 < ρ) (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1) :
    ∃ cells : ((Fin 7 → ℤ) × (Fin 7 → ℤ)) → Finset (Fin 4 → ℤ),
      (∀ b, ((cells b).card : ℝ) ≤ zoomBlockVisitConstant/s) ∧
      ∀ z∈E, canonicalZoomCell c ρ s z ∈ cells (originalZoomBlock c ρ s z.1) := by
  classical
  let Codes := fun b : (Fin 7 → ℤ) × (Fin 7 → ℤ) =>
    {q | ∃ z∈E, originalZoomBlock c ρ s z.1=b ∧ canonicalZoomCell c ρ s z=q}
  have hcount (b) (N : Finset (Fin 4 → ℤ)) (hN : (↑N : Set (Fin 4 → ℤ)) ⊆ Codes b) :
      (N.card : ℝ) ≤ zoomBlockVisitConstant/s := by
    have hex (n : N) : ∃ z∈E, originalZoomBlock c ρ s z.1=b ∧ canonicalZoomCell c ρ s z=n.val :=
      hN n.property
    choose point hp using hex
    let tc := fun n : N => ⌊(point n).2/s⌋
    let J := (Finset.univ : Finset N).image tc
    have htime (n : N) : (point n).2∈Icc (0 : ℝ) 1 := ht _ (hp n).1
    have hrange (n : N) : (0 : ℝ) ≤ (tc n : ℝ) ∧ (tc n : ℝ) ≤ 1/s := by
      have hlo : (0 : ℤ) ≤ tc n := Int.floor_nonneg.mpr (div_nonneg (htime n).1 hs.le)
      exact ⟨by exact_mod_cast hlo,(Int.floor_le _).trans (div_le_div_of_nonneg_right (htime n).2 hs.le)⟩
    have hJ : (J.card : ℝ) ≤ 2/s+2 := by
      apply (Submission.Obl.k4_scalar_coefficient_clustering.card_int_grid_of_diameter
        J (by positivity : 0 ≤ 1/s) ?_).trans_eq
      · ring
      intro a ha a' ha'
      obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨n',_,rfl⟩ := Finset.mem_image.mp ha'
      exact abs_le.mpr ⟨by linarith [(hrange n).1,(hrange n').2],
        by linarith [(hrange n).2,(hrange n').1]⟩
    have hfiber (j : ℤ) :
        (((Finset.univ : Finset N).filter fun n => tc n=j).card : ℝ) ≤ (17 : ℝ)^4 := by
      let S := (Finset.univ : Finset N).filter fun n => tc n=j
      have hinj : S.card=(S.image Subtype.val).card :=
        (Finset.card_image_of_injective S Subtype.val_injective).symm
      rw [hinj]
      apply (Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter
        (S.image Subtype.val) (by norm_num : (0 : ℝ) ≤ 7) ?_).trans_eq (by norm_num)
      intro q hq q' hq' k
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨n',hn',rfl⟩ := Finset.mem_image.mp hq'
      have hdt : |(point n).2-(point n').2| ≤ s := by
        exact (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hs
          ((Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hn').2.symm)).le
      have hdiam := canonical_zoom_block_diameter c ρ s hρ hs (point n).1 (point n').1
        ((hp n).2.1.trans (hp n').2.1.symm)
      have hcoord (i : Fin 7) :
          |canonicalZoomCoefficients c ρ (point n).1 i-canonicalZoomCoefficients c ρ (point n').1 i| ≤ s :=
        (norm_le_pi_norm (canonicalZoomCoefficients c ρ (point n).1-
          canonicalZoomCoefficients c ρ (point n').1) i).trans hdiam
      have hz := original_parameter_world_position_comparison
        (canonicalZoomCoefficients c ρ (point n).1) (canonicalZoomCoefficients c ρ (point n').1)
        s 1 (point n).2 (point n').2 hs.le (by norm_num) (htime n) (htime n') hcoord
        (original_parameter_zoom_coefficients_bound ρ hρ (c (point n').1))
      have hvalue : |zpos (canonicalZoomCoefficients c ρ (point n).1) (point n).2 k-
          zpos (canonicalZoomCoefficients c ρ (point n').1) (point n').2 k| ≤ 6*s := by
        exact ((norm_le_pi_norm _ k).trans hz).trans (by linarith)
      have hscaled : |zpos (canonicalZoomCoefficients c ρ (point n).1) (point n).2 k/s-
          zpos (canonicalZoomCoefficients c ρ (point n').1) (point n').2 k/s| ≤ 6 := by
        rwa [← sub_div,abs_div,abs_of_pos hs,div_le_iff₀ hs]
      have hh := Submission.Obl.k4_matching_homogeneous_records.floor_sub_bound
        (zpos (canonicalZoomCoefficients c ρ (point n).1) (point n).2 k/s)
        (zpos (canonicalZoomCoefficients c ρ (point n').1) (point n').2 k/s)
      have hcode := congrFun (hp n).2.2 k
      have hcode' := congrFun (hp n').2.2 k
      change ⌊zpos (canonicalZoomCoefficients c ρ (point n).1) (point n).2 k/s⌋=n.val k at hcode
      change ⌊zpos (canonicalZoomCoefficients c ρ (point n').1) (point n').2 k/s⌋=n'.val k at hcode'
      rw [hcode,hcode',Int.cast_sub] at hh
      linarith
    have htotal := Submission.Obl.k4_scalar_coefficient_clustering.card_le_image_mul_fiber
      (Finset.univ : Finset N) tc ((17 : ℝ)^4) (fun j _ => hfiber j)
    have hscale : 2/s+2 ≤ 4/s := by
      apply (le_div_iff₀ hs).mpr
      field_simp
      nlinarith
    have hn : (N.card : ℝ) ≤ (4/s)*(17 : ℝ)^4 := by
      simpa only [Finset.card_univ,Fintype.card_coe] using
        htotal.trans (mul_le_mul_of_nonneg_right (hJ.trans hscale) (by positivity))
    exact hn.trans_eq (by unfold zoomBlockVisitConstant; ring)
  have hfinite (b) :=
    Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
      (Codes b) (zoomBlockVisitConstant/s) (hcount b)
  refine ⟨fun b => (hfinite b).toFinset,?_,?_⟩
  · intro b
    exact hcount b _ (by simp)
  · intro z hz
    exact (hfinite _).mem_toFinset.mpr ⟨z,hz,rfl,rfl⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
