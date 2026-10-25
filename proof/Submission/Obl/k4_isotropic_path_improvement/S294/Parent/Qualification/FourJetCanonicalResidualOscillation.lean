-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FourJetCanonicalResidualOscillation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FourJetCanonicalResidualOscillation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit a194894209bc49bb7eab8e89d27e5205146250d6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FourJetCanonicalResidualOscillation.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetOriginalEntryFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CanonicalResidualTables

/-! # Original canonical residual oscillation with unrestricted intercepts

Adapted from this LOT tree, o265, x0943 at 5207eac7,
Broad/Qualification/FrozenResidualOscillation.lean and FrozenResidualRange.lean.
Those files attribute their source to o106, x0352 at 1e57792e.
The graph and the original coefficients are separate from any packet test.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set
noncomputable section

theorem canonical_residual_oscillation_of_jets {Λ : Type*}
    (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ) (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ)
    (b ρ H η error : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hjet : ∀ z∈E, |c z.1 2| ≤ H)
    (hrow : ∀ z∈E, ∀ i : Fin 2,
      |G (originalFineState c b z) i.succ-F (parameterCode ρ (c z.1)) z.2 i| ≤ η)
    (hgraph : ∀ z∈E,
      |c z.1 1+2*c z.1 2*z.2-G (originalFineState c b z) 0-
        (fun i : Fin 2 => G (originalFineState c b z) i.succ) ⬝ᵥ zv (c z.1)| ≤ error) :
    ∀ z∈E, ∀ z'∈E, originalFineState c b z=originalFineState c b z' →
      parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
      |originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1)
        (fun y => F (parameterCode ρ (c y.1)) y.2) Prod.snd z-
        originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1)
          (fun y => F (parameterCode ρ (c y.1)) y.2) Prod.snd z'| ≤
            (2*(error+2*η*ρ)+2*(H+1)*b)/ρ := by
  intro z hz z' hz' hstate hworld
  let q := parameterCode ρ (c z.1)
  let center := parameterCenter ρ q
  have hcenter : |center 2| ≤ H+1 := by
    have hd := original_parameter_center_distance ρ hρ (c z.1) 2
    have ha := abs_sub_le (center 2) (c z.1 2) 0
    rw [sub_zero,sub_zero,abs_sub_comm _ (c z.1 2)] at ha
    change |c z.1 2-center 2| ≤ ρ at hd
    linarith [hjet z hz]
  have hworld' : parameterCode ρ (c z'.1)=q := hworld.symm
  have hdiam (y : Λ × ℝ) (hy : parameterCode ρ (c y.1)=q) (i : Fin 7) :
      |c y.1 i-center i| ≤ ρ := by
    have hh := original_parameter_center_distance ρ hρ (c y.1) i
    simpa only [hy] using hh
  have hvel (y : Λ × ℝ) (hy : parameterCode ρ (c y.1)=q) (i : Fin 2) :
      |zv (c y.1) i-zv center i| ≤ ρ := by
    fin_cases i
    · exact hdiam y hy 4
    · exact hdiam y hy 6
  have hrow' := hrow z' hz'
  have hgraph' := hgraph z' hz'
  rw [← hstate,hworld'] at hrow'
  rw [← hstate] at hgraph'
  have hr := hrow z hz
  change ∀ i : Fin 2, |G (originalFineState c b z) i.succ-F q z.2 i| ≤ η at hr
  have hh := zoom_residual_original_state_range ρ hρ center (c z.1) (c z'.1) (F q)
    (G (originalFineState c b z) 0) (fun i : Fin 2 => G (originalFineState c b z) i.succ)
    z.2 z'.2 η ρ error hη hρ.le hr hrow' (hvel z rfl) (hvel z' hworld')
    (hgraph z hz) hgraph'
  have htime : |z.2-z'.2| ≤ b := by
    have ht := congrFun hstate 0
    exact (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hb ht).le
  have hnum : 2 * |center 2| * |z.2-z'.2| ≤ 2*(H+1)*b := by
    have hc := mul_le_mul hcenter htime (abs_nonneg _) (by linarith : 0 ≤ H+1)
    linarith
  have hcmp := hh.trans (div_le_div_of_nonneg_right (add_le_add le_rfl hnum) hρ.le)
  simpa only [originalResidualValue,canonicalZoomCoefficients,hworld',q,center,zR] using hcmp

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
