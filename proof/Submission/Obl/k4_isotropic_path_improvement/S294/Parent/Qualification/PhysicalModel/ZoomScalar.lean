-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.ZoomScalar, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/ZoomScalar.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenZoomScalar.lean.
The bounded quadratic physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenZoomScalar.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomScalarStrips


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set
open scoped BigOperators

noncomputable section

/-- The scalar-normal affine base is the actual original native base. -/
theorem scalar_normal_base (p : PhysicalModel) (l : Ln) (t : ℝ) :
    Jets2.normalBase (p.scalarCoefficients l) t =
      fun j => p.position l j + p.velocity l j * t := by
  funext j
  fin_cases j <;> simp [Jets2.normalBase, Jets2.zy, position, velocity]

theorem scalar_normal_polynomial (p : PhysicalModel) (l : Ln) (G : Fin 3 → ℝ) (t : ℝ) :
    Jets2.normalScalar G (p.scalarCoefficients l) t =
      (originalNormalPolynomial (p.signal l) (p.position l) (p.velocity l) G).eval t := by
  rw [Jets2.normalScalar, p.scalar_x, ← p.eval_signal, p.scalar_normal_base,
    originalNormalPolynomial_eval]

/-- The normal bin of an actual original incidence, with its row read
from the SAME original fine state. -/
theorem stripLabel_normal_bin (p : PhysicalModel) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (z : Ev) :
    (p.stripLabel b ρ width row z).2 =
      ⌊originalNormalStateCenter (p.signal z.1) (p.position z.1) (p.velocity z.1)
        (row (p.stripLabel b ρ width row z).1) b z.2 / width⌋ := by
  change (originalStripLabel b ρ width row p.signal p.position p.velocity z).2 = _
  rw [originalStripLabel, nativeStripState_original]
  rfl

/-- Construct the scalar/normal-bin comparison from the original
parameter diameter and actual fine physical-state rounding. -/
theorem zoom_scalar_fine_normal_error (p : PhysicalModel) (l : Ln)
    (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (G : Fin 3 → ℝ)
    (ρ b B t η : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (hB : 0 ≤ B) (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hdiam : ∀ i, |p.scalarCoefficients l i - center i| ≤ ρ)
    (hG : ∀ j, |G j| ≤ B)
    (hrow : ∀ i : Fin 2, |G i.succ - F t i| ≤ η) :
    |ρ * Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t -
      (originalNormalStateCenter (p.signal l) (p.position l) (p.velocity l) G b t +
        Jets2.coarseScalarTranslation G center t)| ≤ 4 * η * ρ + (1 + 3 * B) * b := by
  have hzoom := Jets2.zoom_scalar_original_world_error ρ hρ center
    (p.scalarCoefficients l) F G t η ht hη hdiam hrow
  rw [p.scalar_normal_polynomial] at hzoom
  have hstate := originalNormalStateCenter_error (p.signal l) (p.position l) (p.velocity l)
    G b B t hb hB hG
  have htri := abs_sub_le
    (ρ * Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t)
    ((originalNormalPolynomial (p.signal l) (p.position l) (p.velocity l) G).eval t +
      Jets2.coarseScalarTranslation G center t)
    (originalNormalStateCenter (p.signal l) (p.position l) (p.velocity l) G b t +
      Jets2.coarseScalarTranslation G center t)
  rw [add_sub_add_right_eq_sub, abs_sub_comm
    ((originalNormalPolynomial (p.signal l) (p.position l) (p.velocity l) G).eval t)] at htri
  exact htri.trans (add_le_add hzoom hstate)

/-- Each actual retained incidence is covered by the midpoint of its
ORIGINAL normal strip. The centre depends only on time and strip code. -/
theorem zoom_scalar_in_original_strip_ball (p : PhysicalModel) (z : Ev)
    (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (ρ b B r width η : ℝ)
    (hρ : 0 < ρ) (hb : 0 < b) (hw : 0 < width)
    (hB : 0 ≤ B) (hη : 0 ≤ η) (ht : z.2 ∈ Icc (0 : ℝ) 1)
    (hscale : width = ρ * r)
    (hsmall : 4 * η * ρ + (1 + 3 * B) * b ≤ width / 2)
    (hdiam : ∀ i, |p.scalarCoefficients z.1 i - center i| ≤ ρ)
    (hG : ∀ j, |row (p.stripLabel b ρ width row z).1 j| ≤ B)
    (hrow : ∀ i : Fin 2, |row (p.stripLabel b ρ width row z).1 i.succ - F z.2 i| ≤ η) :
    Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients z.1)) z.2 ∈
      Metric.closedBall
        ((((p.stripLabel b ρ width row z).2 : ℝ) + 1 / 2) * width / ρ +
          Jets2.coarseScalarTranslation (row (p.stripLabel b ρ width row z).1) center z.2 / ρ) r := by
  apply Jets2.scalar_in_ball_of_normal_strip hρ hw hscale hsmall
    (Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients z.1)) z.2)
    (originalNormalStateCenter (p.signal z.1) (p.position z.1) (p.velocity z.1)
      (row (p.stripLabel b ρ width row z).1) b z.2)
    (Jets2.coarseScalarTranslation (row (p.stripLabel b ρ width row z).1) center z.2)
    (p.stripLabel b ρ width row z).2
  · exact p.zoom_scalar_fine_normal_error z.1 center F
      (row (p.stripLabel b ρ width row z).1) ρ b B z.2 η hρ hb hB hη ht
      hdiam hG hrow
  · exact (p.stripLabel_normal_bin b ρ width row z).symm

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
