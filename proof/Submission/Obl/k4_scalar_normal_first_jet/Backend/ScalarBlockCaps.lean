/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockCaps.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockCaps.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedGroupCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockGraph

/-! Actual scalar block observations have the required original joint cap. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

namespace ScalarNormalHyp

theorem starting_group_joint_cap {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsFiniteMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d c H r : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : d ≤ 1)
    (hH : 0 < H) (hH1 : H ≤ 1) (hr : 0 < r) (hζr : ζ ≤ H * r)
    (bin : ℤ) (a b : ℝ) :
    (scalarGroupPrior (ν.restrict ((fun l => (l, c)) ⁻¹' E))
      (fun l => ⌊D.scalar F l c / H⌋) bin (H ^ d)).real
      {l | l ∈ scalarStartingLabels D E F c H bin ∧
        (6 * K ^ 2) * D.y l c ∈ Icc a (a + r) ∧
        (D.scalar F l c - H * bin) / H ∈ Icc b (b + r)} ≤ 400 * K ^ 3 * r ^ (1 + d) := by
  let A : Set Λ := (fun l => (l, c)) ⁻¹' E
  let B : Set Λ := {l | l ∈ scalarStartingLabels D E F c H bin ∧
    (6 * K ^ 2) * D.y l c ∈ Icc a (a + r) ∧
    (D.scalar F l c - H * bin) / H ∈ Icc b (b + r)}
  have hB : MeasurableSet B :=
    (scalarStartingLabels_measurable D h.event_measurable F c H bin).inter
      (((measurable_const.mul (D.measurable_at_y c)) measurableSet_Icc).inter
        ((((D.measurable_at_scalar F c).sub_const (H * bin)).div_const H) measurableSet_Icc))
  have hL : 1 ≤ 6 * K ^ 2 := by nlinarith
  have hcap y z : ν.real {l | l ∈ A ∧ D.y l c ∈ Icc y (y + H * r) ∧
      D.scalar F l c ∈ Icc z (z + H * r)} ≤ (16 * K ^ 3) * (H * r) ^ (1 + d) := by
    have hh := h.anchor_scalar_joint_cap hK hζ hd c z y (H * r) hζr
    simpa only [A, mem_preimage, mem_setOf_eq, and_comm, and_left_comm, and_assoc] using hh
  have hh := original_normalized_group_joint_cap ν A B (fun l => D.y l c)
    (fun l => D.scalar F l c) (fun l => ⌊D.scalar F l c / H⌋) bin hB
    (fun l hl => hl.1) hH hH1 hr hL
    (show 0 ≤ 16 * K ^ 3 by positivity)
    (fun l hl => hl.2.1) (fun l hl => hl.2.2) hcap
  convert hh using 1 <;> ring

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
