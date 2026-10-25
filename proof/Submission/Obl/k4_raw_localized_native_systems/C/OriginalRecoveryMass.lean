import Submission.Obl.k4_raw_localized_native_systems.C.ProjectedPackets
import Submission.Obl.k4_raw_localized_native_systems.C.PacketBudgets
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

/-
Adapted from this LOT tree, o178, session x0596, `OriginalRecoveryMass.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- All parent budgets are charged to the unchanged probability priors.
Disjointness is required only within an original world and time block. -/
theorem ProjectedPackets.budget_le_one
    {p : Data} {k M D : ℕ} {loss h η d s m S U : ℝ}
    (hp : Valid p) (a : ProjectedPackets p k M D loss h η d s m S U) :
    (∑ b, ENNReal.ofReal (p.ω k (a.atlas.γ b)) * packetBudget a.atlas b) ≤ 1 := by
  classical
  obtain ⟨Mν, Dν, hf⟩ := hp.2.2.2.2.2.2.2.2.1
  have hb := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
    (p.ν k) (p.ω k) a.atlas.γ a.atlas.j a.atlas.A
    (fun w => ((hf k).2.2.2.1 w).1) (hf k).2.1 (hf k).2.2.1
    (fun b => (a.known.1.2.2.1 b).2.2.2.2.2.2.1)
    a.known.1.2.1
  have heq : ENNReal.ofReal (packetTimeLength a.atlas) *
      (Fintype.card (Fin (2 ^ a.atlas.T)) : ENNReal) = 1 := by
    rw [Fintype.card_fin, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (packetTimeLength_pos a.atlas).le]
    have hident : packetTimeLength a.atlas * ((2 ^ a.atlas.T : ℕ) : ℝ) = 1 := by
      simp [packetTimeLength]
    rw [hident, ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal (packetTimeLength a.atlas) *
        ∑ b, ENNReal.ofReal (p.ω k (a.atlas.γ b)) *
          p.ν k (a.atlas.γ b) (a.atlas.A b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp only [packetBudget]
      ring
    _ ≤ ENNReal.ofReal (packetTimeLength a.atlas) *
        (Fintype.card (Fin (2 ^ a.atlas.T)) : ENNReal) := by gcongr
    _ = 1 := heq

/-- A dominated pushed-forward packet pays its recovered mass directly on
the original selected law.  Its normalization is never changed after recovery. -/
theorem dominated_map_recovery_mass
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (hf : Measurable f)
    (a : ENNReal) (F S : Set Y) (hS : MeasurableSet S)
    (hdom : a • Measure.map f μ ≤ ν.restrict F) :
    a * μ (f ⁻¹' S) ≤ ν (F ∩ S) := by
  have hh := hdom S
  simpa only [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf hS,
    Measure.restrict_apply hS, Set.inter_comm S F] using hh

/-- The half-mass convention used by Q0 is equivalent to the multiplicative
form needed by the finite global packet budget. -/
theorem twice_recovered_mass {a b : ENNReal}
    (h : ENNReal.ofReal (1 / 2 : ℝ) * a ≤ b) : a ≤ 2 * b := by
  calc
    a = 2 * (ENNReal.ofReal (1 / 2 : ℝ) * a) := by
      have heq : (2 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
        calc
          _ = ENNReal.ofReal ((2 : ℝ) * (1 / 2)) := by
            rw [ENNReal.ofReal_mul (by norm_num)]
            norm_num
          _ = 1 := by norm_num
      rw [← mul_assoc, heq, one_mul]
    _ ≤ 2 * b := mul_le_mul_of_nonneg_left h zero_le

end
end Submission.Obl.k4_raw_localized_native_systems.C
