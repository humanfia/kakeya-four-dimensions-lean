/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFirstJetValue.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFirstJetValue.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarMotion

/-! The actual first-jet value, independent of coefficient-bin covering calculations.
The declarations are moved from x0662's ScalarCoefficientObservations in this obligation. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

def scalarFirstJet {Λ : Type*} [MeasurableSpace Λ] (D : ScalarMotion Λ)
    (F A : ℝ → ℝ) (l : Λ) (t : ℝ) : ℝ := D.residual F l t - A t * D.y l t

theorem scalarFirstJet_measurable {Λ : Type*} [MeasurableSpace Λ] (D : ScalarMotion Λ)
    {F A : ℝ → ℝ} (hF : Measurable F) (hA : Measurable A) :
    Measurable (fun p : Λ × ℝ => scalarFirstJet D F A p.1 p.2) :=
  (D.measurable_residual hF).sub ((hA.comp measurable_snd).mul D.measurable_y)

theorem scalarFirstJet_bound {Λ : Type*} [MeasurableSpace Λ] (D : ScalarMotion Λ)
    {F A : ℝ → ℝ} {K t : ℝ} (hK : 1 ≤ K) {l : Λ} (hl : D.Bounded K l)
    (ht : t ∈ Icc (0 : ℝ) 1) (hF : |F t| ≤ K) (hA : |A t| ≤ K) :
    |scalarFirstJet D F A l t| ≤ 6 * K ^ 2 := by
  have hb := D.bounds_at_unit_time hK hl ht hF
  have hAy : |A t * D.y l t| ≤ K * (2 * K) := by
    rw [abs_mul]
    exact mul_le_mul hA hb.2.1 (abs_nonneg _) (zero_le_one.trans hK)
  exact (abs_sub _ _).trans (by linarith [hb.2.2.1])

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
