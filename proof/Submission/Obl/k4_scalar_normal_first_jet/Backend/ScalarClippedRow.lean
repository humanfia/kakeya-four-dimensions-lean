/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarClippedRow.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarClippedRow.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_lift_plank.Lift

/-! Global bounded rows equal the original row at every active incidence. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

/-- Affinely rescale the accepted unit-interval clip. -/
noncomputable def scalarClippedRow (K : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * K * Submission.Obl.k4_scalar_lift_plank.clip ((F t + K) / (2 * K)) - K

theorem measurable_scalarClippedRow {K : ℝ} {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (scalarClippedRow K F) :=
  ((Submission.Obl.k4_scalar_lift_plank.measurable_clip.comp
    ((hF.add_const K).div_const (2 * K))).const_mul (2 * K)).sub_const K

theorem scalarClippedRow_bound {K : ℝ} (hK : 0 ≤ K) (F : ℝ → ℝ) (t : ℝ) :
    |scalarClippedRow K F t| ≤ K := by
  have hlow := Submission.Obl.k4_scalar_lift_plank.clip_nonneg ((F t + K) / (2 * K))
  have hhigh := Submission.Obl.k4_scalar_lift_plank.clip_le_one ((F t + K) / (2 * K))
  dsimp only [scalarClippedRow]
  rw [abs_le]
  constructor <;> nlinarith

theorem scalarClippedRow_eq {K : ℝ} (hK : 0 < K) {F : ℝ → ℝ} {t : ℝ}
    (hF : |F t| ≤ K) : scalarClippedRow K F t = F t := by
  have hbounds := abs_le.mp hF
  have hden : 0 < 2 * K := by positivity
  have hmem : (F t + K) / (2 * K) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by linarith) hden.le, ?_⟩
    apply (div_le_iff₀ hden).mpr
    linarith
  rw [scalarClippedRow, Submission.Obl.k4_scalar_lift_plank.clip_of_mem hmem]
  field_simp <;> ring

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
