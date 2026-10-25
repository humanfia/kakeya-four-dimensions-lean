/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarMovingGroupCaps.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarMovingGroupCaps.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedGroupCaps

/-! Original caps after an anchor group is read at a different physical time. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem original_normalized_moving_group_joint_cap {Λ β : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (Aanchor Acurrent B : Set Λ)
    (Yanchor Ycurrent Zcurrent : Λ → ℝ) (code : Λ → β) (bin : β)
    (hB : MeasurableSet B) (hanchor : B ⊆ Aanchor ∩ (code ⁻¹' {bin}))
    (hcurrent : B ⊆ Acurrent) {H p K C d a b base : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hp : 0 < p) (hHp : H ≤ p)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hmove : ∀ l ∈ B, |Ycurrent l - Yanchor l| ≤ K * H)
    (hY : ∀ l ∈ B, Yanchor l ∈ Icc a (a + p))
    (hZ : ∀ l ∈ B, (Zcurrent l - base) / H ∈ Icc b (b + p))
    (hcap : ∀ y z : ℝ,
      ν.real {l | l ∈ Acurrent ∧ Ycurrent l ∈ Icc y (y + H * p) ∧
        Zcurrent l ∈ Icc z (z + H * p)} ≤ C * (H * p) ^ (1 + d)) :
    (scalarGroupPrior (ν.restrict Aanchor) code bin (H ^ d)).real B ≤
      25 * (1 + 2 * K) * C * p ^ (1 + d) := by
  rw [original_scalar_group_real ν Aanchor code bin (Real.rpow_pos_of_pos hH d) hB hanchor]
  have hbox l (hl : l ∈ B) :
      (![Ycurrent l, Zcurrent l] : Fin 2 → ℝ) 0 ∈
        Icc (a - K * H) (a - K * H + (1 + 2 * K) * p) ∧
      (![Ycurrent l, Zcurrent l] : Fin 2 → ℝ) 1 ∈
        Icc (base + H * b) (base + H * b + H * p) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hmov := abs_le.mp (hmove l hl)
    have hy := hY l hl
    have hz := hZ l hl
    have hKH := mul_le_mul_of_nonneg_left hHp hK
    refine ⟨⟨by linarith [hmov.1, hy.1], by nlinarith [hmov.2, hy.2]⟩, ?_⟩
    constructor
    · have hh := (le_div_iff₀ hH).mp hz.1
      nlinarith
    · have hh := (div_le_iff₀ hH).mp hz.2
      nlinarith
  have hcubes (c : Fin 2 → ℝ) :
      ν.real {l | l ∈ Acurrent ∧
        ∀ i, (![Ycurrent l, Zcurrent l] : Fin 2 → ℝ) i ∈ Icc (c i) (c i + H * p)} ≤
        C * (H * p) ^ (1 + d) := by
    simpa only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
      hcap (c 0) (c 1)
  exact original_normalized_scalar_cap_enlarged ν Acurrent B
    (fun l => ![Ycurrent l, Zcurrent l]) ![a - K * H, base + H * b]
    hH hH1 (by linarith) hp hC hcurrent hbox hcubes

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
