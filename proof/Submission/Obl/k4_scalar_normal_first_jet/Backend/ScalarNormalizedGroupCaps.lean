/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarNormalizedGroupCaps.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarNormalizedGroupCaps.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAnisotropicCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGroupNormalization

/-! The normalized original starting group inherits its actual joint cap. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem original_normalized_group_joint_cap {Λ β : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A B : Set Λ) (Y Z : Λ → ℝ)
    (code : Λ → β) (bin : β) (hB : MeasurableSet B) (hsub : B ⊆ A ∩ (code ⁻¹' {bin}))
    {H r L a b base C d : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hr : 0 < r)
    (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hY : ∀ l ∈ B, L * Y l ∈ Icc a (a + r))
    (hZ : ∀ l ∈ B, (Z l - base) / H ∈ Icc b (b + r))
    (hcap : ∀ y z : ℝ,
      ν.real {l | l ∈ A ∧ Y l ∈ Icc y (y + H * r) ∧ Z l ∈ Icc z (z + H * r)} ≤
        C * (H * r) ^ (1 + d)) :
    (scalarGroupPrior (ν.restrict A) code bin (H ^ d)).real B ≤ 25 * C * r ^ (1 + d) := by
  rw [original_scalar_group_real ν A code bin (Real.rpow_pos_of_pos hH d) hB hsub]
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hbox : ∀ l ∈ B,
      (![Y l, Z l] : Fin 2 → ℝ) 0 ∈ Icc (a / L) (a / L + r) ∧
      (![Y l, Z l] : Fin 2 → ℝ) 1 ∈ Icc (base + H * b) (base + H * b + H * r) := by
    intro l hl
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hy := hY l hl
    have hz := hZ l hl
    have ha : a / L * L = a := div_mul_cancel₀ a hLpos.ne'
    have hrl : r ≤ L * r := by nlinarith
    refine ⟨⟨(div_le_iff₀ hLpos).mpr (by nlinarith [hy.1]), ?_⟩, ?_⟩
    · have hh := hy.2
      apply (mul_le_mul_iff_left₀ hLpos).mp
      nlinarith
    · have hlo := (le_div_iff₀ hH).mp hz.1
      have hhi := (div_le_iff₀ hH).mp hz.2
      constructor <;> nlinarith
  have hcube : ∀ c : Fin 2 → ℝ,
      ν.real {l | l ∈ A ∧ ∀ i, (![Y l, Z l] : Fin 2 → ℝ) i ∈ Icc (c i) (c i + H * r)} ≤
        C * (H * r) ^ (1 + d) := by
    intro c
    simpa only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hcap (c 0) (c 1)
  exact original_normalized_scalar_cap ν A B (fun l => ![Y l, Z l]) ![a / L, base + H * b]
    hH hH1 hr hC (fun l hl => (hsub hl).1) hbox hcube

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
