/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockGroup.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockGroup.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalData
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarStartingGroup

/-! Starting-bin normalization derived from primitive scalar-normal data. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

namespace ScalarNormalHyp

theorem original_starting_group_palette {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsFiniteMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d H c : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : d ≤ 1)
    (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ 10000 * K ^ 4 / H ^ d ∧
      (∀ l, (l, c) ∈ E → (⌊D.scalar F l c / H⌋ : ℤ) ∈ J) ∧
      (∀ b ∈ J, (ν.restrict ((fun l => (l, c)) ⁻¹' E)).real
        {l | (⌊D.scalar F l c / H⌋ : ℤ) = b} ≤ 10000 * K ^ 4 * H ^ d) ∧
      ∀ b ∈ J, (scalarGroupPrior (ν.restrict ((fun l => (l, c)) ⁻¹' E))
        (fun l => ⌊D.scalar F l c / H⌋) b (H ^ d)).real univ ≤ 10000 * K ^ 4 := by
  let A : Set Λ := (fun l => (l, c)) ⁻¹' E
  have hA : MeasurableSet A := measurable_prodMk_right h.event_measurable
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hBY : 1 ≤ 2 * K := by linarith
  have hBZ : 0 < 5 * K ^ 2 := by positivity
  have hHBZ : H ≤ 2 * (5 * K ^ 2) := by nlinarith
  have hY : ∀ l ∈ A, |D.y l c| ≤ 2 * K := fun l hl => (h.active_bounds hK hl).2.1
  have hsupport : ∀ l ∈ A, D.scalar F l c ∈ S c ∩ Icc (-(5 * K ^ 2)) (5 * K ^ 2) := by
    intro l hl
    exact ⟨h.support_mem _ hl, abs_le.mp (h.active_bounds hK hl).2.2.2⟩
  have hSH : IntervalAD H d K (S c) := by
    intro r R a hHr hrR
    exact h.support_AD c r R a (hζH.trans hHr) hrR
  have hjoint : ∀ a b : ℝ,
      ν.real {l | l ∈ A ∧ D.y l c ∈ Icc a (a + H) ∧ D.scalar F l c ∈ Icc b (b + H)} ≤
        (16 * K ^ 3) * H ^ (1 + d) := by
    intro a b
    have hh := h.anchor_scalar_joint_cap hK hζ hd c b a H hζH
    simpa only [A, mem_preimage, mem_setOf_eq, and_comm, and_left_comm, and_assoc] using hh
  have hbase : 1 ≤ 2 * (5 * K ^ 2) := by nlinarith
  have hpow : (2 * (5 * K ^ 2)) ^ d ≤ 2 * (5 * K ^ 2) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hd
  have hK34 : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num : (3 : ℕ) ≤ 4)
  have hcount : 3 * K * (2 * (5 * K ^ 2)) ^ d ≤ 10000 * K ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 3 * K)
    nlinarith [pow_nonneg hK0 4]
  have hprior : 50 * (2 * K) * (16 * K ^ 3) ≤ 10000 * K ^ 4 := by
    nlinarith [pow_nonneg hK0 4]
  exact original_scalar_starting_group_palette ν A hA
    (fun l => D.y l c) (fun l => D.scalar F l c) (D.measurable_at_scalar F c) (S c)
    hH hH1 hBY hBZ hHBZ hK0 (by positivity) (by positivity) hSH hY hsupport hjoint hcount hprior

theorem exists_original_starting_bin_group {Λ Θ : Type*}
    [MeasurableSpace Λ] [MeasurableSpace Θ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsFiniteMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d H c δ : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : d ≤ 1)
    (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H)
    (μ : Measure Θ) [IsFiniteMeasure μ] {P : Set (Θ × Λ)} (hP : MeasurableSet P)
    (hPA : P ⊆ univ ×ˢ ((fun l => (l, c)) ⁻¹' E))
    (hδ : 0 < δ) (hmass : δ ≤ (μ.prod ν).real P) :
    ∃ b : ℤ,
      (scalarGroupPrior (ν.restrict ((fun l => (l, c)) ⁻¹' E))
        (fun l => ⌊D.scalar F l c / H⌋) b (H ^ d)).real univ ≤ 10000 * K ^ 4 ∧
      δ / (10000 * K ^ 4) ≤
        (μ.prod (scalarGroupPrior (ν.restrict ((fun l => (l, c)) ⁻¹' E))
          (fun l => ⌊D.scalar F l c / H⌋) b (H ^ d))).real
            (P ∩ (univ ×ˢ {l | ⌊D.scalar F l c / H⌋ = b})) := by
  let A : Set Λ := (fun l => (l, c)) ⁻¹' E
  have hA : MeasurableSet A := measurable_prodMk_right h.event_measurable
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hBY : 1 ≤ 2 * K := by linarith
  have hBZ : 0 < 5 * K ^ 2 := by positivity
  have hHBZ : H ≤ 2 * (5 * K ^ 2) := by nlinarith
  have hY : ∀ l ∈ A, |D.y l c| ≤ 2 * K := fun l hl => (h.active_bounds hK hl).2.1
  have hsupport : ∀ l ∈ A, D.scalar F l c ∈ S c ∩ Icc (-(5 * K ^ 2)) (5 * K ^ 2) := by
    intro l hl
    exact ⟨h.support_mem _ hl, abs_le.mp (h.active_bounds hK hl).2.2.2⟩
  have hSH : IntervalAD H d K (S c) := by
    intro r R a hHr hrR
    exact h.support_AD c r R a (hζH.trans hHr) hrR
  have hjoint : ∀ a b : ℝ,
      ν.real {l | l ∈ A ∧ D.y l c ∈ Icc a (a + H) ∧ D.scalar F l c ∈ Icc b (b + H)} ≤
        (16 * K ^ 3) * H ^ (1 + d) := by
    intro a b
    have hh := h.anchor_scalar_joint_cap hK hζ hd c b a H hζH
    simpa only [A, mem_preimage, mem_setOf_eq, and_comm, and_left_comm, and_assoc] using hh
  have hbase : 1 ≤ 2 * (5 * K ^ 2) := by nlinarith
  have hpow : (2 * (5 * K ^ 2)) ^ d ≤ 2 * (5 * K ^ 2) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hd
  have hK34 : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num : (3 : ℕ) ≤ 4)
  have hcount : 3 * K * (2 * (5 * K ^ 2)) ^ d ≤ 10000 * K ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 3 * K)
    nlinarith [pow_nonneg hK0 4]
  have hprior : 50 * (2 * K) * (16 * K ^ 3) ≤ 10000 * K ^ 4 := by
    nlinarith [pow_nonneg hK0 4]
  exact exists_original_scalar_starting_group μ ν hP A hA hPA
    (fun l => D.y l c) (fun l => D.scalar F l c) (D.measurable_at_scalar F c) (S c)
    hH hH1 hBY hBZ hHBZ hK0 (by positivity) (by positivity) hδ hmass hSH hY hsupport hjoint hcount hprior

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
