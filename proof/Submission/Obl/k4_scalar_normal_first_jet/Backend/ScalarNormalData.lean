/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarNormalData.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarNormalData.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarMotion
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCovers
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarShearCaps

/-! Primitive scalar-normal hypotheses for the unchanged trajectory prior. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

def scalarNormalTimes {Λ : Type*} (E : Set (Λ × ℝ)) : Set ℝ :=
  {t | ∃ l, (l, t) ∈ E}

structure ScalarNormalHyp {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (ν : Measure Λ) (E : Set (Λ × ℝ))
    (F : ℝ → ℝ) (S : ℝ → Set ℝ) (K ζ d : ℝ) : Prop where
  event_measurable : MeasurableSet E
  unit_time : E ⊆ univ ×ˢ Icc (0 : ℝ) 1
  coefficients : ∀ p ∈ E, D.Bounded K p.1
  row_measurable : Measurable F
  row_bounded : ∀ t, |F t| ≤ K
  row_comparison : ∀ p ∈ E, ∀ q ∈ E, |F p.2 - F q.2| ≤ K * (|p.2 - q.2| + ζ)
  residual_comparison : ∀ p ∈ E, ∀ q ∈ E,
    |D.residual F p.1 p.2 - D.residual F q.1 q.2| ≤
      K * (|p.2 - q.2| + |D.x p.1 p.2 - D.x q.1 q.2| + |D.y p.1 p.2 - D.y q.1 q.2| + ζ)
  support_AD : ∀ t, IntervalAD ζ d K (S t)
  support_mem : ∀ p ∈ E, D.scalar F p.1 p.2 ∈ S p.2
  spatial_cap : ∀ t a b r : ℝ, ζ ≤ r →
    ν.real {l | (l, t) ∈ E ∧ D.x l t ∈ Icc a (a + r) ∧ D.y l t ∈ Icc b (b + r)} ≤ K * r ^ (1 + d)

namespace ScalarNormalHyp

variable {Λ : Type*} [MeasurableSpace Λ] {D : ScalarMotion Λ} {ν : Measure Λ}
  {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d : ℝ}
  (h : ScalarNormalHyp D ν E F S K ζ d)

include h

theorem active_unit_time : scalarNormalTimes E ⊆ Icc (0 : ℝ) 1 := by
  rintro t ⟨l, hl⟩
  exact (h.unit_time hl).2

theorem active_row_comparison : ∀ t ∈ scalarNormalTimes E, ∀ s ∈ scalarNormalTimes E,
    |F t - F s| ≤ K * (|t - s| + ζ) := by
  rintro t ⟨l, hl⟩ s ⟨l', hl'⟩
  exact h.row_comparison (l, t) hl (l', s) hl'

theorem active_bounds (hK : 1 ≤ K) {l : Λ} {t : ℝ} (hl : (l, t) ∈ E) :
    |D.x l t| ≤ 3 * K ∧ |D.y l t| ≤ 2 * K ∧
      |D.residual F l t| ≤ 4 * K ^ 2 ∧ |D.scalar F l t| ≤ 5 * K ^ 2 :=
  D.bounds_at_unit_time hK (h.coefficients _ hl) (h.unit_time hl).2 (h.row_bounded t)

theorem anchor_scalar_joint_cap [IsFiniteMeasure ν] (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : d ≤ 1)
    (t a b r : ℝ) (hr : ζ ≤ r) :
    ν.real {l | (l, t) ∈ E ∧ D.scalar F l t ∈ Icc a (a + r) ∧ D.y l t ∈ Icc b (b + r)} ≤
      16 * K ^ 3 * r ^ (1 + d) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hrpos : 0 < r := hζ.trans_le hr
  let center := a + F t * b
  let R := 4 * K * r
  have hrR : r ≤ R := by dsimp [R]; nlinarith
  have hsub : {l | (l, t) ∈ E ∧ D.scalar F l t ∈ Icc a (a + r) ∧ D.y l t ∈ Icc b (b + r)} ⊆
      {l | (l, t) ∈ E ∧ D.x l t ∈ Icc (center - 2 * K * r) (center - 2 * K * r + R) ∧
        D.y l t ∈ Icc b (b + R)} := by
    intro l hl
    have hs : |(D.x l t - F t * D.y l t) - (center - F t * b)| ≤ r := by
      have hscalar : D.x l t - F t * D.y l t ∈ Icc a (a + r) := hl.2.1
      dsimp [center]
      rw [show a + F t * b - F t * b = a by ring, abs_le]
      constructor <;> linarith [hscalar.1, hscalar.2]
    have hy : |D.y l t - b| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [hl.2.2.1, hl.2.2.2]
    have hs' : |((D.x l t) - F t * D.y l t - 0 * 0) - (center - F t * b - 0 * 0)| ≤ r := by
      simpa only [zero_mul, sub_zero] using hs
    have hx := scalar_shear_displacement hK0 (h.row_bounded t) (show |(0 : ℝ)| ≤ K by simpa using hK0) hs'
    simp only [sub_self, abs_zero, add_zero] at hx
    have hxy := mul_le_mul_of_nonneg_left hy hK0
    have hx' : |D.x l t - center| ≤ 2 * K * r := by nlinarith
    obtain ⟨hlo, hhi⟩ := abs_le.mp hx'
    refine ⟨hl.1, ⟨by linarith, ?_⟩, ⟨hl.2.2.1, by linarith [hl.2.2.2]⟩⟩
    dsimp [R]
    linarith
  have hmass := (measureReal_mono hsub (measure_ne_top ν _)).trans
    (h.spatial_cap t (center - 2 * K * r) b R (hr.trans hrR))
  have hpow : (4 * K) ^ (1 + d) ≤ (4 * K) ^ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 4 * K)
      (by linarith : 1 + d ≤ (2 : ℝ))
    simpa only [Real.rpow_two] using hh
  apply hmass.trans
  dsimp [R]
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * K) hrpos.le]
  calc
    _ ≤ K * ((4 * K) ^ 2 * r ^ (1 + d)) := by gcongr
    _ = _ := by ring

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
