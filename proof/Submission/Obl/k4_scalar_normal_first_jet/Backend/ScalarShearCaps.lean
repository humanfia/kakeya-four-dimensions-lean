/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarShearCaps.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarShearCaps.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Scalar shears preserve original spatial caps with explicit enlargement. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem scalar_shear_displacement {x x' v v' w w' a b K D : ℝ}
    (hK : 0 ≤ K) (ha : |a| ≤ K) (hb : |b| ≤ K)
    (hS : |(x - a * v - b * w) - (x' - a * v' - b * w')| ≤ D) :
    |x - x'| ≤ D + K * (|v - v'| + |w - w'|) := by
  have hv : |a * (v - v')| ≤ K * |v - v'| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hw : |b * (w - w')| ≤ K * |w - w'| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have he : x - x' = ((x - a * v - b * w) - (x' - a * v' - b * w')) +
      a * (v - v') + b * (w - w') := by ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith)

theorem scalar_frozen_residual_comparison {Λ : Type*} (A : Set Λ)
    (x v w q : Λ → ℝ) {a b K H ζ : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hζ : ζ ≤ H) (ha : |a| ≤ K) (hb : |b| ≤ K)
    (hS : ∀ l ∈ A, ∀ l' ∈ A,
      |(x l - a * v l - b * w l) - (x l' - a * v l' - b * w l')| ≤ H)
    (hR : ∀ l ∈ A, ∀ l' ∈ A,
      |q l - q l'| ≤ K * (|x l - x l'| + |v l - v l'| + |w l - w l'| + ζ)) :
    ∀ l ∈ A, ∀ l' ∈ A,
      |q l - q l'| ≤ (2 * K + K ^ 2) * (|v l - v l'| + |w l - w l'| + H) := by
  intro l hl l' hl'
  have hx := scalar_shear_displacement hK ha hb (hS l hl l' hl')
  have hsum : 0 ≤ |v l - v l'| + |w l - w l'| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have harg : |x l - x l'| + |v l - v l'| + |w l - w l'| + ζ ≤
      2 * H + (K + 1) * (|v l - v l'| + |w l - w l'|) := by linarith
  have h := mul_le_mul_of_nonneg_left harg hK
  nlinarith [hR l hl l' hl', mul_nonneg hK hsum, mul_nonneg (sq_nonneg K) hH]

theorem original_scalar_shear_cap {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A : Set Λ) (x v w : Λ → ℝ)
    {a b K C d ζ r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hζr : ζ ≤ r)
    (ha : |a| ≤ K) (hb : |b| ≤ K)
    (hcap : ∀ c c' c'' q : ℝ, ζ ≤ q →
      ν.real {l | l ∈ A ∧ x l ∈ Icc c (c + q) ∧ v l ∈ Icc c' (c' + q) ∧
        w l ∈ Icc c'' (c'' + q)} ≤ C * q ^ (2 + d)) (c c' c'' : ℝ) :
    ν.real {l | l ∈ A ∧ x l - a * v l - b * w l ∈ Icc c (c + r) ∧
      v l ∈ Icc c' (c' + r) ∧ w l ∈ Icc c'' (c'' + r)} ≤
        C * ((2 + 4 * K) * r) ^ (2 + d) := by
  let R := (2 + 4 * K) * r
  let center := c + a * c' + b * c''
  have hrR : r ≤ R := by dsimp [R]; nlinarith
  have hsub : {l | l ∈ A ∧ x l - a * v l - b * w l ∈ Icc c (c + r) ∧
      v l ∈ Icc c' (c' + r) ∧ w l ∈ Icc c'' (c'' + r)} ⊆
      {l | l ∈ A ∧ x l ∈ Icc (center - (1 + 2 * K) * r) (center - (1 + 2 * K) * r + R) ∧
        v l ∈ Icc c' (c' + R) ∧ w l ∈ Icc c'' (c'' + R)} := by
    intro l hl
    have hS : |(x l - a * v l - b * w l) - (center - a * c' - b * c'')| ≤ r := by
      dsimp [center]
      rw [show c + a * c' + b * c'' - a * c' - b * c'' = c by ring, abs_le]
      constructor <;> linarith [hl.2.1.1, hl.2.1.2]
    have hvc : |v l - c'| ≤ r := by rw [abs_le]; constructor <;> linarith [hl.2.2.1.1, hl.2.2.1.2]
    have hwc : |w l - c''| ≤ r := by rw [abs_le]; constructor <;> linarith [hl.2.2.2.1, hl.2.2.2.2]
    have hx := (scalar_shear_displacement hK ha hb hS).trans
      (show r + K * (|v l - c'| + |w l - c''|) ≤ (1 + 2 * K) * r by
        have h := mul_le_mul_of_nonneg_left (add_le_add hvc hwc) hK
        linarith)
    obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
    refine ⟨hl.1, ⟨by linarith, ?_⟩, ⟨hl.2.2.1.1, by linarith [hl.2.2.1.2]⟩,
      ⟨hl.2.2.2.1, by linarith [hl.2.2.2.2]⟩⟩
    dsimp [R]
    linarith
  exact (measureReal_mono hsub (measure_ne_top ν _)).trans
    (hcap (center - (1 + 2 * K) * r) c' c'' R (hζr.trans hrR))

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
