/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockObservations.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockObservations.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockModel
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockGraph
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedSupport

/-! Construct all pointwise scalar-fit observations from primitive original data. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set

def scalarScaledAnchor {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (K c : ℝ) (l : Λ) : ℝ := (6 * K ^ 2) * D.y l c

noncomputable def scalarBlockStart {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (F : ℝ → ℝ) (c H : ℝ) (b : ℤ) (l : Λ) : ℝ :=
  (D.scalar F l c - H * b) / H

noncomputable def scalarBlockRow (g F : ℝ → ℝ) (c H K u : ℝ) : ℝ :=
  -((g (c + H * u) - F c) / H) / (6 * K ^ 2)

namespace ScalarNormalHyp

theorem exists_actual_block_observations {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : MeasureTheory.Measure Λ} {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d c H : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hH : 0 < H) (hH1 : H ≤ 1)
    (hζ : 0 ≤ ζ) (hζH : ζ ≤ H ^ 2) (hc : c ∈ scalarNormalTimes E) (b : ℤ) :
    ∃ g G : ℝ → ℝ, g c = F c ∧
      (∀ t ∈ scalarNormalTimes E, |g t - F t| ≤ 2 * K * ζ) ∧
      scalarBlockRow g F c H K 0 = 0 ∧
      (∀ u t, |scalarBlockRow g F c H K u - scalarBlockRow g F c H K t| ≤ |u - t|) ∧
      (∀ v w, |G v - G w| ≤ |v - w|) ∧
      (∀ l ∈ scalarStartingLabels D E F c H b,
        |scalarScaledAnchor D K c l| ≤ 12 * K ^ 3 ∧
        |G (scalarScaledAnchor D K c l)| ≤ 16 * K ^ 2 ∧
        scalarBlockStart D F c H b l ∈ Icc (0 : ℝ) 1) ∧
      ∀ u l, |u| ≤ 1 → l ∈ scalarStartingLabels D E F c H b → (l, c + H * u) ∈ E →
        |scalarNormalizedValue D F c H b (u, l)| ≤ 13 * K ^ 2 ∧
        |scalarNormalizedValue D F c H b (u, l) -
          (scalarBlockStart D F c H b l + u * G (scalarScaledAnchor D K c l) +
            scalarBlockRow g F c H K u * scalarScaledAnchor D K c l)| ≤ 18 * K ^ 2 * H := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have h1sq : 1 ≤ K ^ 2 := by nlinarith
  have hL : 0 < 6 * K ^ 2 := by positivity
  have hKL : K ≤ 6 * K ^ 2 := by nlinarith
  have hζH' : ζ ≤ H := hζH.trans (by nlinarith)
  obtain ⟨g, hg, hgc, hnear, hnorm, hunit, hmodel⟩ :=
    h.exists_normalized_observation_row hK hH hζ hζH hc
  obtain ⟨G, hG, hGnear, hGbound⟩ := h.exists_starting_residual_graph hK hH hH1 hζH' c b
  have hfzero : scalarBlockRow g F c H K 0 = 0 := by
    simp only [scalarBlockRow, mul_zero, add_zero, hgc, sub_self, zero_div, neg_zero]
  have hfLip u t : |scalarBlockRow g F c H K u - scalarBlockRow g F c H K t| ≤ |u - t| := by
    calc
      _ = |(g (c + H * u) - F c) / H - (g (c + H * t) - F c) / H| / (6 * K ^ 2) := by
        dsimp [scalarBlockRow]
        rw [← sub_div, abs_div, abs_of_pos hL]
        congr 1
        rw [show -((g (c + H * u) - F c) / H) - -((g (c + H * t) - F c) / H) =
          -((g (c + H * u) - F c) / H - (g (c + H * t) - F c) / H) by ring, abs_neg]
      _ ≤ K * |u - t| / (6 * K ^ 2) := div_le_div_of_nonneg_right (hnorm u t) hL.le
      _ ≤ _ := (div_le_iff₀ hL).mpr (by nlinarith [mul_le_mul_of_nonneg_right hKL (abs_nonneg (u - t))])
  have hbds l (hl : l ∈ scalarStartingLabels D E F c H b) :
      |scalarScaledAnchor D K c l| ≤ 12 * K ^ 3 ∧
      |G (scalarScaledAnchor D K c l)| ≤ 16 * K ^ 2 ∧ scalarBlockStart D F c H b l ∈ Icc (0 : ℝ) 1 := by
    have hy := (h.active_bounds hK hl.1).2.1
    have hscaled : |scalarScaledAnchor D K c l| ≤ 12 * K ^ 3 := by
      rw [scalarScaledAnchor, abs_mul, abs_of_pos hL]
      have hh := mul_le_mul_of_nonneg_left hy hL.le
      nlinarith
    exact ⟨hscaled, hGbound l hl, scalarStartingLabels_normalized_value D E F c hH b hl⟩
  refine ⟨g, G, hgc, hnear, hfzero, hfLip, hG, hbds, ?_⟩
  intro u l hu hl hcurrent
  let z := scalarBlockStart D F c H b l
  let q := D.residual F l c
  let φ := (g (c + H * u) - F c) / H
  let Y := D.y l c
  let V := scalarScaledAnchor D K c l
  let Obs := scalarNormalizedValue D F c H b (u, l)
  have hobs : |Obs - (z + u * q - φ * Y)| ≤ H * (K + 5 * K ^ 2) := hmodel (H * b) u l hu hcurrent
  have hz : |z| ≤ 1 := by
    have hz := (hbds l hl).2.2
    exact abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  have hq : |q| ≤ 4 * K ^ 2 := (h.active_bounds hK hl.1).2.2.1
  have hy : |Y| ≤ 2 * K := (h.active_bounds hK hl.1).2.1
  have huq : |u * q| ≤ 4 * K ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hu hq (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hφY : |φ * Y| ≤ 2 * K ^ 2 := by
    rw [abs_mul]
    have hh := mul_le_mul (hunit u hu) hy (abs_nonneg Y) hK0
    nlinarith
  have hpoly : |z + u * q - φ * Y| ≤ 1 + 6 * K ^ 2 :=
    ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith)
  have herr : H * (K + 5 * K ^ 2) ≤ 6 * K ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hH1 (show 0 ≤ K + 5 * K ^ 2 by positivity)
    nlinarith
  have hOb : |Obs| ≤ 13 * K ^ 2 := by
    have hh := abs_sub_le Obs (z + u * q - φ * Y) 0
    rw [sub_zero, sub_zero] at hh
    linarith
  refine ⟨hOb, ?_⟩
  have hqerr : |u * (q - G V)| ≤ 12 * K ^ 2 * H := by
    rw [abs_mul]
    exact (mul_le_mul hu (hGnear l hl) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have he : Obs - (z + u * G V + scalarBlockRow g F c H K u * V) =
      (Obs - (z + u * q - φ * Y)) + u * (q - G V) := by
    dsimp [scalarBlockRow, V, scalarScaledAnchor, φ]
    field_simp
    ring
  change |Obs - (z + u * G V + scalarBlockRow g F c H K u * V)| ≤ 18 * K ^ 2 * H
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hKsq hH.le
  exact (abs_add_le _ _).trans (by linarith)

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
