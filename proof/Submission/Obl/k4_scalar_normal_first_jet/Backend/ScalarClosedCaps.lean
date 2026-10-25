/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarClosedCaps.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarClosedCaps.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib

/-! Half-open original spatial caps suffice for the closed-cap scalar interface. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

/-- Four half-open squares cover a closed square, including all edge
atoms. Above unit scale the unchanged probability prior supplies the cap. -/
theorem original_closed_square_cap_of_half_open {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsProbabilityMeasure ν] (E : Set Λ) (x y : Λ → ℝ)
    {K ζ d : ℝ} (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : 0 ≤ d)
    (hcap : ∀ a b q : ℝ, ζ ≤ q → q ≤ 1 →
      ν {l | l ∈ E ∧ x l ∈ Ico a (a + q) ∧ y l ∈ Ico b (b + q)} ≤
        ENNReal.ofReal (K * q ^ (1 + d))) (a b r : ℝ) (hr : ζ ≤ r) :
    ν.real {l | l ∈ E ∧ x l ∈ Icc a (a + r) ∧ y l ∈ Icc b (b + r)} ≤
      4 * K * r ^ (1 + d) := by
  have hrpos : 0 < r := hζ.trans_le hr
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  by_cases hr1 : r ≤ 1
  · let C : ℝ → ℝ → Set Λ := fun u v =>
      {l | l ∈ E ∧ x l ∈ Ico u (u + r) ∧ y l ∈ Ico v (v + r)}
    have hhalf (u v : ℝ) : ν.real (C u v) ≤ K * r ^ (1 + d) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcap u v r hr hr1)
      simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ K * r ^ (1 + d))] using h
    have hinter (u z : ℝ) (hz : z ∈ Icc u (u + r)) :
        z ∈ Ico u (u + r) ∨ z ∈ Ico (u + r) (u + r + r) := by
      by_cases hlt : z < u + r
      · exact Or.inl ⟨hz.1, hlt⟩
      · exact Or.inr ⟨le_of_not_gt hlt, by linarith [hz.2]⟩
    have hsub : {l | l ∈ E ∧ x l ∈ Icc a (a + r) ∧ y l ∈ Icc b (b + r)} ⊆
        (C a b ∪ C (a + r) b) ∪ (C a (b + r) ∪ C (a + r) (b + r)) := by
      intro l hl
      rcases hinter a (x l) hl.2.1 with hx | hx <;>
        rcases hinter b (y l) hl.2.2 with hy | hy
      · exact Or.inl (Or.inl ⟨hl.1, hx, hy⟩)
      · exact Or.inr (Or.inl ⟨hl.1, hx, hy⟩)
      · exact Or.inl (Or.inr ⟨hl.1, hx, hy⟩)
      · exact Or.inr (Or.inr ⟨hl.1, hx, hy⟩)
    have hfirst := (measureReal_mono (μ := ν) hsub).trans
      (measureReal_union_le (μ := ν) (C a b ∪ C (a + r) b) (C a (b + r) ∪ C (a + r) (b + r)))
    have hleft := measureReal_union_le (μ := ν) (C a b) (C (a + r) b)
    have hright := measureReal_union_le (μ := ν) (C a (b + r)) (C (a + r) (b + r))
    nlinarith [hhalf a b, hhalf (a + r) b, hhalf a (b + r), hhalf (a + r) (b + r)]
  · have hrge : 1 ≤ r := (lt_of_not_ge hr1).le
    have hpow : 1 ≤ r ^ (1 + d) := Real.one_le_rpow hrge (by linarith)
    have hprob : ν.real {l | l ∈ E ∧ x l ∈ Icc a (a + r) ∧ y l ∈ Icc b (b + r)} ≤ 1 := by
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one] using
        (measureReal_mono (μ := ν) (subset_univ {l | l ∈ E ∧ x l ∈ Icc a (a + r) ∧ y l ∈ Icc b (b + r)}))
    nlinarith

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
