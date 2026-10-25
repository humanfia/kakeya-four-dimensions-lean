/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFrozenCollisions.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFrozenCollisions.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLocalModel
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry

/-! Freezing actual scalar collisions at the original mesh representatives. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem scalar_dot_freeze {f G : ℝ → ℝ} {K p u t v v' w w' : ℝ}
    (hK : 1 ≤ K) (hp : 0 ≤ p) (hf0 : f 0 = 0)
    (hf : ∀ x y, |f x - f y| ≤ |x - y|)
    (hG : ∀ x y, |G x - G y| ≤ K * |x - y|)
    (hut : |u - t| ≤ p) (ht : |t| ≤ 1)
    (hv : |v| ≤ K) (hv' : |v'| ≤ K) (hGv : |G v| ≤ K) (hGv' : |G v'| ≤ K)
    (hvw : |v - w| ≤ p) (hvw' : |v' - w'| ≤ p) :
    |(u * (G v - G v') + f u * (v - v')) -
      (t * (G w - G w') + f t * (w - w'))| ≤ (6 * K + 2 * K ^ 2) * p := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hft : |f t| ≤ K := by
    have h := hf t 0
    rw [hf0, sub_zero, sub_zero] at h
    exact h.trans (ht.trans hK)
  have hφ : |(-f u) - (-f t)| ≤ K * p := by
    rw [neg_sub_neg, abs_sub_comm]
    exact (hf u t).trans (hut.trans (by nlinarith))
  have h := scalar_collision_dot_quantization (u := u) (uk := t) (u₀ := 0)
    (G := G v) (G' := G v') (Gj := G w) (Gj' := G w')
    (φu := -f u) (φk := -f t) (φ₀ := 0)
    hK0 hp hut (by simpa only [sub_zero] using ht) hGv hGv'
    ((hG v w).trans (mul_le_mul_of_nonneg_left hvw hK0))
    ((hG v' w').trans (mul_le_mul_of_nonneg_left hvw' hK0)) hφ
    (by simpa only [sub_zero, abs_neg] using hft) hv hv' hvw hvw'
  simpa only [sub_zero, neg_mul, sub_neg_eq_add] using h

/-- Both the rectangle ceiling and the dot-support estimate keep their
complete error, including the original first starting-bin uncertainty. -/
theorem frozen_scalar_collision_relation {D D' z z' base p C Q : ℝ}
    (hactual : |D - (z' - z)| ≤ C * p) (hfreeze : |D - D'| ≤ Q * p)
    (hbin : |z - base| ≤ p) :
    |(z' - z) - D'| ≤ (C + Q) * p ∧ |D' - (z' - base)| ≤ (C + Q + 1) * p := by
  have hfirst : |(z' - z) - D'| ≤ (C + Q) * p := by
    calc
      _ ≤ |(z' - z) - D| + |D - D'| := abs_sub_le _ _ _
      _ ≤ (C + Q) * p := by
        rw [abs_sub_comm (z' - z) D]
        linarith
  refine ⟨hfirst, ?_⟩
  have hbin' : |(z' - z) - (z' - base)| ≤ p := by
    have he : (z' - z) - (z' - base) = base - z := by ring
    rw [he, abs_sub_comm]
    exact hbin
  have ht := abs_sub_le D' (z' - z) (z' - base)
  rw [abs_sub_comm D' (z' - z)] at ht
  linarith

theorem bounded_grid_slope_representatives {Λ : Type*} (A : Set Λ) (v : Λ → ℝ) (G : ℝ → ℝ)
    {K p : ℝ} (hK : 1 ≤ K) (hp : 0 < p) (hp1 : p ≤ 1)
    (hG : ∀ x y, |G x - G y| ≤ K * |x - y|)
    (hbound : ∀ l ∈ A, |v l| ≤ K ∧ |G (v l)| ≤ K)
    (J : Finset ℤ) (hJ : ∀ j ∈ J, ∃ l ∈ A, ⌊v l / p⌋ = j) :
    ∀ j ∈ J, |p * j| ≤ 2 * K + 1 ∧ |G (p * j)| ≤ 2 * K + 1 := by
  intro j hj
  obtain ⟨l, hl, hindex⟩ := hJ j hj
  have hnear := (mesh_lower_endpoint hp hindex).2.le
  have hv := (hbound l hl).1
  have hg := (hbound l hl).2
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hgv : |G (p * j) - G (v l)| ≤ K * p := by
    apply (hG _ _).trans
    apply mul_le_mul_of_nonneg_left _ hK0
    simpa only [abs_sub_comm] using hnear
  constructor
  · have h := abs_sub_le (p * j) (v l) 0
    simp only [sub_zero] at h
    rw [abs_sub_comm (p * j) (v l)] at h
    linarith
  · have h := abs_sub_le (G (p * j)) (G (v l)) 0
    simp only [sub_zero] at h
    nlinarith

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
