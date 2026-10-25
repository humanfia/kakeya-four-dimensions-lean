import Submission.Obl.k4_oss_bad_direction_extraction.Energy
import Submission.Obl.k4_oss_finite_energy_relation.Counting

namespace Submission.Obl.k4_oss_significant_pair_bounds

open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def energy (A C : Finset ℝ) (δ t : ℝ) : ℝ :=
  ((((A.product C).product (A.product C)).filter
    (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      |(q.1.1 - 2 * t * q.1.2) - (q.2.1 - 2 * t * q.2.2)| ≤ 16 * δ)).card : ℝ)

/-- Each projection window has bounded multiplicity in either coordinate. -/
theorem projection_window_le (A C : Finset ℝ) {δ t : ℝ} (hδ : 0 < δ)
    (ht : 1 / 4 ≤ t)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → δ ≤ dist x y) (x : ℝ) :
    (((A.product C).filter (fun p : ℝ × ℝ =>
      |x - (p.1 - 2 * t * p.2)| ≤ 16 * δ)).card : ℝ) ≤
      129 * min (A.card : ℝ) (C.card : ℝ) := by
  have hCcount (a : ℝ) :
      (C.filter (fun c => |x - (a - 2 * t * c)| ≤ 16 * δ)).card ≤ 129 := by
    have h := Submission.Obl.k4_oss_bad_direction_extraction.card_filter_window_le
      C hδ hC (t := 2 * t) (by linarith) (-x) 0 (-a)
    have heq : C.filter (fun c => |x - (a - 2 * t * c)| ≤ 16 * δ) =
        C.filter (fun c => |-x + (2 * t) * 0 - (-a + (2 * t) * c)| ≤ 16 * δ) := by
      apply Finset.filter_congr
      intro c hc
      rw [show -x + (2 * t) * 0 - (-a + (2 * t) * c) =
        -(x - (a - 2 * t * c)) by ring, abs_neg]
    rwa [heq]
  have hAcount (c : ℝ) :
      (A.filter (fun a => |x - (a - 2 * t * c)| ≤ 16 * δ)).card ≤ 129 := by
    have h := Submission.Obl.k4_oss_bad_direction_extraction.card_filter_window_le
      A hδ hA (t := 1) (by norm_num) x 0 (-2 * t * c)
    have heq : A.filter (fun a => |x - (a - 2 * t * c)| ≤ 16 * δ) =
        A.filter (fun a => |x + 1 * 0 - (-2 * t * c + 1 * a)| ≤ 16 * δ) := by
      apply Finset.filter_congr
      intro a ha
      rw [show x + 1 * 0 - (-2 * t * c + 1 * a) = x - (a - 2 * t * c) by ring]
    rwa [heq]
  rw [Submission.Obl.k4_oss_finite_energy_relation.card_product_filter_eq_sum
    A C (fun a c => |x - (a - 2 * t * c)| ≤ 16 * δ)]
  have hleft : (∑ a ∈ A,
      ((C.filter (fun c => |x - (a - 2 * t * c)| ≤ 16 * δ)).card : ℝ)) ≤
      129 * (A.card : ℝ) := by
    calc
      _ ≤ ∑ _a ∈ A, (129 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact_mod_cast hCcount a
      _ = _ := by simp [mul_comm]
  have hright : (∑ a ∈ A,
      ((C.filter (fun c => |x - (a - 2 * t * c)| ≤ 16 * δ)).card : ℝ)) ≤
      129 * (C.card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _c ∈ C, (129 : ℝ) := by
        apply Finset.sum_le_sum
        intro c hc
        have h : ((A.filter (fun a => |x - (a - 2 * t * c)| ≤ 16 * δ)).card : ℝ) ≤ 129 := by
          exact_mod_cast hAcount c
        simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero] using h
      _ = _ := by simp [mul_comm]
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 129)]
  exact le_min hleft hright

/-- Young's counting bound, uniformly on the supported range of slopes. -/
theorem energy_le (A C : Finset ℝ) {δ t : ℝ} (hδ : 0 < δ) (ht : 1 / 4 ≤ t)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → δ ≤ dist x y) :
    energy A C δ t ≤ 129 * (A.card : ℝ) * (C.card : ℝ) *
      min (A.card : ℝ) (C.card : ℝ) := by
  unfold energy
  rw [Submission.Obl.k4_oss_finite_energy_relation.card_product_filter_eq_sum
    (A.product C) (A.product C) (fun p q : ℝ × ℝ =>
      |(p.1 - 2 * t * p.2) - (q.1 - 2 * t * q.2)| ≤ 16 * δ)]
  calc
    _ ≤ ∑ _p ∈ A.product C, 129 * min (A.card : ℝ) (C.card : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact projection_window_le A C hδ ht hA hC (p.1 - 2 * t * p.2)
    _ = _ := by simp [Finset.product_eq_sprod]; ring

/-- The same counting bound after integration against the direction law. -/
theorem averaged_energy_le (A C : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → δ ≤ dist x y)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0) :
    (∫⁻ t, ENNReal.ofReal (energy A C δ t) ∂ν) ≤
      ENNReal.ofReal (129 * (A.card : ℝ) * (C.card : ℝ) *
        min (A.card : ℝ) (C.card : ℝ)) := by
  calc
    _ ≤ ∫⁻ _t : ℝ, ENNReal.ofReal (129 * (A.card : ℝ) * (C.card : ℝ) *
        min (A.card : ℝ) (C.card : ℝ)) ∂ν := by
      apply lintegral_mono_ae
      have hmem : Set.Icc (1 / 4 : ℝ) 1 ∈ ae ν := mem_ae_iff.mpr hν
      filter_upwards [hmem] with t ht
      exact ENNReal.ofReal_le_ofReal (energy_le A C hδ ht.1 hA hC)
    _ = _ := by simp

end Submission.Obl.k4_oss_significant_pair_bounds
