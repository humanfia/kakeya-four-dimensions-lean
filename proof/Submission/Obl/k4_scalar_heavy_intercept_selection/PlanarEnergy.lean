/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/PlanarEnergy.lean.
Earlier source credits are retained below. -/

import Submission.Lib.K4ContinuousKakeya.Incidence
import Submission.Obl.k4_scalar_initial_true_horizon.InitialGroup

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open MeasureTheory Set
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- The two-dimensional incidence Kakeya bound in squared cell masses.
The prior and every cell mass are the original, unnormalized measures. -/
theorem planar_kakeya_cell_energy {α ι : Type*} [MeasurableSpace α]
    {C : ℝ} (hC₀ : 0 ≤ C) (hMK : FiniteMK 2 C)
    (θ : Measure α) [IsFiniteMeasure θ]
    (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin 2)) (hΦ : Measurable Φ)
    (a e : α → EuclideanSpace ℝ (Fin 2)) (ha : Measurable a) (he : Measurable e)
    (he₁ : ∀ l, ‖e l‖ = 1) {B : ℝ} (hB : ∀ l, ‖a l‖ ≤ B)
    {r : ℝ} (hr : 0 < r) (R : ℝ) (Λ : Set α) (hΛ : MeasurableSet Λ)
    (F : Finset ι) (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hEm : ∀ j ∈ F, MeasurableSet (E j)) (hEd : (F : Set ι).PairwiseDisjoint E)
    (hER : ∀ j ∈ F, E j ⊆ Metric.closedBall 0 R)
    (c : NNReal) (hc : 0 < c)
    (hpush : ∀ j ∈ F, (μ.restrict {p | p.1 ∈ Λ ∧ Φ p ∈ E j}).map Prod.fst ≤
      c • θ.restrict Λ)
    (htube : ∀ j ∈ F, ∀ p : α × ℝ, p.1 ∈ Λ → Φ p ∈ E j →
      ∀ x ∈ E j, x ∈ tube r (a p.1) (e p.1))
    (β : ℝ) (Q v : ENNReal) (m : ι → ENNReal)
    (hvol : ∀ j ∈ F, v ≤ volume (E j))
    (hsucc : ∀ j ∈ F, m j ^ 2 / Q ≤ Measure.pi (fun _ : Fin 2 => μ)
      {p | (∀ i, (p i).1 ∈ Λ ∧ Φ (p i) ∈ E j) ∧
        β ≤ |Matrix.det (Matrix.of fun i k : Fin 2 => e (p i).1 k)|}) :
    (v * ENNReal.ofReal β / Q / (c : ENNReal) ^ 2) * ∑ j ∈ F, m j ^ 2 ≤
      ENNReal.ofReal (4 * C * r ^ 2) * θ Λ ^ 2 := by
  classical
  have h := incidence_kakeya (n := 2) (by norm_num) hC₀ hMK θ μ Φ hΦ a e ha he he₁ hB
    hr R Λ hΛ F E hEm hEd hER c hc hpush htube β (fun j => m j ^ 2 / Q) hsucc
  norm_num only [Nat.cast_ofNat, sub_self, sub_zero, one_div_one, ENNReal.rpow_one,
    Fin.prod_univ_two] at h
  have hlower :
      (v * ENNReal.ofReal β / Q / (c : ENNReal) ^ 2) * ∑ j ∈ F, m j ^ 2 ≤
        ∑ j ∈ F, volume (E j) * (ENNReal.ofReal β * (m j ^ 2 / Q) / (c : ENNReal) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      _ = v * (ENNReal.ofReal β * (m j ^ 2 / Q) / (c : ENNReal) ^ 2) := by
        simp only [div_eq_mul_inv]
        ring
      _ ≤ _ := mul_le_mul' (hvol j hj) le_rfl
  simpa [pow_two, mul_assoc] using hlower.trans h

/-- A Kakeya square-energy bound forces a fixed amount of occupied
base area, independently of the size of the original group mass. -/
theorem cell_count_floor_of_energy {ι : Type*} (F : Finset ι) (m : ι → ℝ)
    {M A : ℝ} (hM : 0 < M) (hsum : ∑ j ∈ F, m j = M)
    (henergy : ∑ j ∈ F, m j ^ 2 ≤ A * M ^ 2) :
    1 ≤ (F.card : ℝ) * A := by
  have hcs := Submission.Obl.k4_scalar_initial_true_horizon.sq_sum_le_card_mul_sum_sq F m
  rw [hsum] at hcs
  have hmul := mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg F.card : (0 : ℝ) ≤ _)
  have hfinal : M ^ 2 ≤ ((F.card : ℝ) * A) * M ^ 2 := by nlinarith
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hM)).mp (by simpa [mul_comm] using hfinal)

/-- A finite family with a common occupied-area floor and a total cell
budget has a heavy group at exactly the reciprocal support-count scale. -/
theorem heavy_group_of_cell_budget {ι β : Type*} (G : Finset ι)
    (cells : ι → Finset β) (m : ι → ℝ) {M L T : ℝ}
    (hM : 0 < M) (hL : 0 < L) (hm : ∀ g ∈ G, 0 ≤ m g)
    (hsum : M ≤ ∑ g ∈ G, m g)
    (hfloor : ∀ g ∈ G, L ≤ (cells g).card)
    (hbudget : (∑ g ∈ G, ((cells g).card : ℝ)) ≤ T) :
    ∃ g ∈ G, M * L ≤ T * m g := by
  classical
  have hne : G.Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hsum
    linarith
  obtain ⟨g, hg, hmax⟩ := G.exists_max_image m hne
  refine ⟨g, hg, ?_⟩
  have hcount : (G.card : ℝ) * L ≤ T := by
    calc
      _ = ∑ _g ∈ G, L := by simp
      _ ≤ ∑ g ∈ G, ((cells g).card : ℝ) := Finset.sum_le_sum hfloor
      _ ≤ T := hbudget
  have hmass : M ≤ (G.card : ℝ) * m g := by
    apply hsum.trans
    calc
      (∑ g' ∈ G, m g') ≤ ∑ _g' ∈ G, m g := Finset.sum_le_sum hmax
      _ = _ := by simp
  have h₁ := mul_le_mul_of_nonneg_right hmass hL.le
  have h₂ := mul_le_mul_of_nonneg_right hcount (hm g hg)
  nlinarith

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
