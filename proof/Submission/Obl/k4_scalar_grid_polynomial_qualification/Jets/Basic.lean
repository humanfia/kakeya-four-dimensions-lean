import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Interface

/-!
# Elementary bounds for zoomed trajectories

Bounds on `zx`, `zy`, `zS` for bounded coefficients at times in `[0,1]`, Lipschitz bounds in the
coefficients, and a counting lemma for the floor bins met by a union of closed balls.
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

theorem abs_zx_le {c : Fin 5 → ℝ} {K t : ℝ} (hc : ∀ e, |c e| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) :
    |zx c t| ≤ 3 * K := by
  unfold zx
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
  have ht0 := ht.1; have ht1 := ht.2
  have hK : 0 ≤ K := le_trans (abs_nonneg _) h0
  have e1 : |c 1 * t| ≤ K := by
    rw [abs_mul, abs_of_nonneg ht0]; nlinarith [abs_nonneg (c 1)]
  have e2 : |c 2 * t ^ 2| ≤ K := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]
    have : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [abs_nonneg (c 2)]
  calc |c 0 + c 1 * t + c 2 * t ^ 2| ≤ |c 0| + |c 1 * t| + |c 2 * t ^ 2| := by
        have := abs_add_le (c 0 + c 1 * t) (c 2 * t ^ 2)
        have := abs_add_le (c 0) (c 1 * t)
        linarith
    _ ≤ 3 * K := by linarith

theorem abs_zy_le {c : Fin 5 → ℝ} {K t : ℝ} (hc : ∀ e, |c e| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) :
    |zy c t| ≤ 2 * K := by
  unfold zy
  have h3 := hc 3; have h4 := hc 4
  have e1 : |c 4 * t| ≤ K := by
    rw [abs_mul, abs_of_nonneg ht.1]; nlinarith [abs_nonneg (c 4), ht.2]
  calc |c 3 + c 4 * t| ≤ |c 3| + |c 4 * t| := abs_add_le _ _
    _ ≤ 2 * K := by linarith

theorem abs_zS_le {F : ℝ → ℝ} {c : Fin 5 → ℝ} {K t : ℝ} (hc : ∀ e, |c e| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hF : |F t| ≤ K) : |zS F c t| ≤ 5 * K ^ 2 + 3 * K := by
  unfold zS
  have hx := abs_zx_le hc ht
  have hy := abs_zy_le hc ht
  have hK : 0 ≤ K := le_trans (abs_nonneg _) hF
  calc |zx c t - F t * zy c t| ≤ |zx c t| + |F t * zy c t| := abs_sub _ _
    _ = |zx c t| + |F t| * |zy c t| := by rw [abs_mul]
    _ ≤ 3 * K + K * (2 * K) := by gcongr
    _ ≤ 5 * K ^ 2 + 3 * K := by nlinarith

/-- The floor bins of side `q` met by a closed ball of radius `q`: at most three. -/
theorem floor_mem_of_mem_closedBall {q x z : ℝ} (hq : 0 < q) (hx : x ∈ Metric.closedBall z q) :
    ⌊x / q⌋ ∈ ({⌊z / q⌋ - 1, ⌊z / q⌋, ⌊z / q⌋ + 1} : Finset ℤ) := by
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have h1 : z / q - 1 ≤ x / q := by
    rw [div_sub_one hq.ne', div_le_div_iff_of_pos_right hq]; linarith
  have h2 : x / q ≤ z / q + 1 := by
    rw [div_add_one hq.ne', div_le_div_iff_of_pos_right hq]; linarith
  have a1 : ⌊z / q⌋ - 1 ≤ ⌊x / q⌋ := by
    have : ⌊z / q - 1⌋ ≤ ⌊x / q⌋ := Int.floor_mono h1
    rwa [Int.floor_sub_one] at this
  have a2 : ⌊x / q⌋ ≤ ⌊z / q⌋ + 1 := by
    have : ⌊x / q⌋ ≤ ⌊z / q + 1⌋ := Int.floor_mono h2
    rwa [Int.floor_add_one] at this
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- A set of reals covered by `m` closed balls of radius `q` meets at most `3 m` floor bins of
side `q`. -/
theorem card_floor_image_le {S : Set ℝ} {q : ℝ} (hq : 0 < q) {m : ℕ} {z : Fin m → ℝ}
    (hS : S ⊆ ⋃ j, Metric.closedBall (z j) q) :
    ∃ B : Finset ℤ, B.card ≤ 3 * m ∧ ∀ x ∈ S, ⌊x / q⌋ ∈ B := by
  classical
  refine ⟨Finset.univ.biUnion (fun j => ({⌊z j / q⌋ - 1, ⌊z j / q⌋, ⌊z j / q⌋ + 1} : Finset ℤ)),
    ?_, ?_⟩
  · calc _ ≤ ∑ j : Fin m, (({⌊z j / q⌋ - 1, ⌊z j / q⌋, ⌊z j / q⌋ + 1} : Finset ℤ)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin m, 3 := Finset.sum_le_sum fun j _ => Finset.card_le_three
      _ = 3 * m := by simp [mul_comm]
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hS hx)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, floor_mem_of_mem_closedBall hq hj⟩

/-- The occupied scalar bins at one time: labelled scalar values in `[-A, A]` meet at most
`3 K (2A / q)^d` floor bins of side `q`. -/
theorem occupied_bins_le {S : Set ℝ} {ζ d K q A : ℝ} (hAD : IntervalAD ζ d K S)
    (hζq : ζ ≤ q) (hq : 0 < q) (hqA : q ≤ 2 * A) (hS : S ⊆ Icc (-A) A) :
    ∃ B : Finset ℤ, (B.card : ℝ) ≤ 3 * (K * (2 * A / q) ^ d) ∧ ∀ x ∈ S, ⌊x / q⌋ ∈ B := by
  obtain ⟨m, z, hcov, hm⟩ := hAD q (2 * A) (-A) hζq hqA
  have hS' : S ⊆ ⋃ j, Metric.closedBall (z j) q := by
    intro x hx
    apply hcov
    refine ⟨hx, ?_⟩
    have := hS hx
    constructor <;> linarith [this.1, this.2]
  obtain ⟨B, hB, hmem⟩ := card_floor_image_le hq hS'
  refine ⟨B, ?_, hmem⟩
  calc (B.card : ℝ) ≤ 3 * m := by exact_mod_cast hB
    _ ≤ 3 * (K * (2 * A / q) ^ d) := by linarith

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
