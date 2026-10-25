/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups/HeavyCells.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit af6b1867dfbb677a4a0e008effa5b557d8531e7f,
Submission/Obl/k4_scalar_mesh_projection/HeavyCells.lean.
-/

import Submission.Lib.K4ContinuousKakeya.Incidence

namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Set MeasureTheory
open scoped ENNReal NNReal

/-- A second-moment estimate proportional to total mass squared forces
many occupied cells, independently of the size of that total mass. -/
theorem card_mul_ge_of_relative_second_moment {ι : Type*}
    (s : Finset ι) (m : ι → ℝ) (M A : ℝ) (hM : 0 < M)
    (hsum : ∑ i ∈ s, m i = M) (hmoment : ∑ i ∈ s, (m i) ^ 2 ≤ A * M ^ 2) :
    1 ≤ (s.card : ℝ) * A := by
  have hcs : M ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (m i) ^ 2 := by
    rw [← hsum]
    exact sq_sum_le_card_mul_sum_sq
  have hh := hcs.trans (mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg _))
  have hM2 : 0 < M ^ 2 := pow_pos hM _
  nlinarith


/-- Incidence Kakeya at dimension two forces a fixed number of base
cells in every group, using its original prior-duration bound. -/
theorem pair_incidence_cell_count {α ι : Type*} [MeasurableSpace α]
    (C : ℝ) (hC : 0 ≤ C) (hMK : Submission.Lib.K4ContinuousKakeya.FiniteMK 2 C)
    (θ : Measure α) [IsFiniteMeasure θ] (inc : Measure (α × ℝ)) [IsFiniteMeasure inc]
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin 2)) (hΦ : Measurable Φ)
    (a e : α → EuclideanSpace ℝ (Fin 2)) (ha : Measurable a) (he : Measurable e)
    (he1 : ∀ l, ‖e l‖ = 1) (B : ℝ) (hB : ∀ l, ‖a l‖ ≤ B)
    (r R : ℝ) (hr : 0 < r) (Λ : Set α) (hΛ : MeasurableSet Λ)
    (s : Finset ι) (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hEm : ∀ j ∈ s, MeasurableSet (E j)) (hEd : (s : Set ι).PairwiseDisjoint E)
    (hER : ∀ j ∈ s, E j ⊆ Metric.closedBall 0 R)
    (c : ℝ≥0) (hc : 0 < c)
    (hpush : ∀ j ∈ s, (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}).map Prod.fst ≤
      c • θ.restrict Λ)
    (htube : ∀ j ∈ s, ∀ ω : α × ℝ, ω.1 ∈ Λ → Φ ω ∈ E j → ∀ x ∈ E j,
      x ∈ Submission.Lib.K4ContinuousKakeya.tube r (a ω.1) (e ω.1))
    (m : ι → ℝ) (M A area β σ : ℝ)
    (_hm : ∀ j ∈ s, 0 ≤ m j) (hM : 0 < M) (hA : 0 ≤ A)
    (harea : 0 < area) (hβ : 0 < β) (hσ : 0 < σ)
    (hsum : ∑ j ∈ s, m j = M) (hprior : θ Λ ≤ ENNReal.ofReal (A * M))
    (hvol : ∀ j ∈ s, ENNReal.ofReal area ≤ volume (E j))
    (hsucc : ∀ j ∈ s, ENNReal.ofReal (σ * (m j) ^ 2) ≤
      Measure.pi (fun _ : Fin 2 => inc)
        {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
          β ≤ |Matrix.det (Matrix.of fun i k : Fin 2 => e (ω i).1 k)|}) :
    area * β * σ ≤ 4 * C * r ^ 2 * A ^ 2 * (c : ℝ) ^ 2 * (s.card : ℝ) := by
  classical
  have hcR : 0 < (c : ℝ) := hc
  have hc2 : 0 < (c : ℝ) ^ 2 := pow_pos hcR _
  have hmain := Submission.Lib.K4ContinuousKakeya.incidence_kakeya
    (n := 2) (by omega) hC hMK θ inc Φ hΦ a e ha he he1 hB hr R Λ hΛ s E
      hEm hEd hER c hc hpush htube β (fun j => ENNReal.ofReal (σ * (m j) ^ 2)) hsucc
  have hmain' :
      (∑ j ∈ s, volume (E j) *
        (ENNReal.ofReal β * ENNReal.ofReal (σ * (m j) ^ 2) / (c : ℝ≥0∞) ^ 2)) ≤
      ENNReal.ofReal (4 * C * r ^ 2) * (θ Λ) ^ 2 := by
    norm_num [Fin.prod_univ_two, ENNReal.rpow_one] at hmain
    simpa only [pow_two] using hmain
  have hterm (j : ι) : ENNReal.ofReal (area * β * σ / (c : ℝ) ^ 2 * (m j) ^ 2) =
      ENNReal.ofReal area *
        (ENNReal.ofReal β * ENNReal.ofReal (σ * (m j) ^ 2) / (c : ℝ≥0∞) ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hc2,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul harea.le,
      ENNReal.ofReal_mul hσ.le, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ac_rfl
  have hsumNonneg (j : ι) (_hj : j ∈ s) :
      0 ≤ area * β * σ / (c : ℝ) ^ 2 * (m j) ^ 2 := by positivity
  have hlower : ENNReal.ofReal (area * β * σ / (c : ℝ) ^ 2 * ∑ j ∈ s, (m j) ^ 2) ≤
      ∑ j ∈ s, volume (E j) *
        (ENNReal.ofReal β * ENNReal.ofReal (σ * (m j) ^ 2) / (c : ℝ≥0∞) ^ 2) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg hsumNonneg]
    apply Finset.sum_le_sum
    intro j hj
    rw [hterm]
    exact mul_le_mul' (hvol j hj) le_rfl
  have hupper : ENNReal.ofReal (4 * C * r ^ 2) * (θ Λ) ^ 2 ≤
      ENNReal.ofReal (4 * C * r ^ 2 * (A * M) ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (4 * C * r ^ 2) * (ENNReal.ofReal (A * M)) ^ 2 := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow (mul_nonneg hA hM.le),
          ← ENNReal.ofReal_mul (by positivity)]
  have hreal : area * β * σ / (c : ℝ) ^ 2 * (∑ j ∈ s, (m j) ^ 2) ≤
      4 * C * r ^ 2 * (A * M) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlower.trans (hmain'.trans hupper))
  rw [div_mul_eq_mul_div] at hreal
  have hreal' := (div_le_iff₀ hc2).mp hreal
  have hcs : M ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, (m j) ^ 2 := by
    rw [← hsum]
    exact sq_sum_le_card_mul_sum_sq
  have hproduct : (area * β * σ) * M ^ 2 ≤
      (4 * C * r ^ 2 * A ^ 2 * (c : ℝ) ^ 2 * (s.card : ℝ)) * M ^ 2 := by
    calc
      _ ≤ (area * β * σ) * ((s.card : ℝ) * ∑ j ∈ s, (m j) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (s.card : ℝ) * (area * β * σ * ∑ j ∈ s, (m j) ^ 2) := by ring
      _ ≤ (s.card : ℝ) * ((4 * C * r ^ 2 * (A * M) ^ 2) * (c : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hreal' (Nat.cast_nonneg _)
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (pow_pos hM 2)).mp (by simpa only [mul_comm] using hproduct)

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching


namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching

/-- The physical time scale cancels between the original prior-duration
bound and the cell incidence ceiling. Unit direction normalization and
pair breadth then cost only eight powers of the common slack. -/
theorem scalar_pair_cell_count_scaled
    (C K h ξ r A c β σ : ℝ) (n : ℕ)
    (hC : 0 < C) (hK : 1 ≤ K) (hh : 0 < h) (hξ : 0 < ξ)
    (hr : 0 ≤ r) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hrb : r ≤ 4 * ξ) (hAb : A ≤ K / h) (hcb : c ≤ K * h * ξ)
    (hβ : 1 / (4 * K ^ 3) ≤ β) (hσ : 1 / K ≤ σ)
    (hcount : ξ ^ 2 * β * σ ≤ 4 * C * r ^ 2 * A ^ 2 * c ^ 2 * (n : ℝ)) :
    1 / (256 * C * K ^ 8) ≤ ξ ^ 2 * (n : ℝ) := by
  have hKp : 0 < K := by linarith
  have hscale : ξ ^ 2 * (β * σ) ≤
      (64 * C * K ^ 4 * ξ ^ 2 * (n : ℝ)) * ξ ^ 2 := by
    calc
      _ = ξ ^ 2 * β * σ := by ring
      _ ≤ 4 * C * r ^ 2 * A ^ 2 * c ^ 2 * (n : ℝ) := hcount
      _ ≤ 4 * C * (4 * ξ) ^ 2 * (K / h) ^ 2 * (K * h * ξ) ^ 2 * (n : ℝ) := by
        gcongr
      _ = _ := by field_simp; ring
  have hcancel : β * σ ≤ 64 * C * K ^ 4 * ξ ^ 2 * (n : ℝ) := by
    apply (mul_le_mul_iff_left₀ (pow_pos hξ 2)).mp
    simpa only [mul_comm] using hscale
  have hβp : 0 ≤ β := (by positivity : (0 : ℝ) ≤ 1 / (4 * K ^ 3)).trans hβ
  have hprod : 1 / (4 * K ^ 4) ≤ β * σ := by
    have hmul := mul_le_mul hβ hσ (by positivity : (0 : ℝ) ≤ 1 / K) hβp
    convert hmul using 1 <;> field_simp <;> ring
  have hone : 1 ≤ (β * σ) * (4 * K ^ 4) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * K ^ 4)).mp hprod
  have htrans := hone.trans (mul_le_mul_of_nonneg_right hcancel (by positivity))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 256 * C * K ^ 8)).mpr
  convert htrans using 1 <;> ring

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
