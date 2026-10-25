-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.WeightedStability.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Stability
import Submission.WZ.Obl.wz_concentrated_convex_factorization.WidthClasses
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Pruning

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open Finset
open wz_concentrated_convex_factorization

/-- Geometric pigeonholing followed by variational selection preserves weighted mass.
The selected coefficient is stable under deleting at most half the selected indices.
The number of classes and every mass loss are explicit. -/
theorem weighted_stable_subfamily {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℝ) (f : Finset ι → ℝ)
    {U θ r b η : ℝ} (hU : 0 < U) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 1 ≤ r)
    (ha : ∀ i ∈ S, a i ≤ U) (hmass : 0 < ∑ i ∈ S, a i)
    (htail : θ * U * S.card ≤ (∑ i ∈ S, a i) / 2)
    (q p : ℕ) (hp : 0 < p) (hgrid : 2 ≤ θ * r ^ q) (hη : 0 ≤ η)
    (hcoef : ∀ R ⊆ S, R.Nonempty → 1 ≤ f R ∧ f R ≤ b)
    (hsmall : η ^ p * b ≤ 1) :
    ∃ R : Finset ι, R ⊆ S ∧ R.Nonempty ∧
      η * (∑ i ∈ S, a i) ≤ 2 * r * (q + 1 : ℝ) * ∑ i ∈ R, a i ∧
      (∀ i ∈ R, ∀ j ∈ R, a i ≤ r * a j) ∧
      (∀ P ⊆ R, (R.card : ℝ) ≤ 2 * P.card → f R ≤ 2 ^ p * f P) := by
  classical
  let A := S.filter fun i => θ * U ≤ a i
  have hAS : A ⊆ S := filter_subset _ _
  have hdiscard : (∑ i ∈ S with ¬ θ * U ≤ a i, a i) ≤ θ * U * S.card := by
    calc
      _ ≤ ∑ _i ∈ S with ¬ θ * U ≤ a _i, θ * U :=
        sum_le_sum fun i hi => (lt_of_not_ge (mem_filter.mp hi).2).le
      _ = θ * U * (S.filter (fun i => ¬ θ * U ≤ a i)).card := by simp [mul_comm]
      _ ≤ θ * U * S.card := by
        gcongr
        exact filter_subset (fun i => ¬ θ * U ≤ a i) S
  have hAmass : (∑ i ∈ S, a i) ≤ 2 * ∑ i ∈ A, a i := by
    have hh := sum_filter_add_sum_filter_not S (fun i => θ * U ≤ a i) a
    change (∑ i ∈ A, a i) + _ = _ at hh
    linarith
  obtain ⟨grid, color, hgridbounds, hcolor⟩ := width_classes hθ (by linarith) hr q hgrid
  obtain ⟨k, hk⟩ := weight_class A (fun i => color (a i / U)) a
  let Q := A.filter fun i => color (a i / U) = k
  have hQA : Q ⊆ A := filter_subset _ _
  have hQS : Q ⊆ S := hQA.trans hAS
  have hQmass : (∑ i ∈ S, a i) ≤ 2 * (q + 1 : ℝ) * ∑ i ∈ Q, a i := by
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hk
    have hk' : (∑ i ∈ A, a i) ≤ (q + 1 : ℝ) * ∑ i ∈ Q, a i := by
      convert hk using 1
      congr 1
      apply Finset.sum_congr
      · ext i
        simp only [Q, Finset.mem_filter]
      · intro i hi
        rfl
    linarith
  have hQpos : 0 < ∑ i ∈ Q, a i := by
    have hq : 0 < (q + 1 : ℝ) := by positivity
    by_contra hh
    have hle : (∑ i ∈ Q, a i) ≤ 0 := le_of_not_gt hh
    have hprod := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * (q + 1 : ℝ)) hle
    linarith
  have hQne : Q.Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty.mp hh, sum_empty] at hQpos
    exact lt_irrefl _ hQpos
  have hcmp (i) (hi : i ∈ Q) : a i ≤ U * grid k ∧ U * grid k ≤ r * a i := by
    have hiA := hQA hi
    have hlo : θ ≤ a i / U := (le_div_iff₀ hU).mpr (mem_filter.mp hiA).2
    have hhi : a i / U ≤ 2 := (div_le_iff₀ hU).mpr (by linarith [ha i (hQS hi)])
    have hh := hcolor (a i / U) hlo hhi
    rw [(mem_filter.mp hi).2] at hh
    constructor
    · exact (div_le_iff₀ hU).mp hh.1 |>.trans_eq (mul_comm _ _)
    · have hmul := mul_le_mul_of_nonneg_left hh.2 hU.le
      have he : U * (r * (a i / U)) = r * a i := by field_simp
      rwa [he] at hmul
  have hQcoef := hcoef Q hQS hQne
  obtain ⟨R, hRQ, hRne, hRcard, hstable⟩ := stable_subfamily Q hQne f
    (fun P hPQ hP => (hcoef P (hPQ.trans hQS) hP).1) p hp hη hQcoef.2 hsmall
  have hQupper : (∑ i ∈ Q, a i) ≤ (U * grid k) * Q.card := by
    calc
      _ ≤ ∑ _i ∈ Q, U * grid k := sum_le_sum fun i hi => (hcmp i hi).1
      _ = _ := by simp [mul_comm]
  have hRlower : (U * grid k) * R.card ≤ r * ∑ i ∈ R, a i := by
    calc
      _ = ∑ _i ∈ R, U * grid k := by simp [mul_comm]
      _ ≤ ∑ i ∈ R, r * a i := sum_le_sum fun i hi => (hcmp i (hRQ hi)).2
      _ = _ := (mul_sum ..).symm
  have hretain : η * (∑ i ∈ Q, a i) ≤ r * ∑ i ∈ R, a i := by
    calc
      _ ≤ η * ((U * grid k) * Q.card) := mul_le_mul_of_nonneg_left hQupper hη
      _ = (U * grid k) * (η * Q.card) := by ring
      _ ≤ (U * grid k) * R.card :=
        mul_le_mul_of_nonneg_left hRcard (mul_nonneg hU.le (hθ.le.trans (hgridbounds k).1))
      _ ≤ _ := hRlower
  refine ⟨R, hRQ.trans hQS, hRne, ?_, ?_, hstable⟩
  · have h1 := mul_le_mul_of_nonneg_left hQmass hη
    have h2 := mul_le_mul_of_nonneg_left hretain (by positivity : 0 ≤ 2 * (q + 1 : ℝ))
    nlinarith
  · intro i hi j hj
    exact (hcmp i (hRQ hi)).1.trans (hcmp j (hRQ hj)).2

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
