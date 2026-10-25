/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.GeneralPolynomialNorming

open Set MeasureTheory MvPolynomial

namespace Submission.Lib.K4PolynomialNorming

/-- A degree/dimension exponent works uniformly over all source spaces and
cell index types. Finite cell mass ceilings suffice for polynomial small-value deletion.
The observed law need not have a Lebesgue density. Cell diameter and a
polynomial variation bound pay the explicit thickening error L*Delta. -/
theorem finite_cell_polynomial_sublevel_mass_uniform (D n : ℕ) : ∃ C : ℕ,
      ∀ {Ω ι : Type*} [MeasurableSpace Ω] (F : MvPolynomial (Fin n) ℝ), F.totalDegree ≤ D →
        ∀ (μ : Measure Ω) (I : Finset ι) (events : ι → Set Ω) (cells : ι → Set (Fin n → ℝ))
          (z : Ω → Fin n → ℝ),
          (∀ i ∈ I, MeasurableSet (cells i)) → (I : Set ι).PairwiseDisjoint cells →
          (∀ i ∈ I, ∀ u ∈ cells i, ∀ j, |u j| ≤ 1) →
          ∀ A ε L Δ K : ℝ, 2 ≤ A → 0 ≤ ε → 0 ≤ L → 0 ≤ Δ → 0 ≤ K →
          (∀ i ∈ I, ∀ x ∈ cells i, ∀ y ∈ cells i, ∀ j, |y j - x j| ≤ Δ) →
          (∀ i ∈ I, ∀ w ∈ events i, z w ∈ cells i) →
          (∀ i ∈ I, μ (events i) ≤ ENNReal.ofReal K * volume (cells i)) →
          (∀ x y : Fin n → ℝ, (∀ j, |x j| ≤ 1) → (∀ j, |y j| ≤ 1) →
            (∀ j, |y j - x j| ≤ Δ) → |MvPolynomial.eval y F - MvPolynomial.eval x F| ≤ L * Δ) →
          (∃ m, A ^ C * (ε + L * Δ) < |F.coeff m|) →
          μ {w | w ∈ ⋃ i ∈ I, events i ∧ |MvPolynomial.eval (z w) F| ≤ ε} ≤ ENNReal.ofReal (K / A) := by
  classical
  obtain ⟨C, hC⟩ := finite_dimensional_real_polynomial_norming D n
  refine ⟨C, ?_⟩
  intro Ω ι _ F hD μ I events cells z hmeas hdisj hbox A ε L Δ K hA hε hL hΔ hK
    hdiam hmap hcap hLip hgap
  let bad := I.filter (fun i => (events i ∩ {w | |MvPolynomial.eval (z w) F| ≤ ε}).Nonempty)
  let U : Set (Fin n → ℝ) := ⋃ i ∈ bad, cells i
  have hbadI : bad ⊆ I := Finset.filter_subset _ _
  have hUm : MeasurableSet U := by
    apply Finset.measurableSet_biUnion
    exact fun i hi => hmeas i (hbadI hi)
  have hUbox (u : Fin n → ℝ) (hu : u ∈ U) (j : Fin n) : |u j| ≤ 1 := by
    obtain ⟨i, hi, hui⟩ := Set.mem_iUnion₂.mp hu
    exact hbox i (hbadI hi) u hui j
  have hUsmall (u : Fin n → ℝ) (hu : u ∈ U) : |MvPolynomial.eval u F| ≤ ε + L * Δ := by
    obtain ⟨i, hi, hui⟩ := Set.mem_iUnion₂.mp hu
    obtain ⟨w, hwi, hwsmall⟩ := (Finset.mem_filter.mp hi).2
    have hwcell := hmap i (hbadI hi) w hwi
    have hchange := hLip (z w) u (hbox i (hbadI hi) _ hwcell) (hbox i (hbadI hi) _ hui)
      (hdiam i (hbadI hi) _ hwcell _ hui)
    calc
      _ = |(MvPolynomial.eval u F - MvPolynomial.eval (z w) F) + MvPolynomial.eval (z w) F| := by congr 1; ring
      _ ≤ |MvPolynomial.eval u F - MvPolynomial.eval (z w) F| + |MvPolynomial.eval (z w) F| := abs_add_le _ _
      _ ≤ L * Δ + ε := add_le_add hchange hwsmall
      _ = _ := add_comm _ _
  have hUvol : volume U < ENNReal.ofReal A⁻¹ := by
    by_contra hnot
    have hnorm := hC F hD U hUm hUbox A (ε + L * Δ) hA (by positivity) (le_of_not_gt hnot) hUsmall
    obtain ⟨m, hm⟩ := hgap
    exact (not_le_of_gt hm) (hnorm m)
  have hcover : {w | w ∈ ⋃ i ∈ I, events i ∧ |MvPolynomial.eval (z w) F| ≤ ε} ⊆
      ⋃ i ∈ bad, events i := by
    intro w hw
    obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.mp hw.1
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, ⟨w,hwi,hw.2⟩⟩, hwi⟩
  have hdisj' : (bad : Set ι).PairwiseDisjoint cells := by
    intro i hi j hj hij
    exact hdisj (hbadI hi) (hbadI hj) hij
  have hvolsum : volume U = ∑ i ∈ bad, volume (cells i) :=
    measure_biUnion_finset hdisj' (fun i hi => hmeas i (hbadI hi))
  calc
    _ ≤ μ (⋃ i ∈ bad, events i) := measure_mono hcover
    _ ≤ ∑ i ∈ bad, μ (events i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ bad, ENNReal.ofReal K * volume (cells i) := Finset.sum_le_sum fun i hi => hcap i (hbadI hi)
    _ = ENNReal.ofReal K * volume U := by rw [hvolsum, Finset.mul_sum]
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal A⁻¹ := by gcongr
    _ = ENNReal.ofReal (K / A) := by rw [← ENNReal.ofReal_mul hK, div_eq_mul_inv]

end Submission.Lib.K4PolynomialNorming
