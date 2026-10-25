import Submission.Obl.k4_matching_endpoint_volume.EndpointSlice

/-!
# The endpoint volume estimate

Fubini in the final time reduces this to the internal-time endpoint estimate.
-/

namespace Submission.Obl.k4_matching_endpoint_volume

open Set MeasureTheory
open scoped ENNReal BigOperators

/-- The final time and all low jets, with low jets in reverse derivative order. -/
noncomputable def fullEndpoint {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ : ℝ)
    (p : ℝ × (Fin m → ℝ)) : ℝ × (Fin m → ℝ) :=
  (p.1, endpointLow U s₀ p.1 p.2)

lemma continuous_fullEndpoint {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ : ℝ) :
    Continuous (fullEndpoint U s₀) := by
  unfold fullEndpoint endpointLow
  fun_prop

/-- The fixed-final-time polynomial estimate integrates without any dependence
on the initial time or on the shape of the measurable target. -/
theorem endpoint_full_polynomial_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 2 ≤ K → ∀ (U : Fin (m + 1) → ℝ),
      (∀ p : Fin (m + 1), |U p| ≤ K) →
      (∀ p : Fin m, K⁻¹ ≤ |U p.succ - U p.castSucc|) →
      ∀ s₀ : ℝ, ∀ A : Set (ℝ × (Fin m → ℝ)), MeasurableSet A →
      volume ((Icc (-1 : ℝ) 1 ×ˢ separatedUnitCube m K⁻¹) ∩ (fullEndpoint U s₀) ⁻¹' A) ≤
        ENNReal.ofReal (C * K ^ (m * (m + 1) * (m + 2))) * volume A := by
  obtain ⟨C, hC, hslice⟩ := endpoint_slice_polynomial_bound m hm
  refine ⟨C, hC, ?_⟩
  intro K hK U hU hgap s₀ A hA
  let S := (Icc (-1 : ℝ) 1 ×ˢ separatedUnitCube m K⁻¹) ∩ (fullEndpoint U s₀) ⁻¹' A
  have hS : MeasurableSet S :=
    (measurableSet_Icc.prod (isClosed_separatedUnitCube m K⁻¹).measurableSet).inter
      (hA.preimage (continuous_fullEndpoint U s₀).measurable)
  have hpoint (s : ℝ) : volume (Prod.mk s ⁻¹' S) ≤
      ENNReal.ofReal (C * K ^ (m * (m + 1) * (m + 2))) * volume (Prod.mk s ⁻¹' A) := by
    by_cases hs : |s| ≤ 1
    · have hsI : s ∈ Icc (-1 : ℝ) 1 := abs_le.mp hs
      have heq : Prod.mk s ⁻¹' S = separatedUnitCube m K⁻¹ ∩
          (endpointLow U s₀ s) ⁻¹' (Prod.mk s ⁻¹' A) := by
        ext t
        simp [S, fullEndpoint, hsI]
      rw [heq]
      exact hslice K hK U hU hgap s₀ s hs _ (hA.preimage measurable_prodMk_left)
    · have hsI : s ∉ Icc (-1 : ℝ) 1 := fun h => hs (abs_le.mpr h)
      have heq : Prod.mk s ⁻¹' S = ∅ := by
        ext t
        simp [S, hsI]
      rw [heq, measure_empty]
      exact zero_le
  change volume S ≤ _
  calc
    volume S = ∫⁻ s : ℝ, volume (Prod.mk s ⁻¹' S) := Measure.prod_apply hS
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal (C * K ^ (m * (m + 1) * (m + 2))) *
        volume (Prod.mk s ⁻¹' A) := lintegral_mono hpoint
    _ = ENNReal.ofReal (C * K ^ (m * (m + 1) * (m + 2))) *
        ∫⁻ s : ℝ, volume (Prod.mk s ⁻¹' A) :=
      lintegral_const_mul _ (measurable_measure_prodMk_left hA)
    _ = ENNReal.ofReal (C * K ^ (m * (m + 1) * (m + 2))) * volume A := by
      rw [← Measure.prod_apply hA]
      rfl

/-- The dimension-dependent polynomial factor can be absorbed into a fixed
power of every `K>=2`, as required by the matching proof. -/
theorem endpoint_volume_power_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ (K : ℝ), 2 ≤ K → ∀ (U : Fin (m + 1) → ℝ),
      (∀ p : Fin (m + 1), |U p| ≤ K) →
      (∀ p : Fin m, K⁻¹ ≤ |U p.succ - U p.castSucc|) →
      ∀ s₀ : ℝ, ∀ A : Set (ℝ × (Fin m → ℝ)), MeasurableSet A →
      volume ((Icc (-1 : ℝ) 1 ×ˢ separatedUnitCube m K⁻¹) ∩ (fullEndpoint U s₀) ⁻¹' A) ≤
        ENNReal.ofReal (K ^ A₀) * volume A := by
  obtain ⟨C, hC, hbound⟩ := endpoint_full_polynomial_bound m hm
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  let P : ℕ := m * (m + 1) * (m + 2)
  refine ⟨P + n + 1, by omega, ?_⟩
  intro K hK U hU hgap s₀ A hA
  apply (hbound K hK U hU hgap s₀ A hA).trans
  gcongr
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hconst : C ≤ K ^ n := hn.le.trans (pow_le_pow_left₀ (by norm_num) hK n)
  calc
    C * K ^ P ≤ K ^ n * K ^ P := mul_le_mul_of_nonneg_right hconst (pow_nonneg hK0 _)
    _ = K ^ (P + n) := by rw [pow_add]; ring
    _ ≤ K ^ (P + n + 1) := pow_le_pow_right₀ hK1 (by omega)

end Submission.Obl.k4_matching_endpoint_volume
