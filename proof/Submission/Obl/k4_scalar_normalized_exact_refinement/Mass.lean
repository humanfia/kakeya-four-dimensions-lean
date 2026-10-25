import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open scoped ENNReal

lemma ofReal_assignment_normalizer {X ι Γ : Type*}
    [MeasurableSpace X] [Fintype ι]
    (ν : Γ → Measure X) (w : Γ → ℝ) (γ : ι → Γ) (A : ι → Set X) (dt : ℝ)
    (hprob : ∀ g, IsProbabilityMeasure (ν g)) (hw : ∀ g, 0 ≤ w g) (hdt : 0 ≤ dt) :
    ENNReal.ofReal (∑ i, w (γ i) * dt * (ν (γ i) (A i)).toReal) =
      ENNReal.ofReal dt * ∑ i, ENNReal.ofReal (w (γ i)) * ν (γ i) (A i) := by
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (mul_nonneg (hw (γ i)) hdt) ENNReal.toReal_nonneg), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let : IsProbabilityMeasure (ν (γ i)) := hprob (γ i)
  rw [ENNReal.ofReal_mul (mul_nonneg (hw (γ i)) hdt), ENNReal.ofReal_mul (hw (γ i)),
    ENNReal.ofReal_toReal (measure_ne_top (ν (γ i)) (A i))]
  ring

/-- Original assignment weights, multiplied by the common time length, have
normalizer at most one. -/
lemma assignment_normalizer_le_one {X ι Γ J : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ] [Fintype J]
    (ν : Γ → Measure X) (w : Γ → ℝ) (γ : ι → Γ) (j : ι → J) (A : ι → Set X)
    (dt : ℝ) (hdt : 0 ≤ dt) (hcard : dt * (Fintype.card J : ℝ) = 1)
    (hprob : ∀ g, IsProbabilityMeasure (ν g)) (hw0 : ∀ g, 0 ≤ w g) (hw : ∑ g, w g = 1)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) :
    (∑ i, w (γ i) * dt * (ν (γ i) (A i)).toReal) ≤ 1 := by
  have hnn : 0 ≤ ∑ i, w (γ i) * dt * (ν (γ i) (A i)).toReal :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hw0 (γ i)) hdt) ENNReal.toReal_nonneg)
  have he : ENNReal.ofReal (∑ i, w (γ i) * dt * (ν (γ i) (A i)).toReal) ≤ 1 := by
    rw [ofReal_assignment_normalizer ν w γ A dt hprob hw0 hdt]
    calc
      _ ≤ ENNReal.ofReal dt * (Fintype.card J : ENNReal) := by
        gcongr
        exact k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal ν w γ j A
          hprob hw0 hw hA hdisj
      _ = 1 := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hdt, hcard, ENNReal.ofReal_one]
  have h := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ∞) he
  simpa only [ENNReal.toReal_ofReal hnn, ENNReal.toReal_one] using h

/-- A selected chart costs at most its full prior assignment times its block duration. -/
lemma selected_mass_le_assignment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (μ : Measure (X × ℝ)) (hμ : μ ≤ ν.prod volume)
    (A : Set X) (C : Set (X × ℝ)) (t₀ dt : ℝ)
    (hC : C ⊆ A ×ˢ Icc t₀ (t₀ + dt)) :
    μ C ≤ ENNReal.ofReal dt * ν A := by
  calc
    μ C ≤ (ν.prod volume) C := hμ C
    _ ≤ (ν.prod volume) (A ×ˢ Icc t₀ (t₀ + dt)) := measure_mono hC
    _ = ENNReal.ofReal dt * ν A := by
      rw [Measure.prod_prod, Real.volume_Icc]
      rw [show t₀ + dt - t₀ = dt by ring, mul_comm]

/-- The weighted union selected by an atlas is bounded by its chart-wise sum. -/
lemma weighted_union_le_sum {X ι Γ : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ]
    (μ : Γ → Measure X) (w : Γ → ENNReal) (γ : ι → Γ) (C : ι → Set X) :
    (∑ g, w g * μ g {q | ∃ i, γ i = g ∧ q ∈ C i}) ≤ ∑ i, w (γ i) * μ (γ i) (C i) := by
  classical
  have h g : μ g {q | ∃ i, γ i = g ∧ q ∈ C i} ≤
      ∑ i, if γ i = g then μ g (C i) else 0 := by
    have hs : {q | ∃ i, γ i = g ∧ q ∈ C i} = ⋃ i : ι, if γ i = g then C i else ∅ := by
      ext q
      simp
    rw [hs]
    simpa only [apply_ite, measure_empty] using
      (measure_iUnion_fintype_le (μ g) (fun i : ι => if γ i = g then C i else ∅))
  calc
    _ ≤ ∑ g, w g * ∑ i, if γ i = g then μ g (C i) else 0 := by gcongr with g; exact h g
    _ = ∑ i, ∑ g, if γ i = g then w g * μ g (C i) else 0 := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      exact Finset.sum_comm
    _ = _ := by simp [eq_comm]

lemma weighted_selected_le_normalizer {X ι Γ : Type*}
    [MeasurableSpace X] [Fintype ι]
    (ν : Γ → Measure X) (μ : Γ → Measure (X × ℝ)) (w : Γ → ℝ)
    (γ : ι → Γ) (A : ι → Set X) (C : ι → Set (X × ℝ)) (dt : ℝ)
    (hprob : ∀ g, IsProbabilityMeasure (ν g)) (hw : ∀ g, 0 ≤ w g) (hdt : 0 ≤ dt)
    (hC : ∀ i, μ (γ i) (C i) ≤ ENNReal.ofReal dt * ν (γ i) (A i)) :
    (∑ i, ENNReal.ofReal (w (γ i)) * μ (γ i) (C i)) ≤
      ENNReal.ofReal (∑ i, w (γ i) * dt * (ν (γ i) (A i)).toReal) := by
  rw [ofReal_assignment_normalizer ν w γ A dt hprob hw hdt, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ENNReal.ofReal (w (γ i)) * (ENNReal.ofReal dt * ν (γ i) (A i)) := by gcongr; exact hC i
    _ = _ := by ring

/-- Cancellation of the full assignment budgets in a normalized mixture. -/
lemma normalized_selected_mixture {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (m : ι → ENNReal) (Z : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 < a i) (hZ : 0 < Z) :
    (∑ i, ENNReal.ofReal (w i * a i / Z) * ((ENNReal.ofReal (a i))⁻¹ * m i)) =
      (ENNReal.ofReal Z)⁻¹ * ∑ i, ENNReal.ofReal (w i) * m i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_div_of_pos hZ, ENNReal.ofReal_mul (hw i), div_eq_mul_inv]
  have h0 := ENNReal.ofReal_ne_zero_iff.mpr (ha i)
  calc
    _ = (ENNReal.ofReal Z)⁻¹ * ENNReal.ofReal (w i) *
        (ENNReal.ofReal (a i) * (ENNReal.ofReal (a i))⁻¹) * m i := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top]; ring

/-- The cost of discarding small prior assignments is bounded by the number of
charts times the prior-mass cutoff. -/
lemma deleted_small_assignments_mass_le {X ι Γ : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ]
    (ν : Γ → Measure X) (μ : Γ → Measure (X × ℝ)) (w : Γ → ENNReal)
    (γ : ι → Γ) (A : ι → Set X) (C : ι → Set (X × ℝ))
    (t₀ : ι → ℝ) (dt : ℝ) (s : Finset ι) (τ : ENNReal)
    (hμ : ∀ g, μ g ≤ (ν g).prod volume) (hw : ∀ g, w g ≤ 1) (hdt : dt ≤ 1)
    (hC : ∀ i, C i ⊆ A i ×ˢ Icc (t₀ i) (t₀ i + dt))
    (hsmall : ∀ i ∈ s, ν (γ i) (A i) ≤ τ) :
    (∑ g, w g * μ g {q | ∃ i, γ i = g ∧ i ∈ s ∧ q ∈ C i}) ≤
      (Fintype.card ι : ENNReal) * τ := by
  classical
  let F : ι → Set (X × ℝ) := fun i => if i ∈ s then C i else ∅
  have heq g : {q | ∃ i, γ i = g ∧ i ∈ s ∧ q ∈ C i} =
      {q | ∃ i, γ i = g ∧ q ∈ F i} := by
    ext q
    simp [F]
  have hdt' : ENNReal.ofReal dt ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hdt
  calc
    _ = ∑ g, w g * μ g {q | ∃ i, γ i = g ∧ q ∈ F i} := by simp_rw [heq]
    _ ≤ ∑ i, w (γ i) * μ (γ i) (F i) := weighted_union_le_sum μ w γ F
    _ ≤ ∑ _i : ι, τ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · change w (γ i) * μ (γ i) (if i ∈ s then C i else ∅) ≤ τ
        rw [ite_eq_left hi]
        calc
          _ ≤ w (γ i) * (ENNReal.ofReal dt * ν (γ i) (A i)) := by
            gcongr
            exact selected_mass_le_assignment (ν (γ i)) (μ (γ i)) (hμ (γ i))
              (A i) (C i) (t₀ i) dt (hC i)
          _ ≤ 1 * (1 * τ) := mul_le_mul' (hw (γ i)) (mul_le_mul' hdt' (hsmall i hi))
          _ = τ := by simp
      · simp [F, hi]
    _ = _ := by simp [nsmul_eq_mul]

lemma normalized_selected_mixture_lower_bound {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (m : ι → ENNReal) (Z : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 < a i) (hZ : 0 < Z) (hZ1 : Z ≤ 1)
    {b : ENNReal} (hb : b ≤ ∑ i, ENNReal.ofReal (w i) * m i) :
    b ≤ ∑ i, ENNReal.ofReal (w i * a i / Z) * ((ENNReal.ofReal (a i))⁻¹ * m i) := by
  rw [normalized_selected_mixture w a m Z hw ha hZ]
  have hZ' : ENNReal.ofReal Z ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hZ1
  have hinv : 1 ≤ (ENNReal.ofReal Z)⁻¹ := by
    simpa using ENNReal.inv_le_inv.mpr hZ'
  apply hb.trans
  calc
    _ = 1 * ∑ i, ENNReal.ofReal (w i) * m i := by simp
    _ ≤ _ := mul_le_mul' hinv le_rfl

lemma probability_weight_le_one {Γ : Type*} [Fintype Γ] (w : Γ → ℝ)
    (hw : ∀ g, 0 ≤ w g) (hsum : ∑ g, w g = 1) (g : Γ) : w g ≤ 1 := by
  classical
  simpa only [hsum] using (Finset.single_le_sum (fun i _ => hw i) (Finset.mem_univ g))

/-- Dividing the original assignment budgets by their positive sum produces
 the literal probability weights required by the refinement certificate. -/
lemma normalized_assignment_weights {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hpos : 0 < ∑ i, a i) :
    (∀ i, 0 ≤ a i / ∑ i, a i) ∧ (∑ i, a i / ∑ j, a j) = 1 := by
  constructor
  · intro i
    exact div_nonneg (ha i) hpos.le
  · rw [← Finset.sum_div, div_self (ne_of_gt hpos)]

lemma assignment_normalizer_positive {X ι Γ : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ]
    (ν : Γ → Measure X) (μ : Γ → Measure (X × ℝ)) (w : Γ → ℝ)
    (γ : ι → Γ) (A : ι → Set X) (C : ι → Set (X × ℝ)) (dt : ℝ)
    (hprob : ∀ g, IsProbabilityMeasure (ν g)) (hw : ∀ g, 0 ≤ w g) (hdt : 0 ≤ dt)
    (hC : ∀ i, μ (γ i) (C i) ≤ ENNReal.ofReal dt * ν (γ i) (A i))
    {m : ℝ} (hm : 0 < m)
    (hmass : ENNReal.ofReal m ≤ ∑ g, ENNReal.ofReal (w g) *
      μ g {q | ∃ i, γ i = g ∧ q ∈ C i}) :
    0 < ∑ i, w (γ i) * dt * (ν (γ i) (A i)).toReal := by
  have h := hmass.trans ((weighted_union_le_sum μ (fun g => ENNReal.ofReal (w g)) γ C).trans
    (weighted_selected_le_normalizer ν μ w γ A C dt hprob hw hdt hC))
  exact ENNReal.ofReal_pos.mp ((ENNReal.ofReal_pos.mpr hm).trans_le h)

end Submission.Obl.k4_scalar_normalized_exact_refinement
