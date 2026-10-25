import Submission.Obl.k4_weighted_convex_tubes.FiniteTests
import Submission.Obl.k4_weighted_convex_tubes.SamplingAsymptotics
import Submission.Obl.k4_weighted_convex_tubes.Sampling

namespace Submission.Obl.k4_weighted_convex_tubes

open MeasureTheory Set

def FiniteSelectionPrinciple : Prop :=
  ∀ (n H : ℕ) (p : Fin n → ℝ), (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1) →
    16 ≤ ∑ i, p i → ∀ (U : Fin H → Finset (Fin n)) (t : Fin H → ℝ),
    (∀ h, 0 ≤ t h) →
    (∀ h, (U h).Nonempty → 4 * (∑ i ∈ U h, p i) ≤ t h ∧
      4 * (H : ℝ) ≤ Real.exp (t h / 2)) →
    ∃ S : Finset (Fin n), (∑ i, p i) ≤ 2 * S.card ∧
      ∀ h, ((S ∩ U h).card : ℝ) ≤ t h

theorem sampling_of_finite_selection (hselect : FiniteSelectionPrinciple) : SamplingPrinciple := by
  classical
  intro τ hτ
  obtain ⟨B, hB1, htests⟩ := finite_convex_tests
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB1
  obtain ⟨r₀, hr₀, hslack⟩ := sampling_power_slack hτ hB
  refine ⟨896, by norm_num, r₀, hr₀, ?_⟩
  intro r hr hr100 hrr₀ n x v w A hv hball hw hA hcluster
  have hr1 : r ≤ 1 := by linarith
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hnorm : 0 < 56 * A := by positivity
  obtain ⟨H, P, hH, hP, hcontrol⟩ := htests r hr hr1
  obtain ⟨hM4, htail⟩ := hslack r hr hrr₀
  let M : ℝ := r ^ (-τ) / B
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let p : Fin n → ℝ := fun i => w i / (56 * A)
  have hp0 (i) : 0 ≤ p i := div_nonneg (hw i).le hnorm.le
  have hp1 (i) : p i ≤ 1 := by
    have hconv : Convex ℝ (tube r (x i) (v i)) := (convex_segment _ _).thickening _
    have hh : ENNReal.ofReal (w i * r ^ 2) ≤ ENNReal.ofReal (A * (56 * r ^ 2)) := by
      calc
        _ ≤ ENNReal.ofReal A * volume (tube r (x i) (v i)) := by
          simpa only [Finset.sum_singleton] using
            hcluster (tube r (x i) (v i)) hconv {i} (by simp)
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal (56 * r ^ 2) := by
          gcongr
          exact tube_volume_upper hr.le hr1 (x i) (v i) (hv i)
        _ = _ := (ENNReal.ofReal_mul hA.le).symm
    have hwmax : w i ≤ 56 * A := by
      have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
      exact (mul_le_mul_iff_of_pos_right hr2).mp (by nlinarith [hh'])
    exact (div_le_one hnorm).mpr hwmax
  have hpsum : (∑ i, p i) = (∑ i, w i) / (56 * A) := by
    simp only [p, Finset.sum_div]
  by_cases hsmall : (∑ i, p i) < 16
  · left
    have hh := (div_lt_iff₀ hnorm).mp (hpsum ▸ hsmall)
    linarith
  have hsize : 16 ≤ ∑ i, p i := le_of_not_gt hsmall
  let U : Fin H → Finset (Fin n) := fun h => Finset.univ.filter
    (fun i => tube r (x i) (v i) ⊆ P h)
  let b : Fin H → ℝ := fun h => (volume (P h)).toReal / r ^ 2
  have hb0 (h) : 0 ≤ b h := by dsimp [b]; positivity
  have hmean (h) : (∑ i ∈ U h, p i) ≤ b h / 56 := by
    have hwreal : (∑ i ∈ U h, w i) * r ^ 2 ≤ A * (volume (P h)).toReal := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA.le ENNReal.toReal_nonneg)).mp
      rw [ENNReal.ofReal_mul hA.le, ENNReal.ofReal_toReal (hP h).2.2.2]
      exact hcluster (P h) (hP h).1 (U h) (fun i hi => (Finset.mem_filter.mp hi).2)
    have hwsum : (∑ i ∈ U h, w i) ≤ A * b h := by
      calc
        _ ≤ (A * (volume (P h)).toReal) / r ^ 2 := (le_div_iff₀ hr2).mpr hwreal
        _ = _ := by dsimp [b]; ring
    calc
      _ = (∑ i ∈ U h, w i) / (56 * A) := by simp only [p, Finset.sum_div]
      _ ≤ (A * b h) / (56 * A) := div_le_div_of_nonneg_right hwsum hnorm.le
      _ = _ := by field_simp
  have hb1 (h) (hU : (U h).Nonempty) : 1 ≤ b h := by
    obtain ⟨i, hi⟩ := hU
    have hcontain : tube r (x i) (v i) ⊆ P h := (Finset.mem_filter.mp hi).2
    have hh : r ^ 2 ≤ (volume (P h)).toReal :=
      (ofReal_le_volume_iff (hP h).2.2.2).mp
        ((tube_volume_lower hr (x i) (v i) (hv i)).trans (measure_mono hcontain))
    exact (one_le_div hr2).mpr hh
  let t : Fin H → ℝ := fun h => M * b h
  have ht0 (h) : 0 ≤ t h := mul_nonneg hM (hb0 h)
  have ht (h) (hU : (U h).Nonempty) :
      4 * (∑ i ∈ U h, p i) ≤ t h ∧ 4 * (H : ℝ) ≤ Real.exp (t h / 2) := by
    have hb := hb1 h hU
    constructor
    · calc
        _ ≤ 4 * (b h / 56) := mul_le_mul_of_nonneg_left (hmean h) (by norm_num)
        _ ≤ 4 * b h := by nlinarith [hb0 h]
        _ ≤ M * b h := mul_le_mul_of_nonneg_right hM4 (hb0 h)
    · calc
        _ ≤ 4 * (B * r ^ (-B)) := mul_le_mul_of_nonneg_left hH (by norm_num)
        _ ≤ Real.exp (M / 2) := by simpa only [M, mul_assoc] using htail
        _ ≤ Real.exp (t h / 2) := Real.exp_le_exp.mpr (by dsimp [t]; nlinarith)
  obtain ⟨S, hSmass, hScount⟩ := hselect n H p hp0 hp1 hsize U t ht0 ht
  refine Or.inr ⟨S, ?_, ?_⟩
  · have hh := (div_le_iff₀ hnorm).mp (hpsum ▸ hSmass)
    have hnonneg : 0 ≤ A * (S.card : ℝ) := mul_nonneg hA.le (Nat.cast_nonneg _)
    nlinarith
  · have htest (h) :
        ENNReal.ofReal (((S.filter fun i => tube r (x i) (v i) ⊆ P h).card : ℝ) * r ^ 2) ≤
          ENNReal.ofReal M * volume (P h) := by
      have heq : S ∩ U h = S.filter (fun i => tube r (x i) (v i) ⊆ P h) := by
        ext i
        simp [U]
      have hh := mul_le_mul_of_nonneg_right (hScount h) hr2.le
      rw [heq] at hh
      have halg : t h * r ^ 2 = M * (volume (P h)).toReal := by
        dsimp [t, b]
        field_simp
      rw [halg] at hh
      rw [← ENNReal.ofReal_toReal (hP h).2.2.2, ← ENNReal.ofReal_mul hM]
      exact ENNReal.ofReal_le_ofReal hh
    have hh := hcontrol n x v hv hball M S htest
    have heq : B * M = r ^ (-τ) := by dsimp [M]; field_simp
    rwa [heq] at hh

theorem sampling_principle : SamplingPrinciple :=
  sampling_of_finite_selection (fun _ _ p hp0 hp1 hS U t ht0 ht =>
    exists_good_subset p hp0 hp1 hS U t ht0 ht)

end Submission.Obl.k4_weighted_convex_tubes
