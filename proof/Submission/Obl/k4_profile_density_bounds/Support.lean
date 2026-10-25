import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_adapted_oscillation_tests.Frame
import Submission.Obl.k4_scalar_lift_plank.Cells
import Submission.Obl.k4_matching_homogeneous_records.Offsets

open MeasureTheory Set Filter
open scoped ENNReal

/-!
# Observation support from a ball cover

Each physical ball contributes a base cube of volume `(2C/N)^3` and a bounded number of
hidden bins. The a.e. velocity bound contributes at most `49 * K^2` unit velocity bins.
-/

namespace Submission.Obl.k4_profile_density_bounds

open Submission.Obl.k4_scalar_lift_plank (coordinateBins mem_coordinateBins card_coordinateBins_le)
open Submission.Obl.k4_matching_homogeneous_records (floor_sub_bound)

noncomputable def velocityBins (K : ℝ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ => coordinateBins 1 K)

lemma mem_velocityBins {K : ℝ} (hK : 1 ≤ K) {l : Line} (hl : ‖velocity l‖ ≤ K) :
    (fun j => ⌊velocity l j⌋) ∈ velocityBins K := by
  apply Fintype.mem_piFinset.mpr
  intro j
  simpa only [div_one] using mem_coordinateBins (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 1) hK ((PiLp.norm_apply_le (velocity l) j).trans hl)

lemma card_velocityBins_le {K : ℝ} (hK : 1 ≤ K) :
    ((velocityBins K).card : ℝ) ≤ 49 * K ^ 2 := by
  have h := card_coordinateBins_le (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 1) hK
  have hc : ((coordinateBins 1 K).card : ℝ) ≤ 7 * K := by simpa using h
  simp only [velocityBins, Fintype.card_piFinset, Fin.prod_univ_two, Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) (coordinateBins 1 K).card]

noncomputable def baseBox (z : EuclideanSpace ℝ (Fin 4)) (δ : ℝ) : Set Base :=
  WithLp.toLp 2 '' Icc (fun j : Fin 3 => z j.castSucc - δ)
    (fun j : Fin 3 => z j.castSucc + δ)

lemma mem_baseBox_iff (z : EuclideanSpace ℝ (Fin 4)) (δ : ℝ) (x : Base) :
    x ∈ baseBox z δ ↔ ∀ j : Fin 3, |x j - z j.castSucc| ≤ δ := by
  simp only [baseBox, mem_image, mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩ j
    exact abs_le.mpr ⟨by linarith [hv1 j], by linarith [hv2 j]⟩
  · intro hx
    refine ⟨WithLp.ofLp x, ⟨?_, ?_⟩, by simp⟩
    · intro j
      linarith [(abs_le.mp (hx j)).1]
    · intro j
      linarith [(abs_le.mp (hx j)).2]

lemma measurableSet_baseBox (z : EuclideanSpace ℝ (Fin 4)) (δ : ℝ) :
    MeasurableSet (baseBox z δ) := by
  have heq : baseBox z δ = WithLp.ofLp ⁻¹' Icc
      (fun j : Fin 3 => z j.castSucc - δ) (fun j : Fin 3 => z j.castSucc + δ) := by
    ext x
    simp only [baseBox, mem_image, mem_preimage]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨WithLp.ofLp x, hx, by simp⟩
  rw [heq]
  exact measurableSet_Icc.preimage (WithLp.measurable_ofLp 2 _)

lemma volume_baseBox (z : EuclideanSpace ℝ (Fin 4)) (δ : ℝ) (hδ : 0 ≤ δ) :
    volume (baseBox z δ) = ENNReal.ofReal ((2 * δ) ^ 3) := by
  rw [baseBox, Submission.Obl.k4_adapted_oscillation_tests.volume_box]
  have heq (i : Fin 3) : (z i.castSucc + δ) - (z i.castSucc - δ) = 2 * δ := by ring
  simp only [heq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

noncomputable def hiddenBins (C a w : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌈C + 1⌉) ⌈C + 1⌉).image (fun j => ⌊w / a⌋ + j)

lemma card_hiddenBins_le {C : ℝ} (hC : 0 ≤ C) (a w : ℝ) :
    ((hiddenBins C a w).card : ℝ) ≤ 2 * C + 5 := by
  have hcard := Finset.card_image_le (s := Finset.Icc (-⌈C + 1⌉) ⌈C + 1⌉)
    (f := fun j => ⌊w / a⌋ + j)
  have hbound := Submission.Obl.k4_scalar_lift_plank.card_ceil_interval_le
    (show 0 ≤ C + 1 by linarith)
  exact (Nat.cast_le (α := ℝ)).mpr hcard |>.trans (by linarith)

lemma mem_hiddenBins {C N a w w' : ℝ} (hC : 0 ≤ C) (hN : 0 < N)
    (ha : 1 / N ≤ a) (hww' : |w' - w| ≤ C / N) :
    ⌊w' / a⌋ ∈ hiddenBins C a w := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hdiff : |w' / a - w / a| ≤ C := by
    rw [← sub_div, abs_div, abs_of_pos ha0]
    apply (div_le_iff₀ ha0).2
    exact hww'.trans (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left ha hC)
  have hf : |((⌊w' / a⌋ - ⌊w / a⌋ : ℤ) : ℝ)| ≤ C + 1 := by
    have h := floor_sub_bound (w' / a) (w / a)
    linarith
  have hab : |(⌊w' / a⌋ - ⌊w / a⌋ : ℤ)| ≤ ⌈C + 1⌉ := by
    exact_mod_cast hf.trans (Int.le_ceil (C + 1))
  apply Finset.mem_image.mpr
  refine ⟨⌊w' / a⌋ - ⌊w / a⌋, ?_, by omega⟩
  exact Finset.mem_Icc.mpr (abs_le.mp hab)

noncomputable def observationSupport {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 4))
    (N K C : ℝ) : Set Observation :=
  ⋃ j : Fin m, (baseBox (z j) (C / N) ×ˢ
    (hiddenBins C (width N 1) (z j 3) : Set ℤ)) ×ˢ (velocityBins K : Set (Fin 2 → ℤ))

lemma measurableSet_observationSupport {m : ℕ}
    (z : Fin m → EuclideanSpace ℝ (Fin 4)) (N K C : ℝ) :
    MeasurableSet (observationSupport z N K C) := by
  apply MeasurableSet.iUnion
  intro j
  exact ((measurableSet_baseBox _ _).prod (Finset.measurableSet _)).prod
    (Finset.measurableSet _)

lemma reference_observationSupport_le {m : ℕ}
    (z : Fin m → EuclideanSpace ℝ (Fin 4)) {N K C : ℝ}
    (hN : 0 < N) (hK : 1 ≤ K) (hC : 0 ≤ C) :
    reference (observationSupport z N K C) ≤
      ENNReal.ofReal ((m : ℝ) * (2 * C / N) ^ 3 * (2 * C + 5) * (49 * K ^ 2)) := by
  have hδ : 0 ≤ C / N := div_nonneg hC hN.le
  calc
    reference (observationSupport z N K C) ≤
        ∑ j : Fin m, reference ((baseBox (z j) (C / N) ×ˢ
          (hiddenBins C (width N 1) (z j 3) : Set ℤ)) ×ˢ
          (velocityBins K : Set (Fin 2 → ℤ))) := by
      exact measure_iUnion_fintype_le reference _
    _ ≤ ∑ j : Fin m, ENNReal.ofReal ((2 * C / N) ^ 3) *
        ENNReal.ofReal (2 * C + 5) * ENNReal.ofReal (49 * K ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      rw [reference, Measure.prod_prod, Measure.prod_prod, volume_baseBox _ _ hδ,
        Measure.count_apply_finset, Measure.count_apply_finset]
      have hh : ((hiddenBins C (width N 1) (z j 3)).card : ENNReal) ≤
          ENNReal.ofReal (2 * C + 5) := by
        exact_mod_cast ENNReal.ofReal_le_ofReal (card_hiddenBins_le hC _ _)
      have hv : ((velocityBins K).card : ENNReal) ≤ ENNReal.ofReal (49 * K ^ 2) := by
        exact_mod_cast ENNReal.ofReal_le_ofReal (card_velocityBins_le hK)
      have hid : 2 * (C / N) = 2 * C / N := by ring
      rw [hid]
      gcongr
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h1 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
      have h2 : 0 ≤ (2 * C / N) ^ 3 := by positivity
      have h3 : 0 ≤ 2 * C + 5 := by positivity
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h1 h2) h3),
        ENNReal.ofReal_mul (mul_nonneg h1 h2), ENNReal.ofReal_mul h1,
        ENNReal.ofReal_natCast]
      ring

noncomputable def supportConstant (C : ℝ) : ℝ := 49 * C * (2 * C) ^ 3 * (2 * C + 5)

lemma supportConstant_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ supportConstant C := by
  unfold supportConstant
  positivity

lemma reference_observationSupport_power_le {m : ℕ}
    (z : Fin m → EuclideanSpace ℝ (Fin 4)) {N K C σ : ℝ}
    (hN : 0 < N) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hm : (m : ℝ) ≤ C * N ^ (4 - σ)) :
    reference (observationSupport z N K C) ≤
      ENNReal.ofReal (supportConstant C * K ^ 2 * N ^ (1 - σ)) := by
  refine (reference_observationSupport_le z hN hK hC).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    (m : ℝ) * (2 * C / N) ^ 3 * (2 * C + 5) * (49 * K ^ 2) ≤
        (C * N ^ (4 - σ)) * (2 * C / N) ^ 3 * (2 * C + 5) * (49 * K ^ 2) := by
      gcongr
    _ = supportConstant C * K ^ 2 * (N ^ (4 - σ) / N ^ 3) := by
      unfold supportConstant
      rw [div_pow]
      ring
    _ = _ := by
      have hid : N ^ (4 - σ) / N ^ 3 = N ^ (1 - σ) := by
        rw [← Real.rpow_natCast N 3, ← Real.rpow_sub hN]
        congr 1
        ring
      rw [hid]

lemma mem_observationSupport {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 4))
    {N K C : ℝ} (hN : 0 < N) (hK : 1 ≤ K) (hC : 0 ≤ C)
    {p : State} (hvel : ‖velocity p.1‖ ≤ K)
    (hp : ∃ j, ‖physical p - z j‖ ≤ C / N) :
    observe N 1 0 p ∈ observationSupport z N K C := by
  obtain ⟨j, hj⟩ := hp
  apply mem_iUnion.mpr
  refine ⟨j, ⟨?_, ?_⟩, ?_⟩
  · apply (mem_baseBox_iff _ _ _).mpr
    intro i
    have hi : base p i = physical p i.castSucc := by fin_cases i <;> rfl
    change |base p i - z j i.castSucc| ≤ C / N
    rw [hi]
    exact (PiLp.norm_apply_le (physical p - z j) i.castSucc).trans hj
  · have ha : 1 / N ≤ width N 1 := by
      simpa [Real.rpow_neg_one] using (width_bounds hN 1).1
    exact mem_hiddenBins hC hN ha ((PiLp.norm_apply_le (physical p - z j) 3).trans hj)
  · simpa only [observe, width_zero, div_one, Finset.mem_coe] using mem_velocityBins hK hvel

lemma ae_velocity_bound (ν : Measure Line) {K : ℝ}
    (hvel : ∀ᵐ l ∂ν, ‖velocity l‖ ≤ K) (E : Set State) :
    ∀ᵐ p ∂selected ν E, ‖velocity p.1‖ ≤ K := by
  apply ae_restrict_of_ae
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le (measurable_velocity.comp measurable_fst).norm measurable_const)).mpr
  filter_upwards [hvel] with l hl
  exact Eventually.of_forall fun _ => hl

lemma ae_mem_observationSupport {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 4))
    (ν : Measure Line) {E : Set State} (hE : MeasurableSet E)
    {N K C : ℝ} (hN : 0 < N) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hvel : ∀ᵐ l ∂ν, ‖velocity l‖ ≤ K)
    (hcover : ∀ p ∈ E, ∃ j, ‖physical p - z j‖ ≤ C / N) :
    ∀ᵐ p ∂selected ν E, observe N 1 0 p ∈ observationSupport z N K C := by
  filter_upwards [ae_restrict_mem hE, ae_velocity_bound ν hvel E] with p hp hv
  exact mem_observationSupport z hN hK hC hv (hcover p hp)

end Submission.Obl.k4_profile_density_bounds
