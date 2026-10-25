import Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing.UniformBoxes

/-!
# Planar slices of uniform coefficient boxes

The density estimate behind the spread property of the smoothed problem. For a
trajectory whose intercept and slope are uniform on coordinate boxes of radius `r`,
the planar position at a time `t ∈ [0,1]` has density at most `(2r)⁻²`, supported in
the square of radius `2r` around the planar position of the box centres.
All proofs here are original Mathlib proofs.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem.Spread

open Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing

/-- The planar position at time `t` of the trajectory with intercept `b` and slope `s`
(the two observed spatial coordinates). -/
def planarPos (b s : Fin 3 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  ![b 0 + t * s 0, b 1 + t * s 1]

@[simp] theorem planarPos_zero (b s : Fin 3 → ℝ) (t : ℝ) :
    planarPos b s t 0 = b 0 + t * s 0 := rfl

@[simp] theorem planarPos_one (b s : Fin 3 → ℝ) (t : ℝ) :
    planarPos b s t 1 = b 1 + t * s 1 := rfl

theorem continuous_planarPos :
    Continuous (fun p : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ℝ => planarPos p.1.1 p.1.2 p.2) := by
  unfold planarPos
  fun_prop

theorem continuous_planarPos_fixed (b s : Fin 3 → ℝ) :
    Continuous (fun t : ℝ => planarPos b s t) := by
  unfold planarPos
  fun_prop

/-- The volume of a cylinder over a planar set, with the hidden coordinate in `I`. -/
theorem volume_cylinder (B : Set (Fin 2 → ℝ)) (I : Set ℝ) :
    volume {q : Fin 3 → ℝ | Fin.init q ∈ B ∧ q 2 ∈ I} = volume I * volume B := by
  have e := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ))
    (Fin.last 2)
  have hset : {q : Fin 3 → ℝ | Fin.init q ∈ B ∧ q 2 ∈ I} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)) ⁻¹' (I ×ˢ B) := by
    ext q
    have h1 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2) q).1 = q 2 := by
      simp [MeasurableEquiv.piFinSuccAbove_apply]
    have h2 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2) q).2 =
        Fin.init q := by
      funext j
      fin_cases j
      · simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init, Fin.removeNth]
      · simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init, Fin.removeNth]; rfl
    simp only [mem_preimage, mem_prod, h1, h2]
    exact and_comm
  rw [hset]
  have := e.measure_preimage_equiv (I ×ˢ B)
  rw [← volume_pi] at this
  rw [this, Measure.prod_prod]
  rfl


/-- `(a^3)⁻¹ * (a * X) = (a^2)⁻¹ * X` for a finite nonzero `a`. -/
theorem inv_pow_three_mul_mul {a : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) (X : ℝ≥0∞) :
    (a ^ 3)⁻¹ * (a * X) = (a ^ 2)⁻¹ * X := by
  have h3 : a ^ 3 = a ^ 2 * a := by ring
  rw [h3, ENNReal.mul_inv (Or.inl (pow_ne_zero 2 ha)) (Or.inl (ENNReal.pow_ne_top ha')),
    mul_assoc, ← mul_assoc a⁻¹, ENNReal.inv_mul_cancel ha ha', one_mul]

/-- Inner slice estimate: with the slope fixed inside its box, the planar position of a
uniformly perturbed intercept has density at most `(2r)⁻²` on a square of radius `2r`. -/
theorem boxLaw_planarPos_le {r : ℝ} (hr : 0 < r) (c d q2 : Fin 3 → ℝ)
    (hq2 : q2 ∈ coordBox r d) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (W : Set (Fin 2 → ℝ)) :
    boxLaw r c {q1 | planarPos q1 q2 t ∈ W} ≤
      (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume (W ∩ coordBox (2 * r) (planarPos c d t)) := by
  let τ : Fin 2 → ℝ := ![t * q2 0, t * q2 1]
  let B : Set (Fin 2 → ℝ) :=
    (fun u => u + τ) ⁻¹' (W ∩ coordBox (2 * r) (planarPos c d t))
  have hpos (q1 : Fin 3 → ℝ) : planarPos q1 q2 t = Fin.init q1 + τ := by
    funext j
    fin_cases j <;> simp [planarPos, τ, Fin.init]
  have hsub : {q1 | planarPos q1 q2 t ∈ W} ∩ coordBox r c ⊆
      {q : Fin 3 → ℝ | Fin.init q ∈ B ∧ q 2 ∈ Icc (c 2 - r) (c 2 + r)} := by
    intro q1 ⟨hW, hbox⟩
    rw [mem_coordBox_iff] at hbox
    have hq2' := mem_coordBox_iff.mp hq2
    refine ⟨?_, ?_⟩
    · change Fin.init q1 + τ ∈ W ∩ coordBox (2 * r) (planarPos c d t)
      rw [← hpos]
      refine ⟨hW, mem_coordBox_iff.mpr ?_⟩
      have key (j : Fin 3) :
          |(q1 j + t * q2 j) - (c j + t * d j)| ≤ 2 * r := by
        have h1 := hbox j
        have h2 := hq2' j
        calc |(q1 j + t * q2 j) - (c j + t * d j)|
            = |(q1 j - c j) + t * (q2 j - d j)| := by ring_nf
          _ ≤ |q1 j - c j| + |t * (q2 j - d j)| := abs_add_le _ _
          _ ≤ r + r := by
            rw [abs_mul, abs_of_nonneg ht.1]
            exact add_le_add h1 ((mul_le_mul_of_nonneg_left h2 ht.1).trans
              (mul_le_of_le_one_left hr.le ht.2))
          _ = 2 * r := by ring
      intro j
      fin_cases j
      · simpa [planarPos] using key 0
      · simpa [planarPos] using key 1
    · have h := hbox 2
      exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
  have hvolB : volume B = volume (W ∩ coordBox (2 * r) (planarPos c d t)) :=
    measure_preimage_add_right _ τ _
  have h2r : (0 : ℝ) < 2 * r := by linarith
  rw [boxLaw_eq, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (measurableSet_coordBox r c)]
  calc (ENNReal.ofReal (2 * r) ^ 3)⁻¹ * volume ({q1 | planarPos q1 q2 t ∈ W} ∩ coordBox r c)
      ≤ (ENNReal.ofReal (2 * r) ^ 3)⁻¹ *
          volume {q : Fin 3 → ℝ | Fin.init q ∈ B ∧ q 2 ∈ Icc (c 2 - r) (c 2 + r)} := by
        gcongr
    _ = (ENNReal.ofReal (2 * r) ^ 3)⁻¹ *
          (ENNReal.ofReal (2 * r) * volume (W ∩ coordBox (2 * r) (planarPos c d t))) := by
        rw [volume_cylinder, Real.volume_Icc, hvolB]
        congr 3
        ring
    _ = (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume (W ∩ coordBox (2 * r) (planarPos c d t)) :=
        inv_pow_three_mul_mul (ENNReal.ofReal_ne_zero_iff.mpr h2r) ENNReal.ofReal_ne_top _

/-- Slice estimate for an independent pair of uniform boxes (intercept and slope). -/
theorem boxPair_planarPos_le {r : ℝ} (hr : 0 < r) (c d : Fin 3 → ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {W : Set (Fin 2 → ℝ)} (hW : MeasurableSet W) :
    ((boxLaw r c).prod (boxLaw r d)) {q | planarPos q.1 q.2 t ∈ W} ≤
      (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume (W ∩ coordBox (2 * r) (planarPos c d t)) := by
  have := boxLaw_isProbabilityMeasure hr c
  have := boxLaw_isProbabilityMeasure hr d
  have hmeas : MeasurableSet {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | planarPos q.1 q.2 t ∈ W} := by
    apply hW.preimage
    unfold planarPos
    fun_prop
  have hae : ∀ᵐ q2 ∂(boxLaw r d), q2 ∈ coordBox r d := by
    rw [boxLaw_eq]
    exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_coordBox r d)) _
  rw [Measure.prod_apply_symm hmeas]
  calc ∫⁻ q2, boxLaw r c ((fun q1 => (q1, q2)) ⁻¹'
        {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | planarPos q.1 q.2 t ∈ W}) ∂(boxLaw r d)
      ≤ ∫⁻ _q2, (ENNReal.ofReal (2 * r) ^ 2)⁻¹ *
          volume (W ∩ coordBox (2 * r) (planarPos c d t)) ∂(boxLaw r d) := by
        apply lintegral_mono_ae
        filter_upwards [hae] with q2 hq2
        exact boxLaw_planarPos_le hr c d q2 hq2 ht W
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end Submission.Obl.k4_dk4_smoothed_problem.Spread
