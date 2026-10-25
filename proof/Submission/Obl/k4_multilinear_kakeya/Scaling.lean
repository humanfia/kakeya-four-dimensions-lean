import Submission.Obl.k4_multilinear_kakeya.Plane

namespace Submission.Obl.k4_multilinear_kakeya

open MeasureTheory Set
open scoped ENNReal

lemma lintegral_smul_eq {n : ℕ} {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    (∫⁻ x, f x) = ENNReal.ofReal (r ^ n) * ∫⁻ x, f (r • x) := by
  let g : EuclideanSpace ℝ (Fin n) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
    (Homeomorph.smulOfNeZero r hr.ne').toMeasurableEquiv
  have hmap := lintegral_map_equiv (μ := volume) f g
  change (∫⁻ x, f x ∂Measure.map (fun x => r • x) volume) =
    (∫⁻ x, f (r • x)) at hmap
  rw [Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure] at hmap
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  rw [hdim, abs_of_pos (inv_pos.mpr (pow_pos hr n)),
    ENNReal.ofReal_inv_of_pos (pow_pos hr n)] at hmap
  rw [← hmap, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]

lemma smul_mem_lineTube_iff {n : ℕ} {r : ℝ} (hr : 0 < r)
    (a e x : EuclideanSpace ℝ (Fin n)) :
    r • x ∈ lineTube r a e ↔ x ∈ lineTube 1 (r⁻¹ • a) e := by
  constructor
  · intro hx
    obtain ⟨y, ⟨t, rfl⟩, hdist⟩ := Metric.mem_thickening_iff.mp hx
    change dist (r • x) (a + t • e) < r at hdist
    apply Metric.mem_thickening_iff.mpr
    refine ⟨r⁻¹ • a + (r⁻¹ * t) • e, ⟨r⁻¹ * t, rfl⟩, ?_⟩
    have hid : r • (r⁻¹ • a + (r⁻¹ * t) • e) = a + t • e := by
      simp [smul_add, smul_smul, hr.ne']
    rw [← hid, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr] at hdist
    nlinarith
  · intro hx
    obtain ⟨y, ⟨t, rfl⟩, hdist⟩ := Metric.mem_thickening_iff.mp hx
    apply Metric.mem_thickening_iff.mpr
    refine ⟨a + (r * t) • e, ⟨r * t, rfl⟩, ?_⟩
    have hid : a + (r * t) • e = r • (r⁻¹ • a + t • e) := by
      simp [smul_add, smul_smul, hr.ne']
    rw [hid, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith

noncomputable def tubeSum {n : ℕ} {N : Fin n → ℕ} (r : ℝ)
    (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ T : ((i : Fin n) → Fin (N i)),
    |(Matrix.of fun i j : Fin n => e i (T i) j).det| *
      ∏ i, (w i (T i) * (lineTube r (a i (T i)) (e i (T i))).indicator
        (fun _ => (1 : ℝ)) x)

lemma tubeSum_smul {n : ℕ} {N : Fin n → ℕ} {r : ℝ} (hr : 0 < r)
    (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    tubeSum r a e w (r • x) = tubeSum 1 (fun i k => r⁻¹ • a i k) e w x := by
  unfold tubeSum
  congr 1
  funext T
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  by_cases hx : x ∈ lineTube 1 (r⁻¹ • a i (T i)) (e i (T i))
  · have hx' := (smul_mem_lineTube_iff hr (a i (T i)) (e i (T i)) x).2 hx
    simp [hx, hx']
  · have hx' : r • x ∉ lineTube r (a i (T i)) (e i (T i)) :=
      fun h => hx ((smul_mem_lineTube_iff hr (a i (T i)) (e i (T i)) x).1 h)
    simp [hx, hx']

lemma scaled_kakeya_integral {n : ℕ} {N : Fin n → ℕ} {r : ℝ} (hr : 0 < r)
    (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ) (p : ℝ) :
    (∫⁻ x, ENNReal.ofReal (tubeSum r a e w x ^ p)) =
      ENNReal.ofReal (r ^ n) *
        ∫⁻ x, ENNReal.ofReal (tubeSum 1 (fun i k => r⁻¹ • a i k) e w x ^ p) := by
  rw [lintegral_smul_eq hr]
  simp_rw [tubeSum_smul hr]

theorem kakeya_scaling {n : ℕ} {C : ℝ}
    (h : ∀ (N : Fin n → ℕ)
      (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
      (w : (i : Fin n) → Fin (N i) → ℝ),
      (∀ i k, ‖e i k‖ = 1) → (∀ i k, 0 ≤ w i k) →
      (∫⁻ x, ENNReal.ofReal (tubeSum 1 a e w x ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤
        ENNReal.ofReal (C * ∏ i, (∑ k, w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1))))
    {r : ℝ} (hr : 0 < r) (N : Fin n → ℕ)
    (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ)
    (he : ∀ i k, ‖e i k‖ = 1) (hw : ∀ i k, 0 ≤ w i k) :
    (∫⁻ x, ENNReal.ofReal (tubeSum r a e w x ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤
      ENNReal.ofReal (C * r ^ n * ∏ i, (∑ k, w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1))) := by
  rw [scaled_kakeya_integral hr]
  calc
    ENNReal.ofReal (r ^ n) *
        (∫⁻ x, ENNReal.ofReal
          (tubeSum 1 (fun i k => r⁻¹ • a i k) e w x ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤
      ENNReal.ofReal (r ^ n) *
        ENNReal.ofReal (C * ∏ i, (∑ k, w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1))) := by
      gcongr
      exact h N _ e w he hw
    _ = _ := by
      rw [← ENNReal.ofReal_mul (pow_nonneg hr.le n)]
      congr 1
      ring

end Submission.Obl.k4_multilinear_kakeya
