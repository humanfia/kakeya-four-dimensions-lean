import Mathlib

namespace Submission.Obl.k4_multilinear_kakeya

open MeasureTheory Set
open scoped ENNReal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def lineTube {n : ℕ} (r : ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.thickening r (Set.range fun t : ℝ => a + t • e)

lemma measurableSet_lineTube {n : ℕ} (r : ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (lineTube r a e) :=
  Metric.isOpen_thickening.measurableSet

lemma matrix_preimage_volume {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.det ≠ 0) {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    volume ((fun x : EuclideanSpace ℝ (Fin n) => M.mulVec (WithLp.ofLp x)) ⁻¹' s) =
      ENNReal.ofReal |M.det⁻¹| * volume s := by
  let L := Matrix.toLin' M
  have hL : Measurable L := L.continuous_of_finiteDimensional.measurable
  change volume (WithLp.ofLp ⁻¹' (L ⁻¹' s)) = _
  rw [(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (hs.preimage hL).nullMeasurableSet]
  rw [← Measure.map_apply hL hs, Real.map_matrix_volume_pi_eq_smul_volume_pi hM]
  rfl

def normalMatrix (e : Fin 2 → Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if j = 0 then -(e i 1) else e i 0

lemma normalMatrix_apply (e : Fin 2 → Plane) (x : Plane) (i : Fin 2) :
    (normalMatrix e).mulVec (WithLp.ofLp x) i = e i 0 * x 1 - e i 1 * x 0 := by
  simp [normalMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

lemma det_normalMatrix (e : Fin 2 → Plane) :
    (normalMatrix e).det = (Matrix.of fun i j : Fin 2 => e i j).det := by
  simp [normalMatrix, Matrix.det_fin_two]
  ring

lemma normal_bound_of_mem_lineTube {r : ℝ} {a e x : Plane} (he : ‖e‖ = 1)
    (hx : x ∈ lineTube r a e) :
    |e 0 * x 1 - e 1 * x 0 - (e 0 * a 1 - e 1 * a 0)| ≤ 2 * r := by
  obtain ⟨y, ⟨t, rfl⟩, hxy⟩ := Metric.mem_thickening_iff.mp hx
  have hd : ‖x - (a + t • e)‖ < r := by rwa [dist_eq_norm] at hxy
  have he' (j : Fin 2) : |e j| ≤ 1 := by
    simpa only [← Real.norm_eq_abs, he] using PiLp.norm_apply_le e j
  have hd' (j : Fin 2) : |x j - (a j + t * e j)| ≤ r := by
    calc
      |x j - (a j + t * e j)| = ‖(x - (a + t • e)) j‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖x - (a + t • e)‖ := PiLp.norm_apply_le _ j
      _ ≤ r := hd.le
  calc
    |e 0 * x 1 - e 1 * x 0 - (e 0 * a 1 - e 1 * a 0)| =
        |e 0 * (x 1 - (a 1 + t * e 1)) - e 1 * (x 0 - (a 0 + t * e 0))| := by
      congr 1
      ring
    _ ≤ |e 0 * (x 1 - (a 1 + t * e 1))| + |e 1 * (x 0 - (a 0 + t * e 0))| :=
      abs_sub _ _
    _ = |e 0| * |x 1 - (a 1 + t * e 1)| + |e 1| * |x 0 - (a 0 + t * e 0)| := by
      rw [abs_mul, abs_mul]
    _ ≤ 1 * r + 1 * r := add_le_add
      (mul_le_mul (he' 0) (hd' 1) (abs_nonneg _) (by norm_num))
      (mul_le_mul (he' 1) (hd' 0) (abs_nonneg _) (by norm_num))
    _ = 2 * r := by ring

/-- The Jacobian cancels the inverse determinant in the area of two intersecting strips. -/
lemma weighted_strip_intersection {r : ℝ} (hr : 0 < r) (a e : Fin 2 → Plane)
    (he : ∀ i, ‖e i‖ = 1) :
    ENNReal.ofReal |(Matrix.of fun i j : Fin 2 => e i j).det| *
        volume (lineTube r (a 0) (e 0) ∩ lineTube r (a 1) (e 1)) ≤
      ENNReal.ofReal (16 * r ^ 2) := by
  let d := (Matrix.of fun i j : Fin 2 => e i j).det
  by_cases hd : d = 0
  · simp [d, hd]
  let b : Fin 2 → ℝ := fun i => e i 0 * a i 1 - e i 1 * a i 0
  let B : Set (Fin 2 → ℝ) := Set.univ.pi fun i => Set.Icc (b i - 2 * r) (b i + 2 * r)
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hsub : lineTube r (a 0) (e 0) ∩ lineTube r (a 1) (e 1) ⊆
      (fun x : Plane => (normalMatrix e).mulVec (WithLp.ofLp x)) ⁻¹' B := by
    intro x hx
    simp only [Set.mem_preimage, B, Set.mem_univ_pi, Set.mem_Icc]
    intro i
    have hi : x ∈ lineTube r (a i) (e i) := by
      fin_cases i
      · exact hx.1
      · exact hx.2
    have h := (abs_le.mp (normal_bound_of_mem_lineTube (he i) hi))
    rw [normalMatrix_apply]
    dsimp [b]
    constructor <;> linarith [h.1, h.2]
  have hvolB : volume B = ENNReal.ofReal (16 * r ^ 2) := by
    simp only [B, volume_pi_pi, Real.volume_Icc]
    simp_rw [show ∀ i : Fin 2, b i + 2 * r - (b i - 2 * r) = 4 * r by intro i; ring]
    rw [Fin.prod_univ_two, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc
    ENNReal.ofReal |d| * volume (lineTube r (a 0) (e 0) ∩ lineTube r (a 1) (e 1)) ≤
        ENNReal.ofReal |d| * volume
          ((fun x : Plane => (normalMatrix e).mulVec (WithLp.ofLp x)) ⁻¹' B) :=
      by gcongr
    _ = ENNReal.ofReal |d| * (ENNReal.ofReal |d⁻¹| * volume B) := by
      rw [matrix_preimage_volume _ (by simpa only [det_normalMatrix] using hd) hB,
        det_normalMatrix]
    _ = volume B := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul,
        mul_inv_cancel₀ hd, abs_one, ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (16 * r ^ 2) := hvolB

lemma planar_term_nonneg (r : ℝ) (a e : Fin 2 → Plane) (w : Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (x : Plane) :
    0 ≤ |(Matrix.of fun i j : Fin 2 => e i j).det| *
      ∏ i, (w i * (lineTube r (a i) (e i)).indicator (fun _ => (1 : ℝ)) x) := by
  exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ =>
    mul_nonneg (hw i) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))

lemma planar_term_eq_indicator (r : ℝ) (a e : Fin 2 → Plane) (w : Fin 2 → ℝ) (x : Plane) :
    (|(Matrix.of fun i j : Fin 2 => e i j).det| *
      ∏ i, (w i * (lineTube r (a i) (e i)).indicator (fun _ => (1 : ℝ)) x)) =
    (lineTube r (a 0) (e 0) ∩ lineTube r (a 1) (e 1)).indicator
      (fun _ => (∏ i, w i) * |(Matrix.of fun i j : Fin 2 => e i j).det|) x := by
  by_cases h0 : x ∈ lineTube r (a 0) (e 0)
  · by_cases h1 : x ∈ lineTube r (a 1) (e 1)
    · simp [Fin.prod_univ_two, h0, h1]
      ring
    · simp [Fin.prod_univ_two, h0, h1]
  · simp [Fin.prod_univ_two, h0]

lemma measurable_planar_term (r : ℝ) (a e : Fin 2 → Plane) (w : Fin 2 → ℝ) :
    Measurable (fun x : Plane => ENNReal.ofReal
      (|(Matrix.of fun i j : Fin 2 => e i j).det| *
        ∏ i, (w i * (lineTube r (a i) (e i)).indicator (fun _ => (1 : ℝ)) x))) := by
  simp_rw [planar_term_eq_indicator]
  exact (measurable_const.indicator ((measurableSet_lineTube _ _ _).inter
    (measurableSet_lineTube _ _ _))).ennreal_ofReal

lemma planar_term_integral {r : ℝ} (hr : 0 < r) (a e : Fin 2 → Plane)
    (w : Fin 2 → ℝ) (he : ∀ i, ‖e i‖ = 1) (hw : ∀ i, 0 ≤ w i) :
    (∫⁻ x : Plane, ENNReal.ofReal
      (|(Matrix.of fun i j : Fin 2 => e i j).det| *
        ∏ i, (w i * (lineTube r (a i) (e i)).indicator (fun _ => (1 : ℝ)) x))) ≤
      ENNReal.ofReal (16 * r ^ 2 * ∏ i, w i) := by
  let S := lineTube r (a 0) (e 0) ∩ lineTube r (a 1) (e 1)
  have hS : MeasurableSet S := (measurableSet_lineTube _ _ _).inter
    (measurableSet_lineTube _ _ _)
  have hw' : 0 ≤ ∏ i, w i := Finset.prod_nonneg fun i _ => hw i
  simp_rw [planar_term_eq_indicator]
  have hind : (fun x => ENNReal.ofReal
      (S.indicator (fun _ => (∏ i, w i) * |(Matrix.of fun i j : Fin 2 => e i j).det|) x)) =
      S.indicator (fun _ => ENNReal.ofReal ((∏ i, w i) *
        |(Matrix.of fun i j : Fin 2 => e i j).det|)) := by
    ext x
    by_cases hx : x ∈ S <;> simp [hx]
  change (∫⁻ x, ENNReal.ofReal (S.indicator _ x)) ≤ _
  rw [hind, lintegral_indicator hS, lintegral_const, Measure.restrict_apply_univ,
    ENNReal.ofReal_mul hw', mul_assoc]
  calc
    ENNReal.ofReal (∏ i, w i) *
        (ENNReal.ofReal |(Matrix.of fun i j : Fin 2 => e i j).det| * volume S) ≤
      ENNReal.ofReal (∏ i, w i) * ENNReal.ofReal (16 * r ^ 2) := by
      gcongr
      exact weighted_strip_intersection hr a e he
    _ = ENNReal.ofReal (16 * r ^ 2 * ∏ i, w i) := by
      rw [← ENNReal.ofReal_mul hw', mul_comm]

/-- Determinant-weighted multilinear Kakeya in the plane, with arbitrary real weights. -/
theorem planar_weighted_integral {r : ℝ} (hr : 0 < r) (N : Fin 2 → ℕ)
    (a e : (i : Fin 2) → Fin (N i) → Plane) (w : (i : Fin 2) → Fin (N i) → ℝ)
    (he : ∀ i k, ‖e i k‖ = 1) (hw : ∀ i k, 0 ≤ w i k) :
    (∫⁻ x : Plane, ENNReal.ofReal
      (∑ T : ((i : Fin 2) → Fin (N i)),
        |(Matrix.of fun i j : Fin 2 => e i (T i) j).det| *
          ∏ i, (w i (T i) * (lineTube r (a i (T i)) (e i (T i))).indicator
            (fun _ => (1 : ℝ)) x))) ≤
      ENNReal.ofReal (16 * r ^ 2 * ∏ i, ∑ k, w i k) := by
  classical
  let f := fun (T : (i : Fin 2) → Fin (N i)) (x : Plane) =>
    |(Matrix.of fun i j : Fin 2 => e i (T i) j).det| *
      ∏ i, (w i (T i) * (lineTube r (a i (T i)) (e i (T i))).indicator
        (fun _ => (1 : ℝ)) x)
  have hf (T : (i : Fin 2) → Fin (N i)) (x : Plane) : 0 ≤ f T x :=
    planar_term_nonneg r _ _ _ (fun i => hw i (T i)) x
  change (∫⁻ x, ENNReal.ofReal (∑ T, f T x)) ≤ _
  calc
    (∫⁻ x, ENNReal.ofReal (∑ T, f T x)) =
        ∫⁻ x, ∑ T, ENNReal.ofReal (f T x) := by
      apply lintegral_congr
      intro x
      exact ENNReal.ofReal_sum_of_nonneg fun T _ => hf T x
    _ = ∑ T, ∫⁻ x, ENNReal.ofReal (f T x) :=
      lintegral_finsetSum _ fun T _ => measurable_planar_term r _ _ _
    _ ≤ ∑ T : ((i : Fin 2) → Fin (N i)), ENNReal.ofReal (16 * r ^ 2 * ∏ i, w i (T i)) := by
      apply Finset.sum_le_sum
      intro T _
      exact planar_term_integral hr _ _ _ (fun i => he i (T i)) (fun i => hw i (T i))
    _ = ENNReal.ofReal (∑ T : ((i : Fin 2) → Fin (N i)), 16 * r ^ 2 * ∏ i, w i (T i)) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg fun T _ => by
        apply mul_nonneg (by positivity)
        exact Finset.prod_nonneg fun i _ => hw i (T i)
    _ = ENNReal.ofReal (16 * r ^ 2 * ∏ i, ∑ k, w i k) := by
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      exact (Fintype.prod_sum w).symm

theorem planar_kakeya :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ (N : Fin 2 → ℕ) (a e : (i : Fin 2) → Fin (N i) → EuclideanSpace ℝ (Fin 2))
        (w : (i : Fin 2) → Fin (N i) → ℝ),
      (∀ i k, ‖e i k‖ = 1) → (∀ i k, 0 ≤ w i k) →
      (∫⁻ x : EuclideanSpace ℝ (Fin 2), ENNReal.ofReal
        ((∑ T : ((i : Fin 2) → Fin (N i)),
          |(Matrix.of fun i j : Fin 2 => e i (T i) j).det| *
            ∏ i, (w i (T i) * (Metric.thickening r
              (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator
                (fun _ => (1 : ℝ)) x)) ^ ((1 : ℝ) / ((2 : ℝ) - 1)))) ≤
        ENNReal.ofReal (C * r ^ 2 * ∏ i : Fin 2,
          (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((2 : ℝ) - 1))) := by
  refine ⟨16, by norm_num, ?_⟩
  intro r hr N a e w he hw
  simpa only [show (1 : ℝ) / ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one,
    lineTube] using planar_weighted_integral hr N a e w he hw

end Submission.Obl.k4_multilinear_kakeya
