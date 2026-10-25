import Mathlib

/-!
# Full-time affine parameter predictors

Adapted from: here:o217
Original proofs by session x0759, ParameterGeometry.lean, parent branch x0759
(commit a9dd1541; also present at 1ccf7833). The o217 posts of 2026-10-21T10:17Z
and o218's request at 10:22Z identify these kernels for shared use in o245 and o218.
-/

namespace Submission.Lib.K4FullTimeLayers

open Set

/-- The six-coefficient full-time predictor used by the endpoint engine. -/
def parameterPredictor (h : Fin 6 → ℝ) (t p q : ℝ) : ℝ :=
  h 0 + h 1 * t + (h 2 + h 3 * t) * p + (h 4 + h 5 * t) * q

/-- Reconstruct spatial positions using a representative of the velocity bin. -/
def liftAffine (L : Fin 4 → ℝ) (v : ℝ) : Fin 6 → ℝ :=
  ![L 0, L 1 + v * L 2, L 2, -L 3, L 3, 0]

theorem liftAffine_eval (L : Fin 4 → ℝ) (v t p q : ℝ) :
    parameterPredictor (liftAffine L v) t p q =
      L 0 + L 1 * t + L 2 * (p + t * v) + L 3 * (q - t * p) := by
  simp only [parameterPredictor, liftAffine, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- The horizontal defect is also the error of the static-parameter reconstruction. -/
theorem horizontal_reconstruction {b : Fin 6 → ℝ} {t δ : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hb : |b 4 + b 0| ≤ δ) :
    |b 1 + t * b 4 - (b 1 - t * b 0)| ≤ δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hb
  calc
    |b 1 + t * b 4 - (b 1 - t * b 0)| = |t| * |b 4 + b 0| := by
      rw [← abs_mul]
      congr 1
      ring
    _ = t * |b 4 + b 0| := by rw [abs_of_nonneg ht.1]
    _ ≤ 1 * δ := mul_le_mul ht.2 hb (abs_nonneg _) (by norm_num)
    _ = δ := one_mul _

theorem velocity_reconstruction {b : Fin 6 → ℝ} {v t χ : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hb : |b 3 - v| ≤ χ) :
    |b 0 + t * b 3 - (b 0 + t * v)| ≤ χ := by
  calc
    |b 0 + t * b 3 - (b 0 + t * v)| = |t * (b 3 - v)| := by
      congr 1
      ring
    _ = t * |b 3 - v| := by rw [abs_mul, abs_of_nonneg ht.1]
    _ ≤ 1 * χ := mul_le_mul ht.2 hb (abs_nonneg _) (by norm_num)
    _ = χ := one_mul _

/-- A true affine fit becomes a parameter predictor with only the reconstruction error. -/
theorem affine_fit_to_parameter {b : Fin 6 → ℝ} {L : Fin 4 → ℝ}
    {v t E δ χ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hhor : |b 4 + b 0| ≤ δ) (hvel : |b 3 - v| ≤ χ)
    (hfit : |b 2 + t * b 5 -
      (L 0 + L 1 * t + L 2 * (b 0 + t * b 3) + L 3 * (b 1 + t * b 4))| ≤ E) :
    |b 2 + t * b 5 - parameterPredictor (liftAffine L v) t (b 0) (b 1)| ≤
      E + |L 2| * χ + |L 3| * δ := by
  rw [liftAffine_eval]
  have h1 := velocity_reconstruction ht hvel
  have h2 := horizontal_reconstruction ht hhor
  calc
    |b 2 + t * b 5 -
        (L 0 + L 1 * t + L 2 * (b 0 + t * v) + L 3 * (b 1 - t * b 0))| =
      |(b 2 + t * b 5 -
        (L 0 + L 1 * t + L 2 * (b 0 + t * b 3) + L 3 * (b 1 + t * b 4))) +
        L 2 * (b 0 + t * b 3 - (b 0 + t * v)) +
        L 3 * (b 1 + t * b 4 - (b 1 - t * b 0))| := by
          congr 1
          ring
    _ ≤ |b 2 + t * b 5 -
        (L 0 + L 1 * t + L 2 * (b 0 + t * b 3) + L 3 * (b 1 + t * b 4))| +
        |L 2 * (b 0 + t * b 3 - (b 0 + t * v))| +
        |L 3 * (b 1 + t * b 4 - (b 1 - t * b 0))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ E + |L 2| * χ + |L 3| * δ := by
      rw [abs_mul, abs_mul]
      exact add_le_add (add_le_add hfit (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))

/-- Two corners control a coordinate slope of an affine function. -/
theorem affine_square_slopes {a b c p q D M : ℝ} (hD : 0 < D)
    (h00 : |a + b * p + c * q| ≤ M)
    (h10 : |a + b * (p + D) + c * q| ≤ M)
    (h01 : |a + b * p + c * (q + D)| ≤ M) :
    |b| ≤ 2 * M / D ∧ |c| ≤ 2 * M / D := by
  constructor
  · apply (le_div_iff₀ hD).2
    calc
      |b| * D = |b * D| := by rw [abs_mul, abs_of_pos hD]
      _ = |(a + b * (p + D) + c * q) - (a + b * p + c * q)| := by
        congr 1
        ring
      _ ≤ |a + b * (p + D) + c * q| + |a + b * p + c * q| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  · apply (le_div_iff₀ hD).2
    calc
      |c| * D = |c * D| := by rw [abs_mul, abs_of_pos hD]
      _ = |(a + b * p + c * (q + D)) - (a + b * p + c * q)| := by
        congr 1
        ring
      _ ≤ |a + b * p + c * (q + D)| + |a + b * p + c * q| := abs_sub _ _
      _ ≤ 2 * M := by linarith

/-- The full-domain bound controls all six unscaled coefficients. -/
theorem parameterPredictor_coefficients {h : Fin 6 → ℝ} {p q D M : ℝ}
    (hD : 0 < D)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p' ∈ Icc p (p + D),
      ∀ q' ∈ Icc q (q + D), |parameterPredictor h t p' q'| ≤ M) :
    ∀ e, |h e| ≤ 2 * (M + (2 * M / D) * (|p| + |q| + 1)) := by
  have hp : p ∈ Icc p (p + D) := ⟨le_rfl, le_add_of_nonneg_right hD.le⟩
  have hq : q ∈ Icc q (q + D) := ⟨le_rfl, le_add_of_nonneg_right hD.le⟩
  have hpD : p + D ∈ Icc p (p + D) := ⟨hp.2, le_rfl⟩
  have hqD : q + D ∈ Icc q (q + D) := ⟨hq.2, le_rfl⟩
  have at0 := fun p' hp' q' hq' => hbound 0 (by norm_num) p' hp' q' hq'
  have at1 := fun p' hp' q' hq' => hbound 1 (by norm_num) p' hp' q' hq'
  simp only [parameterPredictor, mul_zero, add_zero, mul_one] at at0 at1
  obtain ⟨h2, h4⟩ := affine_square_slopes hD
    (at0 p hp q hq) (at0 (p + D) hpD q hq) (at0 p hp (q + D) hqD)
  obtain ⟨h23, h45⟩ := affine_square_slopes hD
    (at1 p hp q hq) (at1 (p + D) hpD q hq) (at1 p hp (q + D) hqD)
  have hM : 0 ≤ M := (abs_nonneg _).trans (at0 p hp q hq)
  have hA : 0 ≤ 2 * M / D := div_nonneg (by positivity) hD.le
  have base_bound : ∀ a b c : ℝ, |a + b * p + c * q| ≤ M →
      |b| ≤ 2 * M / D → |c| ≤ 2 * M / D →
      |a| ≤ M + (2 * M / D) * (|p| + |q|) := by
    intro a b c ha hb hc
    calc
      |a| = |(a + b * p + c * q) - b * p - c * q| := by congr 1; ring
      _ ≤ |a + b * p + c * q| + |b * p| + |c * q| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ M + (2 * M / D) * |p| + (2 * M / D) * |q| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (add_le_add ha (mul_le_mul_of_nonneg_right hb (abs_nonneg _)))
          (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
      _ = M + (2 * M / D) * (|p| + |q|) := by ring
  have h0 := base_bound _ _ _ (at0 p hp q hq) h2 h4
  have h01 := base_bound _ _ _ (at1 p hp q hq) h23 h45
  have h1 : |h 1| ≤ 2 * (M + (2 * M / D) * (|p| + |q|)) := by
    calc
      |h 1| = |(h 0 + h 1) - h 0| := by congr 1; ring
      _ ≤ |h 0 + h 1| + |h 0| := abs_sub _ _
      _ ≤ 2 * (M + (2 * M / D) * (|p| + |q|)) := by linarith
  have h3 : |h 3| ≤ 2 * (2 * M / D) := by
    calc
      |h 3| = |(h 2 + h 3) - h 2| := by congr 1; ring
      _ ≤ |h 2 + h 3| + |h 2| := abs_sub _ _
      _ ≤ 2 * (2 * M / D) := by linarith
  have h5 : |h 5| ≤ 2 * (2 * M / D) := by
    calc
      |h 5| = |(h 4 + h 5) - h 4| := by congr 1; ring
      _ ≤ |h 4 + h 5| + |h 4| := abs_sub _ _
      _ ≤ 2 * (2 * M / D) := by linarith
  have hAp : 0 ≤ (2 * M / D) * |p| := mul_nonneg hA (abs_nonneg _)
  have hAq : 0 ≤ (2 * M / D) * |q| := mul_nonneg hA (abs_nonneg _)
  let A := 2 * M / D
  let B := M + A * (|p| + |q|)
  have hB : 0 ≤ B := by dsimp [B, A]; nlinarith only [hM, hAp, hAq]
  change 0 ≤ A at hA
  change |h 0| ≤ B at h0
  change |h 1| ≤ 2 * B at h1
  change |h 2| ≤ A at h2
  change |h 4| ≤ A at h4
  change |h 3| ≤ 2 * A at h3
  change |h 5| ≤ 2 * A at h5
  have htarget : 2 * (M + (2 * M / D) * (|p| + |q| + 1)) = 2 * (B + A) := by
    dsimp [A, B]
    ring
  intro e
  rw [htarget]
  fin_cases e
  · exact h0.trans (by linarith only [hA, hB])
  · exact h1.trans (by linarith only [hA])
  · exact h2.trans (by linarith only [hA, hB])
  · exact h3.trans (by linarith only [hB])
  · exact h4.trans (by linarith only [hA, hB])
  · exact h5.trans (by linarith only [hB])

/-- Extending the parameter square costs only its ratio to the old square. -/
theorem parameterPredictor_extension {h : Fin 6 → ℝ} {p q D M E t p₀ q₀ p' q' : ℝ}
    (hD : 0 < D) (ht : t ∈ Icc (0 : ℝ) 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p' ∈ Icc p (p + D),
      ∀ q' ∈ Icc q (q + D), |parameterPredictor h t p' q'| ≤ M)
    (hp₀ : p₀ ∈ Icc p (p + D)) (hq₀ : q₀ ∈ Icc q (q + D))
    (hp' : |p' - p₀| ≤ E) (hq' : |q' - q₀| ≤ E) :
    |parameterPredictor h t p' q'| ≤ M + 4 * M * E / D := by
  have hp : p ∈ Icc p (p + D) := ⟨le_rfl, le_add_of_nonneg_right hD.le⟩
  have hq : q ∈ Icc q (q + D) := ⟨le_rfl, le_add_of_nonneg_right hD.le⟩
  have hpD : p + D ∈ Icc p (p + D) := ⟨hp.2, le_rfl⟩
  have hqD : q + D ∈ Icc q (q + D) := ⟨hq.2, le_rfl⟩
  obtain ⟨hb, hc⟩ := affine_square_slopes hD
    (hbound t ht p hp q hq) (hbound t ht (p + D) hpD q hq)
    (hbound t ht p hp (q + D) hqD)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound t ht p hp q hq)
  have hA : 0 ≤ 2 * M / D := div_nonneg (by positivity) hD.le
  calc
    |parameterPredictor h t p' q'| = |parameterPredictor h t p₀ q₀ +
        (h 2 + h 3 * t) * (p' - p₀) + (h 4 + h 5 * t) * (q' - q₀)| := by
      unfold parameterPredictor
      congr 1
      ring
    _ ≤ |parameterPredictor h t p₀ q₀| +
        |(h 2 + h 3 * t) * (p' - p₀)| + |(h 4 + h 5 * t) * (q' - q₀)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M + (2 * M / D) * E + (2 * M / D) * E := by
      rw [abs_mul, abs_mul]
      exact add_le_add (add_le_add (hbound t ht p₀ hp₀ q₀ hq₀)
        (mul_le_mul hb hp' (abs_nonneg _) hA))
        (mul_le_mul hc hq' (abs_nonneg _) hA)
    _ = M + 4 * M * E / D := by ring

end Submission.Lib.K4FullTimeLayers
