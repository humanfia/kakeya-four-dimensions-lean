import Mathlib

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/AffineUpgrade.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set

noncomputable section

/-- A full-time predictor, affine in the static parameters and in time. -/
def predictor (h : Fin 6 → ℝ) (t p q : ℝ) : ℝ :=
  h 0 + h 1 * t + (h 2 + h 3 * t) * p + (h 4 + h 5 * t) * q

/-- The normalized prediction obtained from one value bin and one slope bin. -/
def jetPredictor (F A : Fin 2 → ℝ) (t₀ z z' t y₁ y₂ : ℝ) : ℝ :=
  z + F 0 * y₁ + F 1 * y₂ + (t - t₀) * (z' + A 0 * y₁ + A 1 * y₂)

/-- Restoring a normalized first-jet fit preserves the six-coefficient predictor class. -/
def upgrade (h : Fin 6 → ℝ) (a D p₀ q₀ t₀ z z' : ℝ)
    (F A : Fin 2 → ℝ) : Fin 6 → ℝ :=
  ![h 0 + a * (z - t₀ * z' - (F 0 - t₀ * A 0) * p₀ / D -
        (F 1 - t₀ * A 1) * q₀ / D),
    h 1 + a * (z' - A 0 * p₀ / D - A 1 * q₀ / D),
    h 2 + a * (F 0 - t₀ * A 0) / D,
    h 3 + a * A 0 / D,
    h 4 + a * (F 1 - t₀ * A 1) / D,
    h 5 + a * A 1 / D]

theorem predictor_upgrade (h : Fin 6 → ℝ) (a D p₀ q₀ t₀ z z' : ℝ)
    (F A : Fin 2 → ℝ) (t p q : ℝ) :
    predictor (upgrade h a D p₀ q₀ t₀ z z' F A) t p q =
      predictor h t p q + a * jetPredictor F A t₀ z z' t ((p - p₀) / D) ((q - q₀) / D) := by
  simp only [predictor, upgrade, jetPredictor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, div_eq_mul_inv]
  ring

/-- Exact affine evolution promotes a fitted value and slope at one time to a full-time fit. -/
theorem affine_jet_error {r₀ r₁ z z' w t t₀ y₁ y₂ : ℝ} {F A : Fin 2 → ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hvalue : |r₀ + t₀ * r₁ - z - F 0 * y₁ - F 1 * y₂| ≤ w)
    (hslope : |r₁ - z' - A 0 * y₁ - A 1 * y₂| ≤ w) :
    |r₀ + t * r₁ - jetPredictor F A t₀ z z' t y₁ y₂| ≤ 2 * w := by
  have hw : 0 ≤ w := (abs_nonneg _).trans hvalue
  have htime : |t - t₀| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1, ht₀.2], by linarith [ht.2, ht₀.1]⟩
  have hid : r₀ + t * r₁ - jetPredictor F A t₀ z z' t y₁ y₂ =
      (r₀ + t₀ * r₁ - z - F 0 * y₁ - F 1 * y₂) +
      (t - t₀) * (r₁ - z' - A 0 * y₁ - A 1 * y₂) := by dsimp [jetPredictor]; ring
  rw [hid]
  calc
    |(r₀ + t₀ * r₁ - z - F 0 * y₁ - F 1 * y₂) +
        (t - t₀) * (r₁ - z' - A 0 * y₁ - A 1 * y₂)| ≤
      |r₀ + t₀ * r₁ - z - F 0 * y₁ - F 1 * y₂| +
        |(t - t₀) * (r₁ - z' - A 0 * y₁ - A 1 * y₂)| := abs_add_le _ _
    _ ≤ w + 1 * w := add_le_add hvalue (by rw [abs_mul]; exact mul_le_mul htime hslope (abs_nonneg _) (by norm_num))
    _ = 2 * w := by ring

/-- Physical restoration of the full-time error, on the unchanged parameter square. -/
theorem upgrade_fit {h : Fin 6 → ℝ} {a D p₀ q₀ t₀ z z' r₀ r₁ w t p q : ℝ}
    {F A : Fin 2 → ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Icc (0 : ℝ) 1) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hvalue : |r₀ + t₀ * r₁ - z - F 0 * ((p - p₀) / D) - F 1 * ((q - q₀) / D)| ≤ w)
    (hslope : |r₁ - z' - A 0 * ((p - p₀) / D) - A 1 * ((q - q₀) / D)| ≤ w) :
    |predictor h t p q + a * (r₀ + t * r₁) -
      predictor (upgrade h a D p₀ q₀ t₀ z z' F A) t p q| ≤ 2 * a * w := by
  rw [predictor_upgrade]
  have hid : predictor h t p q + a * (r₀ + t * r₁) -
      (predictor h t p q + a * jetPredictor F A t₀ z z' t ((p - p₀) / D) ((q - q₀) / D)) =
      a * (r₀ + t * r₁ - jetPredictor F A t₀ z z' t ((p - p₀) / D) ((q - q₀) / D)) := by ring
  rw [hid, abs_mul, abs_of_nonneg ha]
  calc
    a * |r₀ + t * r₁ - jetPredictor F A t₀ z z' t ((p - p₀) / D) ((q - q₀) / D)| ≤
      a * (2 * w) := mul_le_mul_of_nonneg_left (affine_jet_error ht ht₀ hvalue hslope) ha
    _ = 2 * a * w := by ring

/-- The normalized first-jet predictor is bounded on the whole unit parameter square. -/
theorem jetPredictor_bound {F A : Fin 2 → ℝ} {t₀ z z' t y₁ y₂ M : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hy₁ : |y₁| ≤ 1) (hy₂ : |y₂| ≤ 1)
    (hz : |z| ≤ M) (hz' : |z'| ≤ M)
    (hF : ∀ i, |F i| ≤ M) (hA : ∀ i, |A i| ≤ M) :
    |jetPredictor F A t₀ z z' t y₁ y₂| ≤ 6 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hz
  have htime : |t - t₀| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1, ht₀.2], by linarith [ht.2, ht₀.1]⟩
  have hmul (B : Fin 2 → ℝ) (hB : ∀ i, |B i| ≤ M) :
      |B 0 * y₁| ≤ M ∧ |B 1 * y₂| ≤ M := by
    constructor
    · rw [abs_mul]; exact (mul_le_mul (hB 0) hy₁ (abs_nonneg _) hM).trans_eq (mul_one M)
    · rw [abs_mul]; exact (mul_le_mul (hB 1) hy₂ (abs_nonneg _) hM).trans_eq (mul_one M)
  have hv : |z + F 0 * y₁ + F 1 * y₂| ≤ 3 * M := by
    calc _ ≤ |z| + |F 0 * y₁| + |F 1 * y₂| := abs_add_three _ _ _
         _ ≤ 3 * M := by linarith [(hmul F hF).1, (hmul F hF).2]
  have hs : |z' + A 0 * y₁ + A 1 * y₂| ≤ 3 * M := by
    calc _ ≤ |z'| + |A 0 * y₁| + |A 1 * y₂| := abs_add_three _ _ _
         _ ≤ 3 * M := by linarith [(hmul A hA).1, (hmul A hA).2]
  calc
    |jetPredictor F A t₀ z z' t y₁ y₂| ≤
      |z + F 0 * y₁ + F 1 * y₂| + |(t - t₀) * (z' + A 0 * y₁ + A 1 * y₂)| := abs_add_le _ _
    _ ≤ 3 * M + 1 * (3 * M) := add_le_add hv (by rw [abs_mul]; exact mul_le_mul htime hs (abs_nonneg _) (by norm_num))
    _ = 6 * M := by ring

/-- Whole-square norm control survives restoring the first-jet correction. -/
theorem upgrade_bound {h : Fin 6 → ℝ} {a D p₀ q₀ t₀ z z' t p q K M : ℝ}
    {F A : Fin 2 → ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (ht : t ∈ Icc (0 : ℝ) 1) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hp : p ∈ Icc p₀ (p₀ + D)) (hq : q ∈ Icc q₀ (q₀ + D))
    (hbase : |predictor h t p q| ≤ K)
    (hz : |z| ≤ M) (hz' : |z'| ≤ M)
    (hF : ∀ i, |F i| ≤ M) (hA : ∀ i, |A i| ≤ M) :
    |predictor (upgrade h a D p₀ q₀ t₀ z z' F A) t p q| ≤ K + 6 * a * M := by
  have hy₁ : |(p - p₀) / D| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (by linarith [hp.1]) hD.le), div_le_one hD]
    linarith [hp.2]
  have hy₂ : |(q - q₀) / D| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (by linarith [hq.1]) hD.le), div_le_one hD]
    linarith [hq.2]
  rw [predictor_upgrade]
  calc
    |predictor h t p q + a * jetPredictor F A t₀ z z' t ((p - p₀) / D) ((q - q₀) / D)| ≤
      |predictor h t p q| + |a * jetPredictor F A t₀ z z' t ((p - p₀) / D) ((q - q₀) / D)| := abs_add_le _ _
    _ ≤ K + a * (6 * M) := by
      rw [abs_mul, abs_of_nonneg ha]
      exact add_le_add hbase (mul_le_mul_of_nonneg_left
        (jetPredictor_bound ht ht₀ hy₁ hy₂ hz hz' hF hA) ha)
    _ = K + 6 * a * M := by ring

/-- The affine coefficients of a trajectory after subtracting its old predictor. -/
def normalizedAffine (h : Fin 6 → ℝ) (a x₀ x₁ p q : ℝ) : Fin 2 → ℝ :=
  ![(x₀ - h 0 - h 2 * p - h 4 * q) / a,
    (x₁ - h 1 - h 3 * p - h 5 * q) / a]

theorem normalizedAffine_evolution (h : Fin 6 → ℝ) {a : ℝ} (ha : a ≠ 0)
    (x₀ x₁ p q t : ℝ) :
    x₀ + t * x₁ = predictor h t p q +
      a * (normalizedAffine h a x₀ x₁ p q 0 + t * normalizedAffine h a x₀ x₁ p q 1) := by
  simp only [normalizedAffine, predictor, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- A whole-time fit bounds both coefficients of the normalized affine signal. -/
theorem normalizedAffine_bounds {h : Fin 6 → ℝ} {a x₀ x₁ p q K : ℝ} (ha : 0 < a)
    (hfit : ∀ t ∈ Icc (0 : ℝ) 1, |x₀ + t * x₁ - predictor h t p q| ≤ K * a) :
    (∀ t ∈ Icc (0 : ℝ) 1,
      |normalizedAffine h a x₀ x₁ p q 0 + t * normalizedAffine h a x₀ x₁ p q 1| ≤ K) ∧
    |normalizedAffine h a x₀ x₁ p q 0| ≤ K ∧
    |normalizedAffine h a x₀ x₁ p q 1| ≤ 2 * K := by
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |normalizedAffine h a x₀ x₁ p q 0 + t * normalizedAffine h a x₀ x₁ p q 1| ≤ K := by
    have he := hfit t ht
    rw [normalizedAffine_evolution h ha.ne' x₀ x₁ p q t, add_sub_cancel_left,
      abs_mul, abs_of_pos ha] at he
    nlinarith [he]
  have hzero : |normalizedAffine h a x₀ x₁ p q 0| ≤ K := by
    simpa only [zero_mul, add_zero] using hnorm 0 (by norm_num)
  have hone := hnorm 1 (by norm_num)
  simp only [one_mul] at hone
  refine ⟨hnorm, hzero, ?_⟩
  calc
    |normalizedAffine h a x₀ x₁ p q 1| =
      |(normalizedAffine h a x₀ x₁ p q 0 + normalizedAffine h a x₀ x₁ p q 1) -
        normalizedAffine h a x₀ x₁ p q 0| := by congr 1; ring
    _ ≤ |normalizedAffine h a x₀ x₁ p q 0 + normalizedAffine h a x₀ x₁ p q 1| +
      |normalizedAffine h a x₀ x₁ p q 0| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (normalizedAffine h a x₀ x₁ p q 0 + normalizedAffine h a x₀ x₁ p q 1)
            (-normalizedAffine h a x₀ x₁ p q 0))
    _ ≤ 2 * K := by linarith

end

end Submission.Obl.k4_horizontal_strict_parameter_step
