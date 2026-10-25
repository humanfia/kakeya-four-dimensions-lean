import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_affine_skew_row_fit

/-- Inverting two separated velocity evaluations preserves the common skew term. -/
theorem row_error_of_two_evaluations
    {K R v₁ v₂ x₀ x₁ : ℝ} (hK : 1 ≤ K)
    (hv₁ : |v₁| ≤ K) (_hv₂ : |v₂| ≤ K) (hsep : 1 / K ≤ |v₂ - v₁|)
    (h₁ : |x₀ + v₁ * x₁| ≤ R) (h₂ : |x₀ + v₂ * x₁| ≤ R) :
    |x₀| ≤ 3 * K ^ 2 * R ∧ |x₁| ≤ 2 * K * R := by
  have hKpos : 0 < K := by linarith
  have hR : 0 ≤ R := (abs_nonneg _).trans h₁
  have hd : |(v₂ - v₁) * x₁| ≤ 2 * R := by
    calc
      _ = |(x₀ + v₂ * x₁) - (x₀ + v₁ * x₁)| := by congr 1; ring
      _ ≤ |x₀ + v₂ * x₁| + |x₀ + v₁ * x₁| := abs_sub _ _
      _ ≤ 2 * R := by linarith
  rw [abs_mul] at hd
  have hsep' : 1 ≤ K * |v₂ - v₁| := by
    have := (div_le_iff₀ hKpos).mp hsep
    nlinarith
  have hx₁ : |x₁| ≤ 2 * K * R := by
    have := mul_le_mul_of_nonneg_left hd hKpos.le
    have := mul_le_mul_of_nonneg_right hsep' (abs_nonneg x₁)
    nlinarith
  refine ⟨?_, hx₁⟩
  calc
    |x₀| = |(x₀ + v₁ * x₁) - v₁ * x₁| := by ring_nf
    _ ≤ |x₀ + v₁ * x₁| + |v₁ * x₁| := abs_sub _ _
    _ = |x₀ + v₁ * x₁| + |v₁| * |x₁| := by rw [abs_mul]
    _ ≤ R + K * (2 * K * R) := add_le_add h₁ (mul_le_mul hv₁ hx₁
      (abs_nonneg _) hKpos.le)
    _ ≤ 3 * K ^ 2 * R := by nlinarith [sq_nonneg K, mul_nonneg (sq_nonneg (K - 1)) hR]

/-- The intercept row corresponding to two projection intercepts. -/
noncomputable def interceptRow (v₁ v₂ c₁ c₂ : ℝ) : Fin 2 → ℝ :=
  ![(v₂ * c₁ - v₁ * c₂) / (v₂ - v₁), (c₂ - c₁) / (v₂ - v₁)]

theorem interceptRow_evaluation {v₁ v₂ : ℝ} (hv : v₁ ≠ v₂) (c₁ c₂ : ℝ) :
    interceptRow v₁ v₂ c₁ c₂ 0 + v₁ * interceptRow v₁ v₂ c₁ c₂ 1 = c₁ ∧
    interceptRow v₁ v₂ c₁ c₂ 0 + v₂ * interceptRow v₁ v₂ c₁ c₂ 1 = c₂ := by
  have hd : v₂ - v₁ ≠ 0 := sub_ne_zero.mpr hv.symm
  simp only [interceptRow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor <;> field_simp <;> ring

/-- Parallel projection strips recover a single row on every point of the selected cells. -/
theorem row_fit_of_projection_strips
    {K R v₁ v₂ c₁ c₂ ℓ₀ : ℝ} (hK : 1 ≤ K)
    (hv₁ : |v₁| ≤ K) (hv₂ : |v₂| ≤ K) (hsep : 1 / K ≤ |v₂ - v₁|)
    (z V : Fin 2 → ℝ)
    (h₁ : |V 0 + v₁ * V 1 - ℓ₀ * (z 1 - v₁ * z 0) - c₁| ≤ R)
    (h₂ : |V 0 + v₂ * V 1 - ℓ₀ * (z 1 - v₂ * z 0) - c₂| ≤ R) :
    |V 0 - interceptRow v₁ v₂ c₁ c₂ 0 - ℓ₀ * z 1| ≤ 3 * K ^ 2 * R ∧
    |V 1 - interceptRow v₁ v₂ c₁ c₂ 1 + ℓ₀ * z 0| ≤ 2 * K * R := by
  have hv : v₁ ≠ v₂ := by
    intro h
    rw [h, sub_self, abs_zero] at hsep
    have hKpos : 0 < K := by linarith
    have := one_div_pos.mpr hKpos
    linarith
  obtain ⟨hb₁, hb₂⟩ := interceptRow_evaluation hv c₁ c₂
  apply row_error_of_two_evaluations hK hv₁ hv₂ hsep
  · convert h₁ using 1
    congr 1
    linear_combination -hb₁
  · convert h₂ using 1
    congr 1
    linear_combination -hb₂

/-- A row with a large skew coefficient can occur only during a short time interval. -/
theorem skew_coefficient_bound {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    {C L R m B ℓ : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hR : 0 ≤ R) (hm : 0 < m)
    (hdom : μ ≤ ENNReal.ofReal C • (ν.prod volume))
    (A : Set (α × ℝ)) (hmass : ENNReal.ofReal m ≤ μ A)
    (T : α × ℝ → ℝ) (hT : ∀ p ∈ A, |T p| ≤ L)
    (hfit : ∀ p ∈ A, |T p - B - ℓ * p.2| ≤ R) :
    |ℓ| ≤ 2 * C * (L + R) / m := by
  have hright : 0 ≤ 2 * C * (L + R) / m := by positivity
  by_cases hℓ : ℓ = 0
  · simpa [hℓ] using hright
  have hℓpos : 0 < |ℓ| := abs_pos.mpr hℓ
  let c : ℝ := -B / ℓ
  let r : ℝ := (L + R) / |ℓ|
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsub : A ⊆ univ ×ˢ Icc (c - r) (c + r) := by
    intro p hp
    refine ⟨mem_univ _, ?_⟩
    have heval : |B + ℓ * p.2| ≤ L + R := by
      calc
        _ = |T p - (T p - B - ℓ * p.2)| := by congr 1; ring
        _ ≤ |T p| + |T p - B - ℓ * p.2| := abs_sub _ _
        _ ≤ L + R := add_le_add (hT p hp) (hfit p hp)
    have hid : ℓ * (p.2 - c) = B + ℓ * p.2 := by
      dsimp [c]
      field_simp
      ring
    have ht : |p.2 - c| ≤ r := by
      apply (le_div_iff₀ hℓpos).mpr
      simpa only [← hid, abs_mul, mul_comm] using heval
    exact ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩
  have hmass' : ENNReal.ofReal m ≤ ENNReal.ofReal (2 * C * r) := by
    calc
      _ ≤ μ A := hmass
      _ ≤ (ENNReal.ofReal C • (ν.prod volume)) (univ ×ˢ Icc (c - r) (c + r)) :=
        (hdom A).trans (measure_mono hsub)
      _ = ENNReal.ofReal (2 * C * r) := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, measure_univ, one_mul,
          Real.volume_Icc, show c + r - (c - r) = 2 * r by ring,
          ← ENNReal.ofReal_mul hC]
        congr 1
        ring
  have hreal : m ≤ 2 * C * r := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmass'
  apply (le_div_iff₀ hm).mpr
  have hreal' : m * |ℓ| ≤ 2 * C * (L + R) := by
    have := mul_le_mul_of_nonneg_right hreal hℓpos.le
    dsimp [r] at this
    simpa only [mul_assoc, div_mul_cancel₀ _ hℓpos.ne'] using this
  nlinarith

/-- One occupied incidence bounds both intercepts after the skew coefficient is bounded. -/
theorem intercept_bound {L R K D ℓ : ℝ}
    (z T B : Fin 2 → ℝ)
    (hz₀ : |z 0| ≤ 1) (hz₁ : |z 1| ≤ K)
    (hT₀ : |T 0| ≤ L) (hT₁ : |T 1| ≤ L) (hℓ : |ℓ| ≤ D)
    (hfit₀ : |T 0 - B 0 + ℓ * z 1| ≤ R)
    (hfit₁ : |T 1 - B 1 - ℓ * z 0| ≤ R) :
    |B 0| + |B 1| + |ℓ| ≤ 2 * (L + R) + (K + 2) * D := by
  have hD : 0 ≤ D := (abs_nonneg _).trans hℓ
  have hK : 0 ≤ K := (abs_nonneg _).trans hz₁
  have hB₀ : |B 0| ≤ L + R + D * K := by
    calc
      _ = |T 0 + ℓ * z 1 - (T 0 - B 0 + ℓ * z 1)| := by congr 1; ring
      _ ≤ |T 0 + ℓ * z 1| + |T 0 - B 0 + ℓ * z 1| := abs_sub _ _
      _ ≤ (|T 0| + |ℓ * z 1|) + R := add_le_add (abs_add_le _ _) hfit₀
      _ ≤ L + R + D * K := by
        rw [abs_mul]
        have := mul_le_mul hℓ hz₁ (abs_nonneg _) hD
        linarith
  have hB₁ : |B 1| ≤ L + R + D := by
    calc
      _ = |T 1 - ℓ * z 0 - (T 1 - B 1 - ℓ * z 0)| := by congr 1; ring
      _ ≤ |T 1 - ℓ * z 0| + |T 1 - B 1 - ℓ * z 0| := abs_sub _ _
      _ ≤ (|T 1| + |ℓ * z 0|) + R := add_le_add (abs_sub _ _) hfit₁
      _ ≤ L + R + D := by
        rw [abs_mul]
        have := mul_le_mul hℓ hz₀ (abs_nonneg _) hD
        linarith
  nlinarith

/-- Undoing the row scale loses the error scale, but no power of the fine mesh. -/
theorem unscale_row_fit {h E D₀ D₁ ℓ₀ : ℝ} (hh : 0 < h) (hE : 0 < E)
    (z T B₀ : Fin 2 → ℝ)
    (hfit₀ : |(h / E) * T 0 - B₀ 0 - ℓ₀ * z 1| ≤ D₀ * h)
    (hfit₁ : |(h / E) * T 1 - B₀ 1 + ℓ₀ * z 0| ≤ D₁ * h) :
    |T 0 - (E / h) * B₀ 0 + (-(E / h) * ℓ₀) * z 1| ≤ D₀ * E ∧
    |T 1 - (E / h) * B₀ 1 - (-(E / h) * ℓ₀) * z 0| ≤ D₁ * E := by
  have heh : 0 ≤ E / h := by positivity
  constructor
  · calc
      _ = |(E / h) * ((h / E) * T 0 - B₀ 0 - ℓ₀ * z 1)| := by
        congr 1
        field_simp
        ring
      _ = (E / h) * |(h / E) * T 0 - B₀ 0 - ℓ₀ * z 1| := by
        rw [abs_mul, abs_of_nonneg heh]
      _ ≤ (E / h) * (D₀ * h) := mul_le_mul_of_nonneg_left hfit₀ heh
      _ = D₀ * E := by field_simp
  · calc
      _ = |(E / h) * ((h / E) * T 1 - B₀ 1 + ℓ₀ * z 0)| := by
        congr 1
        field_simp
        ring
      _ = (E / h) * |(h / E) * T 1 - B₀ 1 + ℓ₀ * z 0| := by
        rw [abs_mul, abs_of_nonneg heh]
      _ ≤ (E / h) * (D₁ * h) := mul_le_mul_of_nonneg_left hfit₁ heh
      _ = D₁ * E := by field_simp

/-- Dense original incidence mass in two parallel projection strips gives the row conclusion. -/
theorem recover_dense_row {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    {K h E v₁ v₂ c₁ c₂ ℓ₀ : ℝ} (hK : 1 ≤ K) (hh : 0 < h)
    (hE : 0 < E) (hEone : E ≤ 1)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume))
    (z T : α × ℝ → Fin 2 → ℝ) (hztime : ∀ p, z p 0 = p.2)
    (A : Set (α × ℝ)) (hmass : ENNReal.ofReal (1 / K) ≤ μ A)
    (hz₀ : ∀ p ∈ A, |z p 0| ≤ 1) (hz₁ : ∀ p ∈ A, |z p 1| ≤ K)
    (hT : ∀ p ∈ A, ∀ j, |T p j| ≤ K)
    (hv₁ : |v₁| ≤ K) (hv₂ : |v₂| ≤ K) (hsep : 1 / K ≤ |v₂ - v₁|)
    (hstrip₁ : ∀ p ∈ A,
      |(h / E) * T p 0 + v₁ * ((h / E) * T p 1) -
        ℓ₀ * (z p 1 - v₁ * z p 0) - c₁| ≤ K * h)
    (hstrip₂ : ∀ p ∈ A,
      |(h / E) * T p 0 + v₂ * ((h / E) * T p 1) -
        ℓ₀ * (z p 1 - v₂ * z p 0) - c₂| ≤ K * h) :
    ∃ B : Fin 2 → ℝ, ∃ ℓ : ℝ,
      |B 0| + |B 1| + |ℓ| ≤ 32 * K ^ 6 ∧
      ENNReal.ofReal (1 / K) ≤ μ {p |
        |T p 0 - B 0 + ℓ * z p 1| ≤ 3 * K ^ 3 * E ∧
        |T p 1 - B 1 - ℓ * z p 0| ≤ 3 * K ^ 3 * E} := by
  have hKpos : 0 < K := by linarith
  let B₀ := interceptRow v₁ v₂ c₁ c₂
  let B : Fin 2 → ℝ := fun j => (E / h) * B₀ j
  let ℓ : ℝ := -(E / h) * ℓ₀
  let R : ℝ := 3 * K ^ 3 * E
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hKK : 2 * K ^ 2 ≤ 3 * K ^ 3 := by
    nlinarith [sq_nonneg K, mul_nonneg (sq_nonneg K) (show 0 ≤ K - 1 by linarith)]
  have hfit : ∀ p ∈ A,
      |T p 0 - B 0 + ℓ * z p 1| ≤ R ∧
      |T p 1 - B 1 - ℓ * z p 0| ≤ R := by
    intro p hp
    obtain ⟨h₀, h₁⟩ := row_fit_of_projection_strips hK hv₁ hv₂ hsep (z p)
      (fun j => (h / E) * T p j) (hstrip₁ p hp) (hstrip₂ p hp)
    have h₀' : |(h / E) * T p 0 - B₀ 0 - ℓ₀ * z p 1| ≤
        (3 * K ^ 3) * h := by
      convert h₀ using 1
      ring
    have h₁' : |(h / E) * T p 1 - B₀ 1 + ℓ₀ * z p 0| ≤
        (2 * K ^ 2) * h := by
      convert h₁ using 1
      ring
    obtain ⟨g₀, g₁⟩ := unscale_row_fit hh hE (z p) (T p) B₀ h₀' h₁'
    exact ⟨g₀, g₁.trans (mul_le_mul_of_nonneg_right hKK hE.le)⟩
  have hℓ : |ℓ| ≤ 2 * K * (K + R) / (1 / K) :=
    skew_coefficient_bound ν μ hKpos.le hKpos.le hR (one_div_pos.mpr hKpos)
      hdom A hmass (fun p => T p 1) (fun p hp => hT p hp 1)
      (fun p hp => by simpa only [← hztime p] using (hfit p hp).2)
  have hKcube : K ≤ K ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg K) (show 0 ≤ K - 1 by linarith),
      sq_nonneg (K - 1)]
  have hRle : R ≤ 3 * K ^ 3 := by
    dsimp [R]
    exact (mul_le_mul_of_nonneg_left hEone (by positivity)).trans_eq (mul_one _)
  have hℓ' : |ℓ| ≤ 8 * K ^ 5 := by
    have hiden : 2 * K * (K + R) / (1 / K) = 2 * K ^ 2 * (K + R) := by
      field_simp
    rw [hiden] at hℓ
    have := mul_le_mul_of_nonneg_left (show K + R ≤ 4 * K ^ 3 by linarith)
      (show 0 ≤ 2 * K ^ 2 by positivity)
    calc
      |ℓ| ≤ 2 * K ^ 2 * (K + R) := hℓ
      _ ≤ 2 * K ^ 2 * (4 * K ^ 3) := this
      _ = 8 * K ^ 5 := by ring
  have hA : A.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, measure_empty] at hmass
    have := ENNReal.ofReal_pos.mpr (one_div_pos.mpr hKpos)
    exact (not_le_of_gt this) hmass
  obtain ⟨p, hp⟩ := hA
  have hinter := intercept_bound (z p) (T p) B (hz₀ p hp) (hz₁ p hp)
    (hT p hp 0) (hT p hp 1) hℓ' (hfit p hp).1 (hfit p hp).2
  refine ⟨B, ℓ, hinter.trans ?_, hmass.trans (measure_mono fun p hp => hfit p hp)⟩
  have hc : 2 * (K + R) ≤ 8 * K ^ 3 := by linarith
  have hp₃₆ : K ^ 3 ≤ K ^ 6 := by
    exact_mod_cast pow_le_pow_right₀ hK  (show 3 ≤ 6 by omega)
  calc
    2 * (K + R) + (K + 2) * (8 * K ^ 5) ≤
        8 * K ^ 3 + (3 * K) * (8 * K ^ 5) := by
      exact add_le_add hc (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _ ≤ 8 * K ^ 6 + (3 * K) * (8 * K ^ 5) := by gcongr
    _ = 32 * K ^ 6 := by ring

end Submission.Obl.k4_affine_skew_row_fit
