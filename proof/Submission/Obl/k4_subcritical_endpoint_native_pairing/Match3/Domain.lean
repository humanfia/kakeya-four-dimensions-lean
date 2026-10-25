/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/Domain.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation, session x0764, Match3/Domain.lean, commit2b232aca. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.Quad3
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Coordinates

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Normalizing a full-time comparison domain

A comparison domain is a time block times a parameter square,
`[t₀, t₀ + τ] × [p₀, p₀ + D] × [q₀, q₀ + D]`.  `normVec` centers it and shrinks it by `4τ`
(time) and `4D` (parameters), so that the domain goes into `[-1/8, 1/8]³` (inside the `1/4`-ball
of the three-dimensional matching lemma) and the box `|t - t_c| ≤ 4τ`, `|p - p_c| ≤ 4D`,
`|q - q_c| ≤ 4D` goes onto the unit cube.  A full-time predictor
`parameterPredictor h t p q = h₀ + h₁ t + (h₂ + h₃ t) p + (h₄ + h₅ t) q` becomes the quadratic
`q3 (normCoeffs h)` in normalized coordinates.  The native affine predictor
`L₀ + L₁ t + L₂ x₁ + L₃ x₂` is a full-time predictor (`nativeParam`) in the parameters `(p, q)`
up to the velocity-bin and horizontal-equation errors (`native_fit_transfer`).

Also: Lipschitz bounds for `q3` on the unit cube, and the coefficient bound `512 E` from a sup
bound `E` on `[-1/8, 1/8]³`.
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

/-- Normalized coordinates of `(t, p, q)` for the domain `[t₀, t₀+τ] × [p₀, p₀+D] × [q₀, q₀+D]`. -/
noncomputable def normVec (t₀ τ p₀ q₀ D t p q : ℝ) : Fin 3 → ℝ :=
  ![(t - (t₀ + τ / 2)) / (4 * τ), (p - (p₀ + D / 2)) / (4 * D), (q - (q₀ + D / 2)) / (4 * D)]

/-- Normalized coefficients of the full-time predictor `h` on the domain. -/
noncomputable def normCoeffs (t₀ τ p₀ q₀ D : ℝ) (h : Fin 6 → ℝ) : Fin 10 → ℝ :=
  ![parameterPredictor h (t₀ + τ / 2) (p₀ + D / 2) (q₀ + D / 2),
    4 * τ * (h 1 + h 3 * (p₀ + D / 2) + h 5 * (q₀ + D / 2)),
    4 * D * (h 2 + h 3 * (t₀ + τ / 2)), 4 * D * (h 4 + h 5 * (t₀ + τ / 2)), 0, 0, 0,
    16 * τ * D * h 3, 16 * τ * D * h 5, 0]

theorem q3_normCoeffs (t₀ τ p₀ q₀ D : ℝ) (h : Fin 6 → ℝ) (u : Fin 3 → ℝ) :
    q3 (normCoeffs t₀ τ p₀ q₀ D h) u =
      parameterPredictor h (t₀ + τ / 2 + 4 * τ * u 0) (p₀ + D / 2 + 4 * D * u 1)
        (q₀ + D / 2 + 4 * D * u 2) := by
  simp only [q3, normCoeffs, parameterPredictor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem normVec_unnorm {t₀ τ p₀ q₀ D t p q : ℝ} (hτ : τ ≠ 0) (hD : D ≠ 0) :
    t₀ + τ / 2 + 4 * τ * normVec t₀ τ p₀ q₀ D t p q 0 = t ∧
    p₀ + D / 2 + 4 * D * normVec t₀ τ p₀ q₀ D t p q 1 = p ∧
    q₀ + D / 2 + 4 * D * normVec t₀ τ p₀ q₀ D t p q 2 = q := by
  simp only [normVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- In normalized coordinates the predictor is the quadratic `q3 (normCoeffs h)`. -/
theorem q3_normCoeffs_normVec {t₀ τ p₀ q₀ D : ℝ} (hτ : τ ≠ 0) (hD : D ≠ 0) (h : Fin 6 → ℝ)
    (t p q : ℝ) :
    q3 (normCoeffs t₀ τ p₀ q₀ D h) (normVec t₀ τ p₀ q₀ D t p q) = parameterPredictor h t p q := by
  obtain ⟨h0, h1, h2⟩ := normVec_unnorm (t₀ := t₀) (p₀ := p₀) (q₀ := q₀) (t := t) (p := p)
    (q := q) hτ hD
  rw [q3_normCoeffs, h0, h1, h2]

theorem normCoeffs_sub (t₀ τ p₀ q₀ D : ℝ) (h h' : Fin 6 → ℝ) :
    normCoeffs t₀ τ p₀ q₀ D h - normCoeffs t₀ τ p₀ q₀ D h' = normCoeffs t₀ τ p₀ q₀ D (h - h') := by
  ext k
  fin_cases k <;> simp [normCoeffs, parameterPredictor] <;> ring

theorem abs_sub_div_four_le {x c w : ℝ} (hw : 0 < w) (h1 : c - w / 2 ≤ x)
    (h2 : x ≤ c + w / 2) : |(x - c) / (4 * w)| ≤ 1 / 8 := by
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 4 * w), div_le_iff₀ (by linarith), abs_le]
  constructor <;> linarith

/-- Domain points have normalized coordinates in `[-1/8, 1/8]`. -/
theorem abs_normVec_le {t₀ τ p₀ q₀ D t p q : ℝ} (hτ : 0 < τ) (hD : 0 < D)
    (ht : t ∈ Set.Icc t₀ (t₀ + τ)) (hp : p ∈ Set.Icc p₀ (p₀ + D)) (hq : q ∈ Set.Icc q₀ (q₀ + D))
    (k : Fin 3) : |normVec t₀ τ p₀ q₀ D t p q k| ≤ 1 / 8 := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  fin_cases k <;> simp only [normVec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · exact abs_sub_div_four_le hτ (by linarith) (by linarith)
  · exact abs_sub_div_four_le hD (by linarith) (by linarith)
  · exact abs_sub_div_four_le hD (by linarith) (by linarith)

/-- Points with normalized coordinates in `[-1/8, 1/8]` lie in the `1/4`-ball. -/
theorem norm_toLp_le {u : Fin 3 → ℝ} (hu : ∀ k, |u k| ≤ 1 / 8) :
    ‖(WithLp.toLp 2 u : E3)‖ ≤ 1 / 4 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ i, ‖(WithLp.toLp 2 u : E3) i‖ ^ 2 ≤ (1 / 8) ^ 2 := fun i => by
    rw [Real.norm_eq_abs, sq_abs]
    have := hu i
    nlinarith [abs_nonneg (u i), sq_abs (u i)]
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 u : E3) i‖ ^ 2) ≤
        Real.sqrt (∑ _i : Fin 3, (1 / 8 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => h i)
    _ ≤ 1 / 4 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num

/-- Moving the base point by `ρ` in each coordinate of the unit cube moves `q3 a` by at most
`15 B ρ`. -/
theorem abs_q3_sub_le {a : Fin 10 → ℝ} {B ρ : ℝ} (ha : ∀ k, |a k| ≤ B) {u u' : Fin 3 → ℝ}
    (hu : ∀ i, |u i| ≤ 1) (hu' : ∀ i, |u' i| ≤ 1) (hρ : ∀ i, |u i - u' i| ≤ ρ) :
    |q3 a u - q3 a u'| ≤ 15 * B * ρ := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha 0)
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans (hρ 0)
  -- products of coordinates move by at most `2ρ`
  have hprod : ∀ i j, |u i * u j - u' i * u' j| ≤ 2 * ρ := by
    intro i j
    have e : u i * u j - u' i * u' j = (u i - u' i) * u j + u' i * (u j - u' j) := by ring
    rw [e]
    calc |(u i - u' i) * u j + u' i * (u j - u' j)|
        ≤ |(u i - u' i) * u j| + |u' i * (u j - u' j)| := abs_add_le _ _
      _ = |u i - u' i| * |u j| + |u' i| * |u j - u' j| := by rw [abs_mul, abs_mul]
      _ ≤ ρ * 1 + 1 * ρ := by
          gcongr
          · exact hρ i
          · exact hu j
          · exact hu' i
          · exact hρ j
      _ = 2 * ρ := by ring
  have hterm1 : ∀ (k : Fin 10) (i : Fin 3), |a k * u i - a k * u' i| ≤ B * ρ := by
    intro k i
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (ha k) (hρ i) (abs_nonneg _) hB
  have hterm2 : ∀ (k : Fin 10) (i j : Fin 3),
      |a k * (u i * u j) - a k * (u' i * u' j)| ≤ B * (2 * ρ) := by
    intro k i j
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (ha k) (hprod i j) (abs_nonneg _) hB
  have e : q3 a u - q3 a u' =
      (a 1 * u 0 - a 1 * u' 0) + (a 2 * u 1 - a 2 * u' 1) + (a 3 * u 2 - a 3 * u' 2) +
      (a 4 * (u 0 * u 0) - a 4 * (u' 0 * u' 0)) + (a 5 * (u 1 * u 1) - a 5 * (u' 1 * u' 1)) +
      (a 6 * (u 2 * u 2) - a 6 * (u' 2 * u' 2)) + (a 7 * (u 0 * u 1) - a 7 * (u' 0 * u' 1)) +
      (a 8 * (u 0 * u 2) - a 8 * (u' 0 * u' 2)) + (a 9 * (u 1 * u 2) - a 9 * (u' 1 * u' 2)) := by
    simp only [q3]; ring
  rw [e]
  have t1 := hterm1 1 0; have t2 := hterm1 2 1; have t3 := hterm1 3 2
  have t4 := hterm2 4 0 0; have t5 := hterm2 5 1 1; have t6 := hterm2 6 2 2
  have t7 := hterm2 7 0 1; have t8 := hterm2 8 0 2; have t9 := hterm2 9 1 2
  calc _ ≤ |a 1 * u 0 - a 1 * u' 0| + |a 2 * u 1 - a 2 * u' 1| + |a 3 * u 2 - a 3 * u' 2| +
        |a 4 * (u 0 * u 0) - a 4 * (u' 0 * u' 0)| + |a 5 * (u 1 * u 1) - a 5 * (u' 1 * u' 1)| +
        |a 6 * (u 2 * u 2) - a 6 * (u' 2 * u' 2)| + |a 7 * (u 0 * u 1) - a 7 * (u' 0 * u' 1)| +
        |a 8 * (u 0 * u 2) - a 8 * (u' 0 * u' 2)| + |a 9 * (u 1 * u 2) - a 9 * (u' 1 * u' 2)| := by
        repeat (first | refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl) | exact le_rfl)
    _ ≤ 15 * B * ρ := by linarith

/-- Halving the base point: `q3 (half3 a) x = q3 a (x / 2)`. -/
noncomputable def half3 (a : Fin 10 → ℝ) : Fin 10 → ℝ :=
  ![a 0, a 1 / 2, a 2 / 2, a 3 / 2, a 4 / 4, a 5 / 4, a 6 / 4, a 7 / 4, a 8 / 4, a 9 / 4]

theorem q3_half3 (a : Fin 10 → ℝ) (x : Fin 3 → ℝ) :
    q3 (half3 a) x = q3 a (fun i => x i / 2) := by
  simp only [q3, half3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- A quadratic bounded by `E` on `[-1/8, 1/8]³` has coefficients at most `512 E`. -/
theorem abs_coeff_le_of_sup {a : Fin 10 → ℝ} {E : ℝ}
    (h : ∀ u : Fin 3 → ℝ, (∀ i, |u i| ≤ 1 / 8) → |q3 a u| ≤ E) (k : Fin 10) :
    |a k| ≤ 512 * E := by
  have hs : ∀ k, |q3 (half3 a) (samples k)| ≤ E := by
    intro k
    rw [q3_half3]
    apply h
    intro i
    have := samples_norm k i
    rw [abs_div, abs_two]
    linarith
  have hc := cnorm3_le_of_samples hs
  have hk : ∀ k, |half3 a k| ≤ 128 * E := fun k => (abs_le_cnorm3 _ k).trans hc
  have hE : 0 ≤ E := by
    have := h 0 (fun i => by simp)
    exact (abs_nonneg _).trans this
  have h0 := hk 0; have h1 := hk 1; have h2 := hk 2; have h3 := hk 3; have h4 := hk 4
  have h5 := hk 5; have h6 := hk 6; have h7 := hk 7; have h8 := hk 8; have h9 := hk 9
  simp only [half3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, abs_div,
    abs_two, show |(4 : ℝ)| = 4 by norm_num] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    linarith

/-- A full-time predictor bounded by `E` on the domain has normalized coefficients at most
`512 E`. -/
theorem abs_normCoeffs_le {t₀ τ p₀ q₀ D E : ℝ} (hτ : 0 < τ) (hD : 0 < D) {h : Fin 6 → ℝ}
    (hE : ∀ t ∈ Set.Icc t₀ (t₀ + τ), ∀ p ∈ Set.Icc p₀ (p₀ + D), ∀ q ∈ Set.Icc q₀ (q₀ + D),
      |parameterPredictor h t p q| ≤ E) (k : Fin 10) :
    |normCoeffs t₀ τ p₀ q₀ D h k| ≤ 512 * E := by
  apply abs_coeff_le_of_sup _ k
  intro u hu
  rw [q3_normCoeffs]
  have h0 := abs_le.mp (hu 0); have h1 := abs_le.mp (hu 1); have h2 := abs_le.mp (hu 2)
  apply hE
  · constructor <;> nlinarith
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-! ### Native affine predictors as full-time predictors -/

/-- The native affine predictor `L₀ + L₁ t + L₂ (p + t v) + L₃ (q - t p)` in the parameters. -/
def nativeParam (L : Fin 4 → ℝ) (v : ℝ) : Fin 6 → ℝ :=
  ![L 0, L 1 + L 2 * v, L 2, -L 3, L 3, 0]

theorem parameterPredictor_nativeParam (L : Fin 4 → ℝ) (v t p q : ℝ) :
    parameterPredictor (nativeParam L v) t p q =
      L 0 + L 1 * t + L 2 * (p + t * v) + L 3 * (q - t * p) := by
  simp only [parameterPredictor, nativeParam, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- A native affine fit in the spatial coordinates `(t, Z, Y)` is a fit of the full-time
predictor `nativeParam L v` at the parameters `(p, q)`, up to the velocity-bin error
`|Z - (p + t v)| ≤ χ` and the horizontal-equation error `|Y - (q - t p)| ≤ e`. -/
theorem native_fit_transfer {L : Fin 4 → ℝ} {v t p q Z Y X a χ e : ℝ}
    (hfit : |X - (L 0 + L 1 * t + L 2 * Z + L 3 * Y)| ≤ a)
    (hZ : |Z - (p + t * v)| ≤ χ) (hY : |Y - (q - t * p)| ≤ e) :
    |X - parameterPredictor (nativeParam L v) t p q| ≤ a + |L 2| * χ + |L 3| * e := by
  rw [parameterPredictor_nativeParam]
  have e1 : X - (L 0 + L 1 * t + L 2 * (p + t * v) + L 3 * (q - t * p)) =
      (X - (L 0 + L 1 * t + L 2 * Z + L 3 * Y)) + L 2 * (Z - (p + t * v)) +
        L 3 * (Y - (q - t * p)) := by ring
  rw [e1]
  calc _ ≤ |X - (L 0 + L 1 * t + L 2 * Z + L 3 * Y)| + |L 2 * (Z - (p + t * v))| +
        |L 3 * (Y - (q - t * p))| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ a + |L 2| * χ + |L 3| * e := by
        rw [abs_mul, abs_mul]
        gcongr

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
