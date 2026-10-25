/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/Quad3.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation, session x0764, Match3/Quad3.lean, commit372514ca. -/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Quadratics in three variables by coefficient vectors

`q3 a x = a₀ + a₁x₀ + a₂x₁ + a₃x₂ + a₄x₀² + a₅x₁² + a₆x₂² + a₇x₀x₁ + a₈x₀x₂ + a₉x₁x₂`.

* `q3_sub`, `q3_smul`: linearity in the coefficients.
* `abs_q3_le`: `|q3 a x| ≤ 10 ‖a‖` when `|xₖ| ≤ 1`.
* `cnorm3_le_of_samples`: the coefficients are recovered from the values at ten fixed sample
  points of Euclidean norm `≤ √2/4 < 1/2`, so `‖a‖ ≤ 128 E` if `|q3 a| ≤ E` at those points;
  hence a large coefficient vector has a large value somewhere in the half ball
  (`exists_sample_large`).

Used for the three-dimensional matching lemma (`Match3/*`).
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

/-- The base space of the three-dimensional matching lemma. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The quadratic with coefficient vector `a`. -/
def q3 (a : Fin 10 → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  a 0 + a 1 * x 0 + a 2 * x 1 + a 3 * x 2 + a 4 * x 0 ^ 2 + a 5 * x 1 ^ 2 + a 6 * x 2 ^ 2 +
    a 7 * (x 0 * x 1) + a 8 * (x 0 * x 2) + a 9 * (x 1 * x 2)

/-- The sup norm of a coefficient vector. -/
noncomputable def cnorm3 (a : Fin 10 → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun k => |a k|

theorem abs_le_cnorm3 (a : Fin 10 → ℝ) (k : Fin 10) : |a k| ≤ cnorm3 a :=
  Finset.le_sup' (fun k => |a k|) (Finset.mem_univ k)

theorem cnorm3_nonneg (a : Fin 10 → ℝ) : 0 ≤ cnorm3 a := (abs_nonneg _).trans (abs_le_cnorm3 a 0)

theorem cnorm3_le {a : Fin 10 → ℝ} {B : ℝ} (h : ∀ k, |a k| ≤ B) : cnorm3 a ≤ B :=
  Finset.sup'_le _ _ fun k _ => h k

theorem exists_eq_cnorm3 (a : Fin 10 → ℝ) : ∃ k, |a k| = cnorm3 a := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => |a k|)
  exact ⟨k, hk.symm⟩

theorem q3_sub (a b : Fin 10 → ℝ) (x : Fin 3 → ℝ) : q3 (a - b) x = q3 a x - q3 b x := by
  simp only [q3, Pi.sub_apply]; ring

theorem q3_smul (c : ℝ) (a : Fin 10 → ℝ) (x : Fin 3 → ℝ) : q3 (c • a) x = c * q3 a x := by
  simp only [q3, Pi.smul_apply, smul_eq_mul]; ring

/-- Values on the unit cube are bounded by ten times the coefficient norm. -/
theorem abs_q3_le {a : Fin 10 → ℝ} {B : ℝ} (ha : ∀ k, |a k| ≤ B) {x : Fin 3 → ℝ}
    (hx : ∀ i, |x i| ≤ 1) : |q3 a x| ≤ 10 * B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha 0)
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2
  have hp : ∀ u v : ℝ, |u| ≤ 1 → |v| ≤ 1 → |u * v| ≤ 1 := fun u v hu hv => by
    rw [abs_mul]; nlinarith [abs_nonneg u, abs_nonneg v]
  have hsq : ∀ u : ℝ, |u| ≤ 1 → |u ^ 2| ≤ 1 := fun u hu => by
    rw [sq]; exact hp u u hu hu
  have hterm : ∀ (k : Fin 10) (m : ℝ), |m| ≤ 1 → |a k * m| ≤ B := fun k m hm => by
    rw [abs_mul]; calc |a k| * |m| ≤ B * 1 := mul_le_mul (ha k) hm (abs_nonneg _) hB
      _ = B := mul_one B
  unfold q3
  calc |a 0 + a 1 * x 0 + a 2 * x 1 + a 3 * x 2 + a 4 * x 0 ^ 2 + a 5 * x 1 ^ 2 +
        a 6 * x 2 ^ 2 + a 7 * (x 0 * x 1) + a 8 * (x 0 * x 2) + a 9 * (x 1 * x 2)|
      ≤ |a 0| + |a 1 * x 0| + |a 2 * x 1| + |a 3 * x 2| + |a 4 * x 0 ^ 2| + |a 5 * x 1 ^ 2| +
        |a 6 * x 2 ^ 2| + |a 7 * (x 0 * x 1)| + |a 8 * (x 0 * x 2)| + |a 9 * (x 1 * x 2)| := by
        repeat (first | refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl) | exact le_rfl)
    _ ≤ B + B + B + B + B + B + B + B + B + B := by
        gcongr
        · exact ha 0
        all_goals first
          | exact hterm _ _ (by assumption)
          | exact hterm _ _ (hsq _ (by assumption))
          | exact hterm _ _ (hp _ _ (by assumption) (by assumption))
    _ = 10 * B := by ring

/-- The ten sample points: `0`, `±r eᵢ`, `r(eᵢ + eⱼ)` with `r = 1/4`. -/
noncomputable def samples : Fin 10 → Fin 3 → ℝ :=
  ![0, ![1/4, 0, 0], ![-1/4, 0, 0], ![0, 1/4, 0], ![0, -1/4, 0], ![0, 0, 1/4], ![0, 0, -1/4],
    ![1/4, 1/4, 0], ![1/4, 0, 1/4], ![0, 1/4, 1/4]]

theorem samples_norm (k : Fin 10) (i : Fin 3) : |samples k i| ≤ 1 / 4 := by
  fin_cases k <;> fin_cases i <;> norm_num [samples]

/-- Recovery of the coefficients from the sample values. -/
theorem cnorm3_le_of_samples {a : Fin 10 → ℝ} {E : ℝ}
    (h : ∀ k, |q3 a (samples k)| ≤ E) : cnorm3 a ≤ 128 * E := by
  have hE : 0 ≤ E := (abs_nonneg _).trans (h 0)
  have v0 : q3 a (samples 0) = a 0 := by simp [q3, samples]
  have v1 : q3 a (samples 1) = a 0 + a 1 / 4 + a 4 / 16 := by simp [q3, samples]; ring
  have v2 : q3 a (samples 2) = a 0 - a 1 / 4 + a 4 / 16 := by simp [q3, samples]; ring
  have v3 : q3 a (samples 3) = a 0 + a 2 / 4 + a 5 / 16 := by simp [q3, samples]; ring
  have v4 : q3 a (samples 4) = a 0 - a 2 / 4 + a 5 / 16 := by simp [q3, samples]; ring
  have v5 : q3 a (samples 5) = a 0 + a 3 / 4 + a 6 / 16 := by simp [q3, samples]; ring
  have v6 : q3 a (samples 6) = a 0 - a 3 / 4 + a 6 / 16 := by simp [q3, samples]; ring
  have v7 : q3 a (samples 7) = a 0 + a 1 / 4 + a 2 / 4 + a 4 / 16 + a 5 / 16 + a 7 / 16 := by
    simp [q3, samples]; ring
  have v8 : q3 a (samples 8) = a 0 + a 1 / 4 + a 3 / 4 + a 4 / 16 + a 6 / 16 + a 8 / 16 := by
    simp [q3, samples]; ring
  have v9 : q3 a (samples 9) = a 0 + a 2 / 4 + a 3 / 4 + a 5 / 16 + a 6 / 16 + a 9 / 16 := by
    simp [q3, samples]; ring
  have b : ∀ k, -E ≤ q3 a (samples k) ∧ q3 a (samples k) ≤ E := fun k => abs_le.mp (h k)
  obtain ⟨b0l, b0u⟩ := b 0; obtain ⟨b1l, b1u⟩ := b 1; obtain ⟨b2l, b2u⟩ := b 2
  obtain ⟨b3l, b3u⟩ := b 3; obtain ⟨b4l, b4u⟩ := b 4; obtain ⟨b5l, b5u⟩ := b 5
  obtain ⟨b6l, b6u⟩ := b 6; obtain ⟨b7l, b7u⟩ := b 7; obtain ⟨b8l, b8u⟩ := b 8
  obtain ⟨b9l, b9u⟩ := b 9
  rw [v0] at b0l b0u; rw [v1] at b1l b1u; rw [v2] at b2l b2u; rw [v3] at b3l b3u
  rw [v4] at b4l b4u; rw [v5] at b5l b5u; rw [v6] at b6l b6u; rw [v7] at b7l b7u
  rw [v8] at b8l b8u; rw [v9] at b9l b9u
  apply cnorm3_le
  intro k
  rw [abs_le]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    constructor <;> linarith

/-- A coefficient vector of norm at least `M` has a value at least `M/128` at a sample point. -/
theorem exists_sample_large {a : Fin 10 → ℝ} {M : ℝ} (hM : M ≤ cnorm3 a) :
    ∃ k, M / 128 ≤ |q3 a (samples k)| := by
  by_contra hne
  push Not at hne
  set E := Finset.univ.sup' Finset.univ_nonempty fun k => |q3 a (samples k)| with hEdef
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun k => |q3 a (samples k)|)
  have hEk : ∀ k, |q3 a (samples k)| ≤ E := fun k =>
    Finset.le_sup' (fun k => |q3 a (samples k)|) (Finset.mem_univ k)
  have hElt : E < M / 128 := by rw [hEdef, hk₀]; exact hne k₀
  have := cnorm3_le_of_samples (a := a) (E := E) hEk
  linarith

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
