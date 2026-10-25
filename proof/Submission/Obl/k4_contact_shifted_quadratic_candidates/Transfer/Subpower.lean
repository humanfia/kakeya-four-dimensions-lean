/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/Subpower.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Mathlib

/-!
# Subpower sequences

`Small N x`: the sequence `x` is eventually nonnegative and eventually below
every positive power of `N`. Such sequences are closed under the operations
used by the residual constants: sums, products, natural and nonnegative real
powers, maxima, and they absorb fixed constants.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open Filter

noncomputable section

/-- Eventually nonnegative and eventually below every positive power of `N`. -/
def Small (N x : ℕ → ℝ) : Prop :=
  (∀ᶠ k in atTop, 0 ≤ x k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, x k ≤ N k ^ ε

variable {N : ℕ → ℝ}

theorem eventually_const_le_rpow (hNt : Tendsto N atTop atTop) (c : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ k in atTop, c ≤ N k ^ ε :=
  ((tendsto_rpow_atTop hε).comp hNt).eventually_ge_atTop c

theorem Small.const (hNt : Tendsto N atTop atTop) {c : ℝ} (hc : 0 ≤ c) :
    Small N (fun _ => c) :=
  ⟨Eventually.of_forall fun _ => hc, fun _ hε => eventually_const_le_rpow hNt c hε⟩

theorem Small.mono {x y : ℕ → ℝ} (hy : Small N y) (hx0 : ∀ᶠ k in atTop, 0 ≤ x k)
    (hxy : ∀ᶠ k in atTop, x k ≤ y k) : Small N x :=
  ⟨hx0, fun ε hε => by
    filter_upwards [hxy, hy.2 ε hε] with k h1 h2
    exact h1.trans h2⟩

theorem Small.mul (hN : ∀ k, 0 ≤ N k) {x y : ℕ → ℝ} (hx : Small N x) (hy : Small N y) :
    Small N (fun k => x k * y k) := by
  refine ⟨?_, fun ε hε => ?_⟩
  · filter_upwards [hx.1, hy.1] with k h1 h2
    exact mul_nonneg h1 h2
  · filter_upwards [hx.1, hy.1, hx.2 (ε / 2) (by positivity), hy.2 (ε / 2) (by positivity)]
      with k h1 h2 h3 h4
    calc x k * y k ≤ N k ^ (ε / 2) * N k ^ (ε / 2) :=
          mul_le_mul h3 h4 h2 (Real.rpow_nonneg (hN k) _)
      _ = N k ^ ε := by
          rw [← Real.rpow_add' (hN k) (by positivity)]
          ring_nf

theorem Small.add (hNt : Tendsto N atTop atTop) {x y : ℕ → ℝ} (hx : Small N x)
    (hy : Small N y) : Small N (fun k => x k + y k) := by
  refine ⟨?_, fun ε hε => ?_⟩
  · filter_upwards [hx.1, hy.1] with k h1 h2
    exact add_nonneg h1 h2
  · have h2N : ∀ᶠ k in atTop, 2 ≤ N k ^ (ε / 2) := eventually_const_le_rpow hNt 2 (by positivity)
    have hNpos : ∀ᶠ k in atTop, 0 < N k := hNt.eventually_gt_atTop 0
    filter_upwards [hx.2 (ε / 2) (by positivity), hy.2 (ε / 2) (by positivity), h2N, hNpos]
      with k h3 h4 h5 h6
    calc x k + y k ≤ 2 * N k ^ (ε / 2) := by linarith
      _ ≤ N k ^ (ε / 2) * N k ^ (ε / 2) :=
          mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg h6.le _)
      _ = N k ^ ε := by
          rw [← Real.rpow_add h6]
          ring_nf

theorem Small.pow (hN : ∀ k, 0 ≤ N k) (hNt : Tendsto N atTop atTop) {x : ℕ → ℝ}
    (hx : Small N x) (n : ℕ) : Small N (fun k => x k ^ n) := by
  induction n with
  | zero => simpa using Small.const hNt (c := 1) zero_le_one
  | succ n ih =>
    have := ih.mul hN hx
    simpa [pow_succ] using this

theorem Small.rpow (hN : ∀ k, 1 ≤ N k) {x : ℕ → ℝ} (hx : Small N x) {a : ℝ} (ha : 0 ≤ a) :
    Small N (fun k => x k ^ a) := by
  refine ⟨?_, fun ε hε => ?_⟩
  · filter_upwards [hx.1] with k h1
    exact Real.rpow_nonneg h1 a
  · rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0
      refine Eventually.of_forall fun k => ?_
      simpa using Real.one_le_rpow (hN k) hε.le
    · filter_upwards [hx.1, hx.2 (ε / a) (by positivity)] with k h1 h2
      calc x k ^ a ≤ (N k ^ (ε / a)) ^ a := Real.rpow_le_rpow h1 h2 ha
        _ = N k ^ ε := by
            rw [← Real.rpow_mul (by linarith [hN k])]
            congr 1
            field_simp

theorem Small.max (hNt : Tendsto N atTop atTop) {x y : ℕ → ℝ} (hx : Small N x)
    (hy : Small N y) : Small N (fun k => max (x k) (y k)) := by
  refine (hx.add hNt hy).mono ?_ ?_
  · filter_upwards [hx.1] with k h1
    exact h1.trans (le_max_left _ _)
  · filter_upwards [hx.1, hy.1] with k h1 h2
    exact max_le (by linarith) (by linarith)

/-- A sequence whose exponents tend to zero gives a subpower power of `N`. -/
theorem Small.rpow_of_exponent (hN : ∀ k, 1 ≤ N k) {g : ℕ → ℝ}
    (hg : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, g k ≤ ε) : Small N (fun k => N k ^ g k) :=
  ⟨Eventually.of_forall fun k => Real.rpow_nonneg (by linarith [hN k]) _, fun ε hε => by
    filter_upwards [hg ε hε] with k hk
    exact Real.rpow_le_rpow_of_exponent_le (hN k) hk⟩

/-- The inverse of a sequence above every negative power of `N` is subpower. -/
theorem Small.inv_of_large {θ : ℕ → ℝ}
    (hθ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, N k ^ (-ε) ≤ θ k)
    (hNpos : ∀ k, 0 < N k) : Small N (fun k => (θ k)⁻¹) := by
  refine ⟨?_, fun ε hε => ?_⟩
  · filter_upwards [hθ 1 one_pos] with k hk
    exact inv_nonneg.mpr ((Real.rpow_pos_of_pos (hNpos k) _).le.trans hk)
  · filter_upwards [hθ ε hε] with k hk
    have hp := Real.rpow_pos_of_pos (hNpos k) (-ε)
    calc (θ k)⁻¹ ≤ (N k ^ (-ε))⁻¹ := inv_anti₀ hp hk
      _ = N k ^ ε := by rw [Real.rpow_neg (hNpos k).le, inv_inv]

/-- A subpower sequence is eventually below any fixed positive multiple of a
positive power. -/
theorem Small.le_mul_rpow (hNt : Tendsto N atTop atTop) {x : ℕ → ℝ} (hx : Small N x)
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) : ∀ᶠ k in atTop, x k ≤ c * N k ^ γ := by
  have hNpos : ∀ᶠ k in atTop, 0 < N k := hNt.eventually_gt_atTop 0
  filter_upwards [hx.2 (γ / 2) (by positivity), eventually_const_le_rpow hNt c⁻¹ (by positivity :
    0 < γ / 2), hNpos] with k h1 h2 h3
  have h4 : N k ^ γ = N k ^ (γ / 2) * N k ^ (γ / 2) := by
    rw [← Real.rpow_add h3]; ring_nf
  have h5 : 1 ≤ c * N k ^ (γ / 2) := by
    calc (1 : ℝ) = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
      _ ≤ c * N k ^ (γ / 2) := mul_le_mul_of_nonneg_left h2 hc.le
  calc x k ≤ N k ^ (γ / 2) := h1
    _ = 1 * N k ^ (γ / 2) := (one_mul _).symm
    _ ≤ c * N k ^ (γ / 2) * N k ^ (γ / 2) :=
        mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg h3.le _)
    _ = c * N k ^ γ := by rw [h4]; ring

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
