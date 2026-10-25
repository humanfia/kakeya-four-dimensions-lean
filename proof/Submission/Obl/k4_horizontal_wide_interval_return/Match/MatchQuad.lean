/- Adapted within this LOT tree (g-oai-074) from o227 `k4_horizontal_three_projection_wide_return`,
session x0788, branch x0788, commit d1137a70, file
Submission/Obl/k4_horizontal_three_projection_wide_return/MatchQuad.lean (namespace renamed into o250's). -/
import Mathlib

/-!
# Quadratic functions of one variable for the matching lemma

`quad c x = c 0 + c 1 * x + c 2 * x ^ 2`, its derivatives, and the elementary
fact that a quadratic whose coefficient vector has sup-norm at least one and
whose value at a point of `[0,1]` is small has a large first or second
derivative there.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.MatchQuad

/-- The quadratic with coefficient vector `c`. -/
def quad (c : Fin 3 → ℝ) (x : ℝ) : ℝ := c 0 + c 1 * x + c 2 * x ^ 2

lemma hasDerivAt_quad (c : Fin 3 → ℝ) (x : ℝ) :
    HasDerivAt (quad c) (c 1 + 2 * c 2 * x) x := by
  have h1 := (hasDerivAt_id x).const_mul (c 1)
  have h2 := (hasDerivAt_pow 2 x).const_mul (c 2)
  have h := ((hasDerivAt_const x (c 0)).add h1).add h2
  have hf : quad c = ((fun _ : ℝ => c 0) + fun y => c 1 * id y) + fun y => c 2 * y ^ 2 := by
    funext y; simp [quad]
  rw [hf]
  convert h using 1
  simp; ring

lemma deriv_quad (c : Fin 3 → ℝ) :
    deriv (quad c) = fun x => c 1 + 2 * c 2 * x := by
  funext x; exact (hasDerivAt_quad c x).deriv

lemma deriv_deriv_quad (c : Fin 3 → ℝ) :
    deriv (deriv (quad c)) = fun _ => 2 * c 2 := by
  rw [deriv_quad]
  funext x
  have h := ((hasDerivAt_id x).const_mul (2 * c 2)).const_add (c 1)
  have := h.deriv
  simp at this ⊢

lemma iteratedDeriv_one_quad (c : Fin 3 → ℝ) (x : ℝ) :
    iteratedDeriv 1 (quad c) x = c 1 + 2 * c 2 * x := by
  rw [iteratedDeriv_one, deriv_quad]

lemma iteratedDeriv_two_quad (c : Fin 3 → ℝ) (x : ℝ) :
    iteratedDeriv 2 (quad c) x = 2 * c 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_deriv_quad]

lemma iteratedDeriv_three_quad (c : Fin 3 → ℝ) :
    iteratedDeriv 3 (quad c) = fun _ => 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, deriv_deriv_quad]
  funext x; simp

lemma iteratedDeriv_quad_add_three (c : Fin 3 → ℝ) (m : ℕ) :
    iteratedDeriv (3 + m) (quad c) = fun _ => 0 := by
  induction m with
  | zero => simp [iteratedDeriv_three_quad]
  | succ m ih =>
    rw [show 3 + (m + 1) = (3 + m) + 1 by ring, iteratedDeriv_succ, ih]
    funext x; simp

lemma iteratedDeriv_quad_of_three_le (c : Fin 3 → ℝ) {j : ℕ} (hj : 3 ≤ j) (x : ℝ) :
    iteratedDeriv j (quad c) x = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [iteratedDeriv_quad_add_three]

lemma contDiff_quad (c : Fin 3 → ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (quad c) := by
  unfold quad
  fun_prop

/-- Sup-norm of a coefficient vector. -/
noncomputable def cnorm (c : Fin 3 → ℝ) : ℝ := max |c 0| (max |c 1| |c 2|)

lemma abs_le_cnorm (c : Fin 3 → ℝ) (k : Fin 3) : |c k| ≤ cnorm c := by
  unfold cnorm
  fin_cases k <;> simp

/-- Bounds for the value and the derivatives of a quadratic on `[0,1]`. -/
lemma abs_quad_le (c : Fin 3 → ℝ) {B x : ℝ} (hc : ∀ k, |c k| ≤ B) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |quad c x| ≤ 3 * B := by
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
  obtain ⟨hx0, hx1⟩ := hx
  unfold quad
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hx2' : 0 ≤ x ^ 2 := by positivity
  calc |c 0 + c 1 * x + c 2 * x ^ 2| ≤ |c 0| + |c 1 * x| + |c 2 * x ^ 2| := abs_add_three _ _ _
    _ = |c 0| + |c 1| * x + |c 2| * x ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hx0, abs_of_nonneg hx2']
    _ ≤ B + B * 1 + B * 1 := by
        gcongr
        · exact le_trans (abs_nonneg _) h0
        · exact le_trans (abs_nonneg _) h0
    _ = 3 * B := by ring

lemma abs_iteratedDeriv_quad_le (c : Fin 3 → ℝ) {B x : ℝ} (hc : ∀ k, |c k| ≤ B)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (j : ℕ) :
    |iteratedDeriv j (quad c) x| ≤ 3 * B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hc 0)
  have h1 := hc 1; have h2 := hc 2
  obtain ⟨hx0, hx1⟩ := hx
  rcases j with _ | _ | _ | j
  · simpa using abs_quad_le c hc ⟨hx0, hx1⟩
  · rw [iteratedDeriv_one_quad]
    calc |c 1 + 2 * c 2 * x| ≤ |c 1| + |2 * c 2 * x| := abs_add_le _ _
      _ = |c 1| + 2 * |c 2| * x := by rw [abs_mul, abs_mul, abs_of_nonneg hx0]; norm_num
      _ ≤ B + 2 * B * 1 := by gcongr
      _ = 3 * B := by ring
  · rw [iteratedDeriv_two_quad, abs_mul]; norm_num; linarith
  · rw [iteratedDeriv_quad_of_three_le c (by omega)]; simp; linarith

lemma quad_sub (c c' : Fin 3 → ℝ) (x : ℝ) :
    quad c x - quad c' x = quad (c - c') x := by
  simp [quad]; ring

/-- A quadratic whose coefficients have sup-norm at least one, and whose value at a
point of `[0,1]` is at most `1/4`, has first derivative at least `1/8` or second
derivative at least `1/4` in absolute value at that point. -/
lemma deriv_separation (c : Fin 3 → ℝ) (hc : 1 ≤ cnorm c) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hval : |quad c x| ≤ 1 / 4) :
    1 / 8 ≤ |iteratedDeriv 1 (quad c) x| ∨ 1 / 8 ≤ |iteratedDeriv 2 (quad c) x| := by
  rw [iteratedDeriv_one_quad, iteratedDeriv_two_quad]
  obtain ⟨hx0, hx1⟩ := hx
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hc2 : |c 2| < 1 / 16 := by rw [abs_mul] at h2; norm_num at h2; linarith
  have hc1 : |c 1| < 1 / 4 := by
    have : |c 1| ≤ |c 1 + 2 * c 2 * x| + |2 * c 2 * x| := by
      calc |c 1| = |(c 1 + 2 * c 2 * x) - 2 * c 2 * x| := by ring_nf
        _ ≤ |c 1 + 2 * c 2 * x| + |2 * c 2 * x| := abs_sub _ _
    have h3 : |2 * c 2 * x| ≤ 2 * |c 2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hx0]; norm_num; nlinarith [abs_nonneg (c 2)]
    linarith
  have hc0 : |c 0| < 1 := by
    have e : c 0 = quad c x - c 1 * x - c 2 * x ^ 2 := by simp [quad]; ring
    have h3 : |c 1 * x| ≤ |c 1| := by
      rw [abs_mul, abs_of_nonneg hx0]; nlinarith [abs_nonneg (c 1)]
    have h4 : |c 2 * x ^ 2| ≤ |c 2| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2)]
      have : x ^ 2 ≤ 1 := by nlinarith
      nlinarith [abs_nonneg (c 2)]
    calc |c 0| = |quad c x - c 1 * x - c 2 * x ^ 2| := by rw [← e]
      _ ≤ |quad c x| + |c 1 * x| + |c 2 * x ^ 2| := by
          have := abs_sub (quad c x - c 1 * x) (c 2 * x ^ 2)
          have := abs_sub (quad c x) (c 1 * x)
          linarith
      _ < 1 := by linarith
  have : cnorm c < 1 := by
    unfold cnorm
    exact max_lt hc0 (max_lt (by linarith) (by linarith))
  linarith

end Submission.Obl.k4_horizontal_wide_interval_return.MatchQuad
