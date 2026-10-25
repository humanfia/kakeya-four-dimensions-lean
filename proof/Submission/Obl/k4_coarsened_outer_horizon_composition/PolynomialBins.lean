import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open Set Metric
open Submission.Lib.K4QuadraticSublevel

lemma quadratic_second_constant (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) (x : ℝ) :
    p.derivative.derivative.eval x = p.derivative.derivative.eval 0 := by
  obtain ⟨a, b, c, rfl⟩ := quadratic_eq_coefficients p hp
  simp

lemma quadratic_derivative_sub (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) (x y : ℝ) :
    p.derivative.eval y - p.derivative.eval x =
      p.derivative.derivative.eval 0 * (y - x) := by
  obtain ⟨a, b, c, rfl⟩ := quadratic_eq_coefficients p hp
  simp
  ring

lemma quadratic_taylor (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) (x y : ℝ) :
    p.eval y = p.eval x + (y - x) * p.derivative.eval x +
      (y - x) ^ 2 / 2 * p.derivative.derivative.eval 0 := by
  obtain ⟨a, b, c, rfl⟩ := quadratic_eq_coefficients p hp
  simp
  ring

/-- Polynomial tests at an integer representative, with a curvature alternative.
The curvature alternative covers a bin containing a critical point. -/
def binTest (p : Polynomial ℝ) (κ a b : ℝ) (n : ℤ) : Prop :=
  |p.eval ((n : ℝ) * a)| ≤ 3 * κ * a * b ∧
    (b / (2 * κ) ≤ |p.derivative.eval ((n : ℝ) * a)| ∨
      b / (2 * κ) ≤ |p.derivative.derivative.eval 0| * a)

lemma floor_bin_distance {a : ℝ} (ha : 0 < a) (w : ℝ) :
    |(⌊w / a⌋ : ℝ) * a - w| ≤ a := by
  have hlo := (mul_le_mul_of_nonneg_right (Int.floor_le (w / a)) ha.le)
  have hhi := (mul_lt_mul_of_pos_right (Int.lt_floor_add_one (w / a)) ha)
  rw [div_mul_cancel₀ _ ha.ne'] at hlo hhi
  rw [abs_le]
  constructor <;> nlinarith

/-- Every selected hidden coordinate passes the representative-bin tests. -/
theorem binTest_of_bounds (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {κ a b w : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hv : |p.eval w| ≤ κ * a * b)
    (hd : |p.derivative.eval w| ≤ κ * b)
    (hc : |p.derivative.derivative.eval 0| ≤ κ * b / a)
    (hfloor : b / κ ≤ |p.derivative.eval w|) : binTest p κ a b ⌊w / a⌋ := by
  let z : ℝ := (⌊w / a⌋ : ℝ) * a
  have hdist : |z - w| ≤ a := floor_bin_distance ha w
  constructor
  · calc
      |p.eval z| ≤ |p.eval w| + |z - w| * |p.derivative.eval w| +
          |z - w| ^ 2 / 2 * |p.derivative.derivative.eval 0| := by
        rw [quadratic_taylor p hp w z]
        calc
          _ ≤ |p.eval w + (z - w) * p.derivative.eval w| +
              |(z - w) ^ 2 / 2 * p.derivative.derivative.eval 0| := abs_add_le _ _
          _ ≤ _ := by
            rw [abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            gcongr
            exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
      _ ≤ κ * a * b + a * (κ * b) + a ^ 2 / 2 * (κ * b / a) := by gcongr
      _ = 5 / 2 * (κ * a * b) := by field_simp; ring
      _ ≤ 3 * κ * a * b := by nlinarith [mul_pos (mul_pos hκ ha) hb]
  · by_cases hhigh : b / (2 * κ) ≤ |p.derivative.derivative.eval 0| * a
    · exact Or.inr hhigh
    · left
      by_contra hlow
      have h1 : |p.derivative.eval z| < b / (2 * κ) := lt_of_not_ge hlow
      have h2 : |p.derivative.derivative.eval 0| * a < b / (2 * κ) := lt_of_not_ge hhigh
      have hdiff := quadratic_derivative_sub p hp z w
      have hdiffabs : |p.derivative.eval w - p.derivative.eval z| ≤
          |p.derivative.derivative.eval 0| * a := by
        rw [hdiff, abs_mul]
        gcongr
        simpa [abs_sub_comm] using hdist
      have htri := abs_add_le (p.derivative.eval z)
        (p.derivative.eval w - p.derivative.eval z)
      have heq : p.derivative.eval z + (p.derivative.eval w - p.derivative.eval z) =
          p.derivative.eval w := by ring
      rw [heq] at htri
      have hhalf : b / (2 * κ) + b / (2 * κ) = b / κ := by ring
      linarith

/-- The explicit polynomial bin test has a uniform quadratic slack budget. -/
theorem binTest_count (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {κ a b : ℝ} (hκ : 1 ≤ κ) (ha : 0 < a) (hb : 0 < b) :
    {n : ℤ | binTest p κ a b n}.Finite ∧
      ({n : ℤ | binTest p κ a b n}.ncard : ℝ) ≤ 64 * κ ^ 2 := by
  have hκ0 : 0 < κ := by linarith
  let ε : ℝ := 3 * κ * a * b
  let d : ℝ := b / (2 * κ)
  have hd : 0 < d := by dsimp [d]; positivity
  let R : Set ℝ := {w | |p.eval w| ≤ ε ∧ d ≤ |p.derivative.eval w|}
  let S : Set ℤ := (fun w : ℝ => ⌊(w - 0) / a⌋) '' R
  have hS := grid_bins_quadratic_sublevel p hp (show 0 ≤ ε by dsimp [ε]; positivity) hd ha 0
  change S.Finite ∧ (S.ncard : ℝ) ≤ 8 * (1 + ε / (d * a)) at hS
  have hnumber : ε / (d * a) = 6 * κ ^ 2 := by
    dsimp [ε, d]
    field_simp
    ring
  rw [hnumber] at hS
  have hrep (n : ℤ) : ⌊((n : ℝ) * a - 0) / a⌋ = n := by
    rw [sub_zero, mul_div_cancel_right₀ _ ha.ne', Int.floor_intCast]
  by_cases hhigh : d ≤ |p.derivative.derivative.eval 0| * a
  · let T : Set ℝ := {w | |p.derivative.eval w| ≤ d}
    let U : Set ℤ := (fun w : ℝ => ⌊(w - 0) / a⌋) '' T
    have hcurv : 0 < |p.derivative.derivative.eval 0| := by
      have : 0 < |p.derivative.derivative.eval 0| * a := hd.trans_le hhigh
      exact (mul_pos_iff_of_pos_right ha).mp this
    have hdiam : ∀ x ∈ T, ∀ y ∈ T, dist x y ≤ 2 * a := by
      intro x hx y hy
      change |p.derivative.eval x| ≤ d at hx
      change |p.derivative.eval y| ≤ d at hy
      have heq := quadratic_derivative_sub p hp x y
      have hdiff : |p.derivative.derivative.eval 0| * dist x y ≤ 2 * d := by
        rw [dist_comm, Real.dist_eq, ← abs_mul, ← heq]
        exact (abs_sub _ _).trans (by linarith [hx, hy])
      nlinarith
    have hU := grid_bins_of_pairwise_dist_le T (show 0 ≤ 2 * a by positivity) ha 0 hdiam
    change U.Finite ∧ (U.ncard : ℝ) ≤ 2 * (2 * a) / a + 2 at hU
    have hbound : 2 * (2 * a) / a + 2 = 6 := by field_simp; ring
    rw [hbound] at hU
    have hsub : {n : ℤ | binTest p κ a b n} ⊆ S ∪ U := by
      intro n hn
      by_cases hd' : d ≤ |p.derivative.eval ((n : ℝ) * a)|
      · exact Or.inl ⟨(n : ℝ) * a, ⟨hn.1, hd'⟩, hrep n⟩
      · exact Or.inr ⟨(n : ℝ) * a, le_of_not_ge hd', hrep n⟩
    refine ⟨(hS.1.union hU.1).subset hsub, ?_⟩
    have hn := (Set.ncard_le_ncard hsub (hS.1.union hU.1)).trans (Set.ncard_union_le S U)
    have hn' : ({n : ℤ | binTest p κ a b n}.ncard : ℝ) ≤ (S.ncard : ℝ) + U.ncard := by
      exact_mod_cast hn
    exact (hn'.trans (add_le_add hS.2 hU.2)).trans (by nlinarith)
  · have hsub : {n : ℤ | binTest p κ a b n} ⊆ S := by
      intro n hn
      have hd' : d ≤ |p.derivative.eval ((n : ℝ) * a)| := hn.2.resolve_right hhigh
      exact ⟨(n : ℝ) * a, ⟨hn.1, hd'⟩, hrep n⟩
    refine ⟨hS.1.subset hsub, ?_⟩
    have hn : ({n : ℤ | binTest p κ a b n}.ncard : ℝ) ≤ S.ncard := by
      exact_mod_cast Set.ncard_le_ncard hsub hS.1
    exact (hn.trans hS.2).trans (by nlinarith)

end Submission.Obl.k4_coarsened_outer_horizon_composition
