import Mathlib

/-!
# Entropy bounds for the palette likelihood (helper for o038)

For a probability vector `p` on `Fin n`, a record `f : Fin n → ℕ` and a palette `Z : Fin n → ℕ`,
the conditional likelihood of the palette of `x` given its record is written out, as in the frozen
statement of o038, as the ratio of finite sums
`q x = (∑ y ∈ univ.filter (fun y => f y = f x ∧ Z y = Z x), p y) /
  (∑ y ∈ univ.filter (fun y => f y = f x), p y)`.

* `sum_fiber_div_joint_le`: grouping a record fiber by palette values; with a palette weight `Φ`,
  `∑_{x : f x = f y} p x * Φ (Z x) / P(f = f x, Z = Z x) ≤ ∑_{z} Φ z` over the positive-mass
  palette values `z` of the fiber.
* `sum_div_likelihood_le`: `∑ x, p x / q x ≤ M` when every fiber has at most `M` positive-mass
  palette values.
* `log_likelihood_nonpos`: `∑ x, p x * log (q x) ≤ 0` (conditional entropy is nonnegative).
* `neg_log_card_le_log_likelihood`: `-log M ≤ ∑ x, p x * log (q x)` (conditional entropy is at most
  `log M`), by Gibbs' inequality `log t ≤ t - 1` with `t = 1 / (M * q x)`.
-/

namespace Submission.Obl.k4_matching_palette_likelihood

open Finset

/-- The joint mass of the record and palette value of a point of positive mass is positive. -/
theorem joint_mass_pos {n : ℕ} (p : Fin n → ℝ) (f Z : Fin n → ℕ) (hp : ∀ x, 0 ≤ p x)
    {x : Fin n} (hx : 0 < p x) :
    0 < ∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y :=
  lt_of_lt_of_le hx (Finset.single_le_sum (f := p) (fun i _ => hp i) (by simp))

/-- The mass of the record fiber of a point of positive mass is positive. -/
theorem fiber_mass_pos {n : ℕ} (p : Fin n → ℝ) (f : Fin n → ℕ) (hp : ∀ x, 0 ≤ p x)
    {x : Fin n} (hx : 0 < p x) :
    0 < ∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y :=
  lt_of_lt_of_le hx (Finset.single_le_sum (f := p) (fun i _ => hp i) (by simp))

/-- The joint mass is at most the fiber mass. -/
theorem joint_mass_le_fiber_mass {n : ℕ} (p : Fin n → ℝ) (f Z : Fin n → ℕ)
    (hp : ∀ x, 0 ≤ p x) (x : Fin n) :
    ∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y ≤
      ∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact hy.1
  · intro i _ _
    exact hp i

/-- The likelihood is nonnegative. -/
theorem likelihood_nonneg {n : ℕ} (p : Fin n → ℝ) (f Z : Fin n → ℕ) (hp : ∀ x, 0 ≤ p x)
    (x : Fin n) :
    0 ≤ (∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y) /
      (∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y) :=
  div_nonneg (Finset.sum_nonneg (fun i _ => hp i)) (Finset.sum_nonneg (fun i _ => hp i))

/-- The likelihood is at most one. -/
theorem likelihood_le_one {n : ℕ} (p : Fin n → ℝ) (f Z : Fin n → ℕ) (hp : ∀ x, 0 ≤ p x)
    (x : Fin n) :
    (∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y) /
      (∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y) ≤ 1 :=
  div_le_one_of_le₀ (joint_mass_le_fiber_mass p f Z hp x) (Finset.sum_nonneg (fun i _ => hp i))

/-- The likelihood of a point of positive mass is positive. -/
theorem likelihood_pos {n : ℕ} (p : Fin n → ℝ) (f Z : Fin n → ℕ) (hp : ∀ x, 0 ≤ p x)
    {x : Fin n} (hx : 0 < p x) :
    0 < (∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y) /
      (∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y) :=
  div_pos (joint_mass_pos p f Z hp hx) (fiber_mass_pos p f hp hx)

/-- Grouping the record fiber of `y` by palette values: with a nonnegative palette weight `Φ`,
`∑_{x : f x = f y} p x * Φ (Z x) / P(f = f x, Z = Z x)` is at most the sum of `Φ` over the
palette values of positive mass in the fiber. -/
theorem sum_fiber_div_joint_le {n : ℕ} (p : Fin n → ℝ) (f Z : Fin n → ℕ)
    (hp : ∀ x, 0 ≤ p x) (y : Fin n) (Φ : ℕ → ℝ) (hΦ : ∀ z, 0 ≤ Φ z) :
    ∑ x ∈ univ.filter (fun x : Fin n => f x = f y),
        p x * Φ (Z x) / (∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f x ∧ Z x' = Z x), p x') ≤
      ∑ z ∈ (univ.filter (fun x : Fin n => 0 < p x ∧ f x = f y)).image Z, Φ z := by
  classical
  -- drop the points of zero mass
  have h1 : ∑ x ∈ univ.filter (fun x : Fin n => 0 < p x ∧ f x = f y),
        p x * Φ (Z x) / (∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f x ∧ Z x' = Z x), p x') =
      ∑ x ∈ univ.filter (fun x : Fin n => f x = f y),
        p x * Φ (Z x) / (∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f x ∧ Z x' = Z x), p x') := by
    apply Finset.sum_subset
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.2
    · intro x hx hxS
      simp only [mem_filter, mem_univ, true_and, not_and] at hx hxS
      have h0 : p x = 0 := by
        rcases (hp x).lt_or_eq with h | h
        · exact absurd hx (hxS h)
        · exact h.symm
      simp [h0]
  rw [← h1]
  -- group by palette values
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := univ.filter (fun x : Fin n => 0 < p x ∧ f x = f y))
    (t := (univ.filter (fun x : Fin n => 0 < p x ∧ f x = f y)).image Z) (g := Z)
    (fun x hx => mem_image_of_mem Z hx)]
  apply Finset.sum_le_sum
  intro z hz
  have hm_pos : 0 < ∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f y ∧ Z x' = z), p x' := by
    obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hz
    simp only [mem_filter, mem_univ, true_and] at hx₀
    have := joint_mass_pos p f Z hp hx₀.1
    rwa [hx₀.2] at this
  have h2 : ∀ x ∈ (univ.filter (fun x : Fin n => 0 < p x ∧ f x = f y)).filter (fun x => Z x = z),
      p x * Φ (Z x) / (∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f x ∧ Z x' = Z x), p x') =
        p x * (Φ z / ∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f y ∧ Z x' = z), p x') := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [hx.2, hx.1.2]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]
  have h3 : ∑ x ∈ (univ.filter (fun x : Fin n => 0 < p x ∧ f x = f y)).filter (fun x => Z x = z),
      p x ≤ ∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f y ∧ Z x' = z), p x' := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact ⟨hx.1.2, hx.2⟩
    · intro i _ _
      exact hp i
  calc (∑ x ∈ (univ.filter (fun x : Fin n => 0 < p x ∧ f x = f y)).filter (fun x => Z x = z),
          p x) * (Φ z / ∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f y ∧ Z x' = z), p x')
        ≤ (∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f y ∧ Z x' = z), p x') *
          (Φ z / ∑ x' ∈ univ.filter (fun x' : Fin n => f x' = f y ∧ Z x' = z), p x') :=
        mul_le_mul_of_nonneg_right h3 (div_nonneg (hΦ z) hm_pos.le)
    _ = Φ z := by field_simp

/-- `∑ x, p x / q x ≤ M` when every record fiber has at most `M` palette values of positive
mass (`q` the likelihood of the palette given the record). -/
theorem sum_div_likelihood_le {n M : ℕ} (p : Fin n → ℝ) (f Z : Fin n → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (hcard : ∀ x, ((univ.filter (fun y : Fin n => 0 < p y ∧ f y = f x)).image Z).card ≤ M) :
    ∑ x, p x / ((∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y) /
        (∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y)) ≤ M := by
  classical
  have h1 : ∀ x, p x / ((∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y) /
        (∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y)) =
      ∑ y ∈ univ.filter (fun y : Fin n => f y = f x),
        p y * (p x * 1 / (∑ y' ∈ univ.filter (fun y' : Fin n => f y' = f x ∧ Z y' = Z x), p y')) := by
    intro x
    rw [div_div_eq_mul_div, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [Finset.sum_congr rfl (fun x _ => h1 x)]
  rw [Finset.sum_comm' (t' := univ) (s' := fun y => univ.filter (fun x : Fin n => f x = f y))
    (fun x y => by simp [eq_comm])]
  calc ∑ y, ∑ x ∈ univ.filter (fun x : Fin n => f x = f y),
        p y * (p x * 1 / (∑ y' ∈ univ.filter (fun y' : Fin n => f y' = f x ∧ Z y' = Z x), p y'))
      = ∑ y, p y * ∑ x ∈ univ.filter (fun x : Fin n => f x = f y),
          p x * 1 / (∑ y' ∈ univ.filter (fun y' : Fin n => f y' = f x ∧ Z y' = Z x), p y') := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
    _ ≤ ∑ y, p y * (M : ℝ) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ (hp y)
        have := sum_fiber_div_joint_le p f Z hp y (fun _ => 1) (fun _ => zero_le_one)
        simp only [sum_const, nsmul_eq_mul, mul_one] at this
        refine le_trans (by simpa using this) ?_
        exact_mod_cast hcard y
    _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Conditional entropy is nonnegative: `∑ x, p x * log (q x) ≤ 0`. -/
theorem log_likelihood_nonpos {n : ℕ} (p : Fin n → ℝ) (f Z : Fin n → ℕ) (hp : ∀ x, 0 ≤ p x) :
    ∑ x, p x * Real.log ((∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y) /
        (∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y)) ≤ 0 :=
  Finset.sum_nonpos (fun x _ => mul_nonpos_of_nonneg_of_nonpos (hp x)
    (Real.log_nonpos (likelihood_nonneg p f Z hp x) (likelihood_le_one p f Z hp x)))

/-- Conditional entropy is at most `log M` when every record fiber has at most `M` palette values
of positive mass: `-log M ≤ ∑ x, p x * log (q x)`. -/
theorem neg_log_card_le_log_likelihood {n M : ℕ} (p : Fin n → ℝ) (f Z : Fin n → ℕ) (hM : 1 ≤ M)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (hcard : ∀ x, ((univ.filter (fun y : Fin n => 0 < p y ∧ f y = f x)).image Z).card ≤ M) :
    -Real.log M ≤ ∑ x, p x * Real.log ((∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x),
        p y) / (∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y)) := by
  classical
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hdiv := sum_div_likelihood_le p f Z hp hsum hcard
  generalize hq : (fun x => (∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y) /
      (∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y)) = q at hdiv
  have hq' : ∀ x, (∑ y ∈ univ.filter (fun y : Fin n => f y = f x ∧ Z y = Z x), p y) /
      (∑ y ∈ univ.filter (fun y : Fin n => f y = f x), p y) = q x := fun x => by rw [← hq]
  simp only [hq']
  simp only [hq'] at hdiv
  have hpt : ∀ x, -(p x * Real.log M) + p x - p x / q x / M ≤ p x * Real.log (q x) := by
    intro x
    rcases (hp x).lt_or_eq with hx | hx
    · have hqpos : 0 < q x := by rw [← hq']; exact likelihood_pos p f Z hp hx
      have key := Real.log_le_sub_one_of_pos (show 0 < 1 / (M * q x) by positivity)
      rw [one_div, Real.log_inv, Real.log_mul hMpos.ne' hqpos.ne'] at key
      have h2 := mul_le_mul_of_nonneg_left key (hp x)
      have e : p x * ((M * q x)⁻¹ - 1) = p x / q x / M - p x := by
        field_simp
      rw [e] at h2
      linarith
    · rw [← hx]; simp
  have hS : ∑ x, (-(p x * Real.log M) + p x - p x / q x / M) =
      -Real.log M + 1 - (∑ x, p x / q x) / M := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul,
      ← Finset.sum_div, hsum]
    ring
  have hdiv' : (∑ x, p x / q x) / M ≤ 1 := by
    rw [div_le_one hMpos]; exact hdiv
  calc -Real.log M ≤ -Real.log M + 1 - (∑ x, p x / q x) / M := by linarith
    _ = ∑ x, (-(p x * Real.log M) + p x - p x / q x / M) := hS.symm
    _ ≤ ∑ x, p x * Real.log (q x) := Finset.sum_le_sum (fun x _ => hpt x)

end Submission.Obl.k4_matching_palette_likelihood
