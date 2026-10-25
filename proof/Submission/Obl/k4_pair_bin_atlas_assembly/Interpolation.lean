import Submission.Obl.k4_pair_bin_atlas_assembly.Rescale

-- The use of three-point control along trajectories follows the plan of this LOT tree, o158,
-- session x0532, branch x0532,
-- Submission/Obl/k4_matched_pair_representative_realization/Interpolation.lean (statements only).

/-!
# Three-node control of quadratic functions of time

A test of total degree at most two is a quadratic function of time along a trajectory.
Three values at equally spaced nodes control a quadratic everywhere (Lagrange interpolation).
We use this twice:

* the value of a quadratic at the three block nodes (both endpoints and the midpoint) bounds it
  on the whole block, with a factor `8`;
* a bound on a short subinterval (of relative length `η`) of a block around a point of the
  block bounds the quadratic on the whole block, with a factor `32 (length / η) ^ 2`.
-/

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Submission.Obl.k4_quadratic_atlas_normalization MvPolynomial
open Submission.Obl.k4_eligibility_sign_description (Quadratic)

/-- Evaluation of a test of degree at most two along a trajectory is quadratic in time. -/
theorem quadratic_eval_x (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) (l : Traj) :
    Quadratic (fun t => eval (x l t) R) := by
  have h := Submission.Obl.k4_eligibility_sign_description.Quadratic.mv_line R hR
    ![0, l.2 0, l.2 1, l.2 2] ![1, l.2 3, l.2 4, l.2 5]
  have hx : ∀ t, x l t = fun i => (![0, l.2 0, l.2 1, l.2 2] : Fin 4 → ℝ) i +
      t * (![1, l.2 3, l.2 4, l.2 5] : Fin 4 → ℝ) i := by
    intro t
    funext i
    fin_cases i <;> simp [x]
  simpa only [hx] using h

/-- Lagrange identity for three equally spaced nodes. -/
theorem quadratic_lagrange {f : ℝ → ℝ} (hf : Quadratic f) (s h t : ℝ) :
    2 * h ^ 2 * f t = f s * ((t - (s + h)) * (t - (s + 2 * h))) -
      2 * f (s + h) * ((t - s) * (t - (s + 2 * h))) +
        f (s + 2 * h) * ((t - s) * (t - (s + h))) := by
  obtain ⟨A, B, C, hf⟩ := hf
  simp only [hf]
  ring

/-- Three equally spaced values control a quadratic at every point within `ρ` of the nodes. -/
theorem quadratic_three_node_bound {f : ℝ → ℝ} (hf : Quadratic f) {s h t X ρ : ℝ}
    (hh : h ≠ 0) (h0 : |f s| ≤ X) (h1 : |f (s + h)| ≤ X) (h2 : |f (s + 2 * h)| ≤ X)
    (r0 : |t - s| ≤ ρ) (r1 : |t - (s + h)| ≤ ρ) (r2 : |t - (s + 2 * h)| ≤ ρ) :
    |f t| ≤ 2 * X * ρ ^ 2 / h ^ 2 := by
  have hX : 0 ≤ X := (abs_nonneg _).trans h0
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans r0
  have hh2 : 0 < h ^ 2 := by positivity
  rw [le_div_iff₀ hh2]
  have key := quadratic_lagrange hf s h t
  have e0 : |f s * ((t - (s + h)) * (t - (s + 2 * h)))| ≤ X * (ρ * ρ) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul h0 (mul_le_mul r1 r2 (abs_nonneg _) hρ) (by positivity) hX
  have e1 : |2 * f (s + h) * ((t - s) * (t - (s + 2 * h)))| ≤ 2 * X * (ρ * ρ) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    have := mul_le_mul h1 (mul_le_mul r0 r2 (abs_nonneg _) hρ) (by positivity) hX
    nlinarith
  have e2 : |f (s + 2 * h) * ((t - s) * (t - (s + h)))| ≤ X * (ρ * ρ) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul h2 (mul_le_mul r0 r1 (abs_nonneg _) hρ) (by positivity) hX
  have htot : |2 * h ^ 2 * f t| ≤ 4 * X * ρ ^ 2 := by
    rw [key]
    calc _ ≤ |f s * ((t - (s + h)) * (t - (s + 2 * h))) -
            2 * f (s + h) * ((t - s) * (t - (s + 2 * h)))| +
          |f (s + 2 * h) * ((t - s) * (t - (s + h)))| := abs_add_le _ _
      _ ≤ (|f s * ((t - (s + h)) * (t - (s + 2 * h)))| +
            |2 * f (s + h) * ((t - s) * (t - (s + 2 * h)))|) +
          |f (s + 2 * h) * ((t - s) * (t - (s + h)))| := by gcongr; exact abs_sub _ _
      _ ≤ X * (ρ * ρ) + 2 * X * (ρ * ρ) + X * (ρ * ρ) := by gcongr
      _ = 4 * X * ρ ^ 2 := by ring
  rw [abs_mul, abs_mul, abs_two, abs_of_pos hh2] at htot
  nlinarith

/-- The three nodes of a block: both endpoints and the midpoint. -/
noncomputable def node (T : ℕ) (jr : ℝ) (i : Fin 3) : ℝ := (jr + (i : ℝ) / 2) / (2 : ℝ) ^ T

theorem node_mem_tblock (T : ℕ) (jr : ℝ) (i : Fin 3) : node T jr i ∈ tblock T jr := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hi : (i : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  have hi0 : (0 : ℝ) ≤ i := by positivity
  constructor
  · apply div_le_div_of_nonneg_right _ hq.le; linarith
  · apply div_le_div_of_nonneg_right _ hq.le; linarith

/-- Values at the three block nodes bound a quadratic on the whole block. -/
theorem tblock_bound_of_nodes {f : ℝ → ℝ} (hf : Quadratic f) {T : ℕ} {jr X : ℝ}
    (hn : ∀ i : Fin 3, |f (node T jr i)| ≤ X) : ∀ t ∈ tblock T jr, |f t| ≤ 8 * X := by
  intro t ht
  have hq : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  set h : ℝ := 1 / (2 * (2 : ℝ) ^ T) with hh
  have hpos : 0 < h := by positivity
  have hs0 : node T jr 0 = jr / (2 : ℝ) ^ T := by simp [node]
  have hs1 : node T jr 1 = jr / (2 : ℝ) ^ T + h := by
    rw [hh, node]; norm_num; field_simp
  have hs2 : node T jr 2 = jr / (2 : ℝ) ^ T + 2 * h := by
    rw [hh, node]; norm_num; field_simp
  have hb := quadratic_three_node_bound (s := jr / (2 : ℝ) ^ T) (h := h) (t := t) (X := X)
    (ρ := 2 * h) hf hpos.ne' (by rw [← hs0]; exact hn 0) (by rw [← hs1]; exact hn 1)
    (by rw [← hs2]; exact hn 2)
  obtain ⟨ht1, ht2⟩ := ht
  have hlen : (jr + 1) / (2 : ℝ) ^ T = jr / (2 : ℝ) ^ T + 2 * h := by
    rw [hh]; field_simp
  rw [hlen] at ht2
  have := hb (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
  calc |f t| ≤ 2 * X * (2 * h) ^ 2 / h ^ 2 := this
    _ = 8 * X := by field_simp; ring

/-- A bound on all points of a closed interval within `η` of one of its points bounds a
quadratic on the whole interval, if the interval has length at least `2 η`. -/
theorem interval_bound_of_short {f : ℝ → ℝ} (hf : Quadratic f) {lo hi t₀ η X : ℝ}
    (ht₀ : t₀ ∈ Set.Icc lo hi) (hη : 0 < η) (hη2 : 2 * η ≤ hi - lo)
    (hshort : ∀ t ∈ Set.Icc lo hi, |t - t₀| ≤ η → |f t| ≤ X) :
    ∀ t ∈ Set.Icc lo hi, |f t| ≤ 32 * X * ((hi - lo) / η) ^ 2 := by
  intro t ht
  obtain ⟨h0l, h0h⟩ := ht₀
  obtain ⟨htl, hth⟩ := ht
  have hlen : 0 < hi - lo := by linarith
  -- choose the side of `t₀` with room `η`
  obtain ⟨e, he, hroom⟩ : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ lo ≤ t₀ + e * η ∧ t₀ + e * η ≤ hi := by
    by_cases hr : t₀ + η ≤ hi
    · exact ⟨1, Or.inl rfl, by linarith, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith, by linarith⟩
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have habs_e : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  set h : ℝ := e * η / 2 with hhdef
  have hh0 : h ≠ 0 := by
    rw [hhdef]; rcases he with rfl | rfl <;> simp [hη.ne']
  have hX : ∀ k : ℝ, 0 ≤ k → k ≤ 1 → |f (t₀ + k * (e * η))| ≤ X := by
    intro k hk0 hk1
    apply hshort
    · constructor
      · rcases he with rfl | rfl <;> nlinarith
      · rcases he with rfl | rfl <;> nlinarith
    · rw [add_sub_cancel_left, abs_mul, abs_mul, habs_e, abs_of_pos hη, abs_of_nonneg hk0]
      nlinarith
  have hn0 : |f t₀| ≤ X := by simpa using hX 0 le_rfl zero_le_one
  have hn1 : |f (t₀ + h)| ≤ X := by
    have := hX (1 / 2) (by norm_num) (by norm_num)
    rw [hhdef]; convert this using 3; ring
  have hn2 : |f (t₀ + 2 * h)| ≤ X := by
    have := hX 1 zero_le_one le_rfl
    rw [hhdef]; convert this using 3; ring
  set ρ : ℝ := (hi - lo) + η with hρ
  have hdist : ∀ k : ℝ, 0 ≤ k → k ≤ 1 → |t - (t₀ + k * (e * η))| ≤ ρ := by
    intro k hk0 hk1
    have h1 : |t - t₀| ≤ hi - lo := by rw [abs_le]; constructor <;> linarith
    have h2 : |k * (e * η)| ≤ η := by
      rw [abs_mul, abs_mul, habs_e, abs_of_pos hη, abs_of_nonneg hk0]; nlinarith
    calc |t - (t₀ + k * (e * η))| = |(t - t₀) - k * (e * η)| := by ring_nf
      _ ≤ |t - t₀| + |k * (e * η)| := abs_sub _ _
      _ ≤ ρ := by rw [hρ]; linarith
  have hb := quadratic_three_node_bound hf hh0 hn0 hn1 hn2 (t := t) (ρ := ρ)
    (by simpa using hdist 0 le_rfl zero_le_one)
    (by have := hdist (1 / 2) (by norm_num) (by norm_num); rw [hhdef]; convert this using 3; ring)
    (by have := hdist 1 zero_le_one le_rfl; rw [hhdef]; convert this using 3; ring)
  have hXn : 0 ≤ X := (abs_nonneg _).trans hn0
  have hh2 : h ^ 2 = η ^ 2 / 4 := by rw [hhdef, div_pow, mul_pow, he2]; ring
  have hρle : ρ ≤ 2 * (hi - lo) := by rw [hρ]; linarith
  calc |f t| ≤ 2 * X * ρ ^ 2 / h ^ 2 := hb
    _ = 8 * X * ρ ^ 2 / η ^ 2 := by rw [hh2]; field_simp; ring
    _ ≤ 8 * X * (2 * (hi - lo)) ^ 2 / η ^ 2 := by
        gcongr
    _ = 32 * X * ((hi - lo) / η) ^ 2 := by field_simp; ring

end Submission.Obl.k4_pair_bin_atlas_assembly
