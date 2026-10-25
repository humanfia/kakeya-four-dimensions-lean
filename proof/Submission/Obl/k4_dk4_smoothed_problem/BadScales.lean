import Submission.Lib.KakeyaCovering.GraphReduction

/-! Cofinal finite counterconfigurations to the discrete Kakeya estimate. -/

open MeasureTheory Set

namespace Submission.Obl.k4_dk4_smoothed_problem

abbrev E4 := EuclideanSpace ℝ (Fin 4)

noncomputable def lineCountFloor (c : ℝ) (k : ℕ) : ℝ :=
  c * (2 : ℝ) ^ (3 * k) / ((k : ℝ) + 1) ^ 2

theorem lineCountFloor_pos {c : ℝ} (hc : 0 < c) (k : ℕ) :
    0 < lineCountFloor c k := by
  unfold lineCountFloor
  positivity

/-- A finite configuration witnessing failure at one dyadic scale. The upper bound
on the number of lines comes from retaining just the required number of them. -/
structure BadConfiguration (c R σ : ℝ) (k : ℕ) where
  n : ℕ
  n_pos : 0 < n
  x : Fin n → E4
  v : Fin n → E4
  count_lower : lineCountFloor c k ≤ (n : ℝ)
  count_upper : (n : ℝ) ≤ (c + 1) * (2 : ℝ) ^ (3 * k)
  coordinates : ∀ i, x i 0 = 0 ∧ v i 0 = 1 ∧ ‖v i‖ ≤ 2
  separated : ∀ i j, i ≠ j → (2 : ℝ) ^ (-(k : ℤ)) ≤ ‖v i - v j‖
  bounded : ∀ i, ‖x i‖ ≤ R
  m : ℕ
  z : Fin m → E4
  ρ : Fin m → ℝ
  cover_count : (m : ℝ) ≤ (2 : ℝ) ^ (((k : ℝ) + 1) * (4 - σ))
  radii : ∀ j, (2 : ℝ) ^ (-((k : ℤ) + 1)) < ρ j ∧ ρ j ≤ (2 : ℝ) ^ (-(k : ℤ))
  time_mass : ∀ i, ENNReal.ofReal (c / ((k : ℝ) + 1) ^ 2) ≤
    volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      x i + t • v i ∈ ⋃ j, Metric.ball (z j) (ρ j)}

theorem exists_bad_configuration
    (h : ¬ Submission.Lib.KakeyaCovering.DiscreteKakeyaEstimate) :
    ∃ σ c R : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < c ∧ 1 ≤ R ∧
      ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧ Nonempty (BadConfiguration c R σ k) := by
  classical
  unfold Submission.Lib.KakeyaCovering.DiscreteKakeyaEstimate at h
  push Not at h
  obtain ⟨σ, hσ, hσ1, c, hc, R, hR, h⟩ := h
  refine ⟨σ, c, R, hσ, hσ1, hc, hR, ?_⟩
  intro k₀
  obtain ⟨k, hk, n, x, v, hn, hcoords, hsep, hx, m, z, ρ, hm, hρ, htime⟩ := h k₀
  let n' : ℕ := ⌈lineCountFloor c k⌉₊
  have hn' : n' ≤ n := Nat.ceil_le.mpr hn
  have hcount : lineCountFloor c k ≤ (n' : ℝ) := Nat.le_ceil _
  have hpos : 0 < n' := by
    have := (lineCountFloor_pos hc k).trans_le hcount
    exact_mod_cast this
  have hden : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]
  have hbound : lineCountFloor c k ≤ c * (2 : ℝ) ^ (3 * k) := by
    exact div_le_self (by positivity) hden
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (3 * k) := one_le_pow₀ (by norm_num)
  have hupper : (n' : ℝ) ≤ (c + 1) * (2 : ℝ) ^ (3 * k) := by
    have hceil := Nat.ceil_lt_add_one (lineCountFloor_pos hc k).le
    dsimp [n']
    nlinarith
  refine ⟨k, hk, ⟨{
    n := n'
    n_pos := hpos
    x := fun i => x (Fin.castLE hn' i)
    v := fun i => v (Fin.castLE hn' i)
    count_lower := hcount
    count_upper := hupper
    coordinates := fun i => hcoords _
    separated := ?_
    bounded := fun i => hx _
    m := m
    z := z
    ρ := ρ
    cover_count := hm
    radii := hρ
    time_mass := fun i => htime _ }⟩⟩
  intro i j hij
  apply hsep
  intro heq
  apply hij
  exact Fin.ext (congrArg (fun a : Fin n => a.val) heq)

/-- A cofinal family can be chosen on a sequence tending to infinity. No
monotonicity of the chosen scales is needed by the smoothing conclusion. -/
theorem exists_bad_sequence
    (h : ¬ Submission.Lib.KakeyaCovering.DiscreteKakeyaEstimate) (a : ℕ) :
    ∃ σ c R : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < c ∧ 1 ≤ R ∧
      ∃ κ : ℕ → ℕ, (∀ j, a ≤ κ j ∧ j ≤ κ j) ∧
        ∀ j, Nonempty (BadConfiguration c R σ (κ j)) := by
  classical
  obtain ⟨σ, c, R, hσ, hσ1, hc, hR, hbad⟩ := exists_bad_configuration h
  choose κ hκ hconfig using fun j => hbad (max a j)
  exact ⟨σ, c, R, hσ, hσ1, hc, hR, κ,
    (fun j => ⟨(le_max_left a j).trans (hκ j), (le_max_right a j).trans (hκ j)⟩),
    hconfig⟩

end Submission.Obl.k4_dk4_smoothed_problem
