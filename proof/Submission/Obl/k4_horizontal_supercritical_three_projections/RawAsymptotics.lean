import Submission.Obl.k4_horizontal_supercritical_three_projections.Model
import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartScalar

/-!
# Asymptotic bookkeeping for the raw chart estimates

Fixed constants and powers of the subpower parameter `K` lose against any
fixed positive power of `N`; the true blocks of one depth, at one index,
satisfy the single-index hypotheses `BlockHyp` used by the support count.
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Filter Parent
open scoped ENNReal

noncomputable section

namespace HorizontalModel

variable {α : Type} [MeasurableSpace α] {m : HorizontalModel α}

theorem Valid.N_pos (h : m.Valid) (k : ℕ) : 0 < m.N k := by linarith [h.N_ge k]

theorem Valid.N_one_le (h : m.Valid) (k : ℕ) : 1 ≤ m.N k := by linarith [h.N_ge k]

/-- Any fixed constant times a fixed power of `K` is eventually below any fixed
positive power of `N`. -/
theorem Valid.eventually_const_mul_K_pow_le (h : m.Valid) {x : ℝ} (hx : 0 < x)
    (C : ℝ) (p : ℕ) : ∀ᶠ k in atTop, C * m.K k ^ p ≤ m.N k ^ x := by
  have hε : 0 < x / (2 * ((p : ℝ) + 1)) := by positivity
  have hNlarge : ∀ᶠ k in atTop, max C 1 ≤ m.N k ^ (x / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < x / 2)).comp h.N_tendsto).eventually_ge_atTop _
  filter_upwards [h.K_subpower _ hε, hNlarge] with k hK hN
  have hN1 := h.N_one_le k
  have hK1 := h.K_ge k
  have hpow : m.K k ^ p ≤ m.N k ^ (x / 2) := by
    calc m.K k ^ p ≤ (m.N k ^ (x / (2 * ((p : ℝ) + 1)))) ^ p :=
          pow_le_pow_left₀ (by linarith) hK p
      _ = m.N k ^ (x / (2 * ((p : ℝ) + 1)) * p) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      _ ≤ m.N k ^ (x / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  calc C * m.K k ^ p ≤ max C 1 * m.K k ^ p :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ m.N k ^ (x / 2) * m.N k ^ (x / 2) :=
        mul_le_mul hN hpow (by positivity) (by positivity)
    _ = m.N k ^ x := by rw [← Real.rpow_add (by linarith)]; ring_nf

/-- A comparison of two powers of `N` with a constant and a power of `K` loss. -/
theorem Valid.eventually_pow_le (h : m.Valid) {x y : ℝ} (hxy : y < x) (C : ℝ) (p : ℕ) :
    ∀ᶠ k in atTop, C * m.K k ^ p * m.N k ^ (-x) ≤ m.N k ^ (-y) := by
  filter_upwards [h.eventually_const_mul_K_pow_le (sub_pos.mpr hxy) C p] with k hk
  have hN := h.N_pos k
  calc C * m.K k ^ p * m.N k ^ (-x) ≤ m.N k ^ (x - y) * m.N k ^ (-x) :=
        mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hN.le _)
    _ = m.N k ^ (-y) := by rw [← Real.rpow_add hN]; ring_nf

theorem x_one (k : ℕ) (l : α) (t : ℝ) : m.x k l t 1 = m.b k l 0 + t * m.b k l 3 := rfl
theorem x_two (k : ℕ) (l : α) (t : ℝ) : m.x k l t 2 = m.b k l 1 + t * m.b k l 4 := rfl
theorem x_three (k : ℕ) (l : α) (t : ℝ) : m.x k l t 3 = m.b k l 2 + t * m.b k l 5 := rfl

theorem eval_affine_test (L : Fin 4 → ℝ) (w : Fin 4 → ℝ) :
    MvPolynomial.eval w (MvPolynomial.X (3 : Fin 4) -
      (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) +
        MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
        MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4))) =
      w 3 - affineValue L (w 0) (w 1) (w 2) := by
  simp [affineValue]

/-- The true blocks of one depth at one index satisfy `BlockHyp`. -/
theorem AtDepth.blockHyp {k : ℕ} {s R : ℝ} (hA : m.AtDepth k s R) :
    ∃ L : Fin (m.n k s) → Fin 4 → ℝ,
      BlockHyp (m.ν k) (m.μ k) (m.b k) (m.K k) (m.N k ^ (-s))
        ((2 : ℝ) ^ (-(m.T k s : ℤ))) (m.N k ^ (-m.κ * s)) m.d (m.T k s) (m.n k s)
        (m.j k s) (m.A k s) (m.B k s) (m.c k s) L := by
  obtain ⟨-, -, hmeas, hdisj, hblk, -, -⟩ := hA
  have hL : ∀ i, ∃ L : Fin 4 → ℝ,
      m.F k s i = MvPolynomial.X (3 : Fin 4) -
        (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) +
          MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
          MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧
      |L 3| ≤ m.K k * (1 + m.N k ^ (-s) / ((2 : ℝ) ^ (-(m.T k s : ℤ))) ^ 2) ∧
      ∀ l ∈ m.B k s i, ∀ t ∈ I (m.T k s) (m.j k s i),
        |L 1 - (m.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤
          m.K k * (1 + m.N k ^ (-s) / (2 : ℝ) ^ (-(m.T k s : ℤ))) :=
    fun i => ((hblk i).2.2.2.2.2.2.2.2 rfl).2.2.2
  choose L hLF hL3 hLs using hL
  refine ⟨L, ⟨rfl, hmeas, hdisj, fun i => (hblk i).1, fun i => (hblk i).2.2.1,
    fun i => (hblk i).2.2.2.1, ?_, ?_, ?_, hL3, ?_⟩⟩
  · intro i l hl t ht
    exact ⟨(hblk i).2.2.2.2.2.1 l hl t ht |>.1, (hblk i).2.2.2.2.2.1 l hl t ht |>.2.1⟩
  · intro i l hl t ht
    have h := ((hblk i).2.2.2.2.2.2.1 l hl t ht).1
    rw [hLF i, eval_affine_test] at h
    exact h
  · intro i
    exact ((hblk i).2.2.2.2.2.2.2.2 rfl).2.2.1
  · intro i l hl t ht
    exact hLs i l hl t ht

end HorizontalModel

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
