-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/FlatMajorant.lean;
-- only the namespace and module paths were renamed to o071's.
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.Parallelogram

/-!
# A trigonometric majorant for window probabilities

Paper Lemma 7.4 (`re:flat-coefficients`) bounds the mass of a window `[x - h, x + h]` by the
Fourier transform of the law on frequencies up to `h⁻¹`. We use the discrete majorant
`Q(y) = ∑_{j ≤ N} e^{2πijy}`: it has modulus at least `(N+1)/2` when `2πN|y| ≤ 1`, and
`|Q|² = ∑_{j,j'} e^{2πi(j-j')y}`. Hence, with `H = 2πNh`, the window mass is at most
`4/(N+1)² · ∑_{j,j' ≤ N} |χ((j-j')/H)|`, where `χ` is the characteristic function of the law.
Only finite sums appear.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open Complex

noncomputable section

variable {α : Type*} [Fintype α]

/-- The characteristic function `χ(ζ) = ∑ₐ w a e^{2πiζ val a}` of a finite law. -/
def chf (w : α → ℝ) (val : α → ℝ) (ζ : ℝ) : ℂ :=
  ∑ a, (w a : ℂ) * Complex.exp (((2 * Real.pi * ζ * val a : ℝ) : ℂ) * I)

/-- The trigonometric sum `Q(y) = ∑_{j ≤ N} e^{2πijy}`. -/
def trigQ (N : ℕ) (y : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), Complex.exp (((2 * Real.pi * j * y : ℝ) : ℂ) * I)

theorem half_le_cos_of_abs_le_one {θ : ℝ} (hθ : |θ| ≤ 1) : (1 : ℝ) / 2 ≤ Real.cos θ := by
  rw [← Real.cos_abs]
  have hpi := Real.pi_gt_three
  have h1 : Real.cos (Real.pi / 3) ≤ Real.cos |θ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith) (by linarith)
  rwa [Real.cos_pi_div_three] at h1

theorem trigQ_lower (N : ℕ) {y : ℝ} (hy : 2 * Real.pi * N * |y| ≤ 1) :
    ((N : ℝ) + 1) / 2 ≤ ‖trigQ N y‖ := by
  have hre : (trigQ N y).re = ∑ j ∈ Finset.range (N + 1), Real.cos (2 * Real.pi * j * y) := by
    rw [trigQ, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Complex.exp_ofReal_mul_I_re _
  have hcos : ∀ j ∈ Finset.range (N + 1), (1 : ℝ) / 2 ≤ Real.cos (2 * Real.pi * j * y) := by
    intro j hj
    apply half_le_cos_of_abs_le_one
    have hjN : (j : ℝ) ≤ N := by
      have := Finset.mem_range.mp hj
      exact_mod_cast Nat.lt_succ_iff.mp this
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos, Nat.abs_cast]
    calc 2 * Real.pi * (j : ℝ) * |y| ≤ 2 * Real.pi * N * |y| := by gcongr
      _ ≤ 1 := hy
  calc ((N : ℝ) + 1) / 2 = ∑ _j ∈ Finset.range (N + 1), (1 : ℝ) / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ∑ j ∈ Finset.range (N + 1), Real.cos (2 * Real.pi * j * y) := Finset.sum_le_sum hcos
    _ = (trigQ N y).re := hre.symm
    _ ≤ ‖trigQ N y‖ := Complex.re_le_norm _

theorem norm_trigQ_sq (N : ℕ) (y : ℝ) :
    ((‖trigQ N y‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
      Complex.exp (((2 * Real.pi * ((j : ℝ) - j') * y : ℝ) : ℂ) * I) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, trigQ, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **The trigonometric majorant**: the window mass is controlled by the characteristic function
at the frequencies `(j - j')/H`, `j, j' ≤ N`, where `H = 2πNh`. -/
theorem lawMass_window_le_chf {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (val : α → ℝ) {h : ℝ}
    (hh : 0 < h) (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    lawMass w val (Set.Icc (x - h) (x + h)) ≤ 4 / ((N : ℝ) + 1) ^ 2 *
      ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
        ‖chf w val (((j : ℝ) - j') / (2 * Real.pi * N * h))‖ := by
  classical
  set H := 2 * Real.pi * N * h with hH
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hHpos : 0 < H := by positivity
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- pointwise majorant of the window indicator
  have hpt : ∀ a, (if val a ∈ Set.Icc (x - h) (x + h) then (1 : ℝ) else 0) ≤
      4 / ((N : ℝ) + 1) ^ 2 * ‖trigQ N ((val a - x) / H)‖ ^ 2 := by
    intro a
    split_ifs with ha
    · have hd : |val a - x| ≤ h := by rw [abs_le]; constructor <;> linarith [ha.1, ha.2]
      have hy : 2 * Real.pi * N * |(val a - x) / H| ≤ 1 := by
        rw [abs_div, abs_of_pos hHpos, hH]
        rw [mul_div_assoc', div_le_one (by positivity)]
        calc 2 * Real.pi * N * |val a - x| ≤ 2 * Real.pi * N * h := by gcongr
          _ = 2 * Real.pi * N * h := rfl
      have hq := trigQ_lower N hy
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
      have : 0 ≤ ((N : ℝ) + 1) / 2 := by positivity
      nlinarith
    · positivity
  -- expand the squares
  have hexp : ∀ a, ((‖trigQ N ((val a - x) / H)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
        Complex.exp (((-(2 * Real.pi * (((j : ℝ) - j') / H) * x) : ℝ) : ℂ) * I) *
          Complex.exp (((2 * Real.pi * (((j : ℝ) - j') / H) * val a : ℝ) : ℂ) * I) := by
    intro a
    rw [norm_trigQ_sq]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  set r := ∑ a, w a * ‖trigQ N ((val a - x) / H)‖ ^ 2 with hr
  have hrC : (r : ℂ) = ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
      Complex.exp (((-(2 * Real.pi * (((j : ℝ) - j') / H) * x) : ℝ) : ℂ) * I) *
        chf w val (((j : ℝ) - j') / H) := by
    rw [hr, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_mul, hexp, Finset.mul_sum, chf]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hr_le : r ≤ ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
      ‖chf w val (((j : ℝ) - j') / H)‖ := by
    have hr0 : 0 ≤ r := Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (sq_nonneg _)
    calc r = ‖(r : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hr0]
      _ ≤ ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
          ‖Complex.exp (((-(2 * Real.pi * (((j : ℝ) - j') / H) * x) : ℝ) : ℂ) * I) *
            chf w val (((j : ℝ) - j') / H)‖ := by
          rw [hrC]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
      _ = ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
          ‖chf w val (((j : ℝ) - j') / H)‖ := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc lawMass w val (Set.Icc (x - h) (x + h))
      = ∑ a, w a * (if val a ∈ Set.Icc (x - h) (x + h) then (1 : ℝ) else 0) := rfl
    _ ≤ ∑ a, w a * (4 / ((N : ℝ) + 1) ^ 2 * ‖trigQ N ((val a - x) / H)‖ ^ 2) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hw a)
    _ = 4 / ((N : ℝ) + 1) ^ 2 * r := by
        rw [hr, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ ≤ 4 / ((N : ℝ) + 1) ^ 2 * ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
          ‖chf w val (((j : ℝ) - j') / H)‖ := by gcongr

end

end Submission.Obl.k4_retained_edge_planar_rigidity
