-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.JetAlgebra, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/JetAlgebra.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/JetAlgebra.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/JetAlgebra.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic

set_option autoImplicit false

/-!
# Jets of a quadratic signal against a row sequence, version 2

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `b03d2c4a`,
`Jets/JetAlgebra.lean`, with rows in `(ℝ²)^*` acting by dot products.

For a row sequence `R : ℕ → Fin 2 → ℝ` (the values `F_0 = F(t), F_1, …, F_m` at one time `t`),
the jets are `J_j = x^{(j)}(t) - R_j · y(t) - j R_{j-1} · y'` (`jet`).  Exact identities:
* `zS_sub_eq`: `S(s) - S(t) = (s - t) J_1(t) + (s - t)² (c₂ - R₁ · y') - e · y(s)` with
  `e = F(s) - F(t) - (s - t) R₁` (paper `a04:scalar-first-expansion`);
* `jet_sub_eq`: for `j ≥ 1`, the jet difference (paper `a04:jet-difference`);
* `zS_eq_taylor`: the final expansion `a04:final-jet-expansion`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Finset

noncomputable section

/-- The derivatives `x^{(j)}(t)` of the quadratic `x`. -/
def xder (c : Fin 7 → ℝ) (t : ℝ) : ℕ → ℝ
  | 0 => zx c t
  | 1 => c 1 + 2 * c 2 * t
  | 2 => 2 * c 2
  | _ => 0

/-- The jet `J_j = x^{(j)}(t) - R_j · y(t) - j R_{j-1} · y'`. -/
def jet (R : ℕ → Fin 2 → ℝ) (c : Fin 7 → ℝ) (t : ℝ) (j : ℕ) : ℝ :=
  xder c t j - R j ⬝ᵥ zy c t - (j : ℝ) * (R (j - 1) ⬝ᵥ zv c)

theorem jet_zero {F : ℝ → Fin 2 → ℝ} {R : ℕ → Fin 2 → ℝ} {c : Fin 7 → ℝ} {t : ℝ}
    (hR : R 0 = F t) : jet R c t 0 = zS F c t := by
  simp [jet, xder, zS, hR]

theorem xder_succ_sub {c : Fin 7 → ℝ} {s t : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    xder c s j - xder c t j = (s - t) * xder c t (j + 1) := by
  match j, hj with
  | 1, _ => simp [xder]; ring
  | 2, _ => simp [xder]
  | (n + 3), _ => simp [xder]

/-- `a04:scalar-first-expansion` (exact form). -/
theorem zS_sub_eq {F : ℝ → Fin 2 → ℝ} {R : ℕ → Fin 2 → ℝ} {c : Fin 7 → ℝ} {s t : ℝ}
    (hR : R 0 = F t) :
    zS F c s - zS F c t = (s - t) * jet R c t 1 + (s - t) ^ 2 * (c 2 - R 1 ⬝ᵥ zv c) -
      (F s - F t - (s - t) • R 1) ⬝ᵥ zy c s := by
  have hy := zy_add c s t
  simp only [zS, jet, xder, hR, zx]
  rw [hy]
  simp only [dotProduct_add, dotProduct_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul,
    Nat.cast_one, one_mul]
  ring

/-- `a04:jet-difference` (exact form, multiplied out). -/
theorem jet_sub_eq {R R' : ℕ → Fin 2 → ℝ} {c : Fin 7 → ℝ} {s t : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    jet R' c s j - jet R c t j = (s - t) * xder c t (j + 1) - (R' j - R j) ⬝ᵥ zy c t -
      (s - t) * (R' j ⬝ᵥ zv c) - (j : ℝ) * ((R' (j - 1) - R (j - 1)) ⬝ᵥ zv c) := by
  have hx := xder_succ_sub (c := c) (s := s) (t := t) hj
  have hy := zy_add c s t
  simp only [jet]
  rw [hy]
  simp only [dotProduct_add, dotProduct_smul, sub_dotProduct, smul_eq_mul]
  linear_combination hx

/-- The Taylor polynomial of a row sequence at `u`, evaluated at `v`. -/
def rowPoly (R : ℕ → Fin 2 → ℝ) (M : ℕ) (u v : ℝ) : Fin 2 → ℝ :=
  ∑ i ∈ range (M + 1), ((v - u) ^ i / (i.factorial : ℝ)) • R i

theorem xder_taylor {c : Fin 7 → ℝ} {u v : ℝ} {M : ℕ} (hM : 2 ≤ M) :
    ∑ i ∈ range (M + 1), xder c u i * (v - u) ^ i / (i.factorial : ℝ) = zx c v := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest : ∑ i ∈ range k, xder c u (i + 1 + 1 + 1) * (v - u) ^ (i + 1 + 1 + 1) /
      ((i + 1 + 1 + 1).factorial : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [xder]
  rw [hrest]
  simp [xder, zx, Nat.factorial]
  ring

/-- `a04:final-jet-expansion` (exact form). -/
theorem zS_eq_taylor {F : ℝ → Fin 2 → ℝ} {R : ℕ → Fin 2 → ℝ} {c : Fin 7 → ℝ} {u v : ℝ} {M : ℕ}
    (hM : 2 ≤ M) :
    zS F c v = ∑ i ∈ range (M + 1), jet R c u i * (v - u) ^ i / (i.factorial : ℝ) -
      (F v - rowPoly R M u v) ⬝ᵥ zy c v -
        (R M ⬝ᵥ zv c) * (v - u) ^ (M + 1) / (M.factorial : ℝ) := by
  have hsplit : ∀ i ∈ range (M + 1), jet R c u i * (v - u) ^ i / (i.factorial : ℝ) =
      xder c u i * (v - u) ^ i / (i.factorial : ℝ) -
        (R i ⬝ᵥ zy c u) * ((v - u) ^ i / (i.factorial : ℝ)) -
        ((i : ℝ) * (R (i - 1) ⬝ᵥ zv c) * (v - u) ^ i / (i.factorial : ℝ)) := by
    intro i _; simp only [jet]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    xder_taylor hM]
  -- the shifted sum
  have hshift : ∑ i ∈ range (M + 1), (i : ℝ) * (R (i - 1) ⬝ᵥ zv c) * (v - u) ^ i /
      (i.factorial : ℝ) =
      (v - u) * ((rowPoly R M u v - ((v - u) ^ M / (M.factorial : ℝ)) • R M) ⬝ᵥ zv c) := by
    rw [Finset.sum_range_succ']
    simp only [CharP.cast_eq_zero, zero_mul, zero_div, add_zero]
    have : rowPoly R M u v - ((v - u) ^ M / (M.factorial : ℝ)) • R M =
        ∑ i ∈ range M, ((v - u) ^ i / (i.factorial : ℝ)) • R i := by
      rw [rowPoly, Finset.sum_range_succ]; abel
    rw [this, sum_dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, smul_dotProduct, smul_eq_mul]
    push_cast
    have hf : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hfirst : ∑ i ∈ range (M + 1), (R i ⬝ᵥ zy c u) * ((v - u) ^ i / (i.factorial : ℝ)) =
      rowPoly R M u v ⬝ᵥ zy c u := by
    rw [rowPoly, sum_dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_dotProduct, smul_eq_mul, mul_comm]
  rw [hshift, hfirst]
  have hy : zy c v = zy c u + (v - u) • zv c := zy_add c v u
  simp only [zS]
  rw [hy]
  simp only [dotProduct_add, dotProduct_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  have hf : (M.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Coefficient-Lipschitz bound for the jets at a time in `[0,1]`. -/
theorem abs_jet_sub_le {R : ℕ → Fin 2 → ℝ} {c c' : Fin 7 → ℝ} {t B r : ℝ} {j : ℕ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hB : ∀ i, ‖R i‖ ≤ B) (h : ‖c - c'‖ ≤ r) :
    |jet R c t j - jet R c' t j| ≤ (3 + 4 * B + 2 * j * B) * r := by
  have hc : ∀ e, |c e - c' e| ≤ r := abs_coeff_sub_le h
  have hr : 0 ≤ r := le_trans (abs_nonneg _) (hc 0)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hxd : |xder c t j - xder c' t j| ≤ 3 * r := by
    match j with
    | 0 =>
      have := abs_zx_sub_le h ht
      simpa [xder] using this
    | 1 =>
      simp only [xder]
      have h1 := hc 1; have h2 := hc 2
      have : c 1 + 2 * c 2 * t - (c' 1 + 2 * c' 2 * t) = (c 1 - c' 1) + 2 * t * (c 2 - c' 2) := by
        ring
      rw [this]
      calc |(c 1 - c' 1) + 2 * t * (c 2 - c' 2)| ≤ |c 1 - c' 1| + |2 * t * (c 2 - c' 2)| :=
            abs_add_le _ _
        _ = |c 1 - c' 1| + 2 * t * |c 2 - c' 2| := by
            rw [abs_mul, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ 2 * t)]
        _ ≤ r + 2 * 1 * r := by
            have := mul_le_mul (by linarith [ht.2] : 2 * t ≤ 2 * 1) h2 (abs_nonneg _) (by norm_num)
            linarith
        _ = 3 * r := by ring
    | 2 =>
      simp only [xder]
      rw [← mul_sub, abs_mul]; norm_num; linarith [hc 2]
    | (n + 3) => simp [xder]; positivity
  have hyd : ‖zy c t - zy c' t‖ ≤ 2 * r := norm_zy_sub_le h ht
  have hvd : ‖zv c - zv c'‖ ≤ r := by
    refine norm_le_of_abs_le hr fun i => ?_
    fin_cases i
    · simpa [zv] using hc 4
    · simpa [zv] using hc 6
  have e : jet R c t j - jet R c' t j = (xder c t j - xder c' t j) - R j ⬝ᵥ (zy c t - zy c' t) -
      (j : ℝ) * (R (j - 1) ⬝ᵥ (zv c - zv c')) := by
    simp only [jet, dotProduct_sub]; ring
  rw [e]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 := abs_dot_le (R j) (zy c t - zy c' t)
  have h2 := abs_dot_le (R (j - 1)) (zv c - zv c')
  have h1' : 2 * ‖R j‖ * ‖zy c t - zy c' t‖ ≤ 2 * B * (2 * r) := by
    gcongr; exact hB j
  have h2' : 2 * ‖R (j - 1)‖ * ‖zv c - zv c'‖ ≤ 2 * B * r := by
    gcongr; exact hB (j - 1)
  calc |(xder c t j - xder c' t j) - R j ⬝ᵥ (zy c t - zy c' t) -
        (j : ℝ) * (R (j - 1) ⬝ᵥ (zv c - zv c'))|
      ≤ |xder c t j - xder c' t j| + |R j ⬝ᵥ (zy c t - zy c' t)| +
          (j : ℝ) * |R (j - 1) ⬝ᵥ (zv c - zv c')| := by
        have h3 := abs_sub (xder c t j - xder c' t j - R j ⬝ᵥ (zy c t - zy c' t))
          ((j : ℝ) * (R (j - 1) ⬝ᵥ (zv c - zv c')))
        have h4 := abs_sub (xder c t j - xder c' t j) (R j ⬝ᵥ (zy c t - zy c' t))
        rw [abs_mul (j : ℝ), abs_of_nonneg hj] at h3
        linarith
    _ ≤ 3 * r + 2 * B * (2 * r) + (j : ℝ) * (2 * B * r) := by
        have := mul_le_mul_of_nonneg_left (h2.trans h2') hj
        linarith
    _ = (3 + 4 * B + 2 * j * B) * r := by ring

theorem measurable_jet {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ} (hc : Measurable c)
    (R : ℕ → Fin 2 → ℝ) (t : ℝ) (j : ℕ) : Measurable (fun l => jet R (c l) t j) := by
  have hcomp : ∀ e : Fin 7, Measurable (fun l => c l e) := fun e => (measurable_pi_apply e).comp hc
  have hx : Measurable (fun l => xder (c l) t j) := by
    match j with
    | 0 => simp only [xder, zx]; fun_prop
    | 1 => simp only [xder]; fun_prop
    | 2 => simp only [xder]; fun_prop
    | (n + 3) => simp only [xder]; exact measurable_const
  simp only [jet, dot_two, zy_zero, zy_one, zv_zero, zv_one]
  have h3 := hcomp 3; have h4 := hcomp 4; have h5 := hcomp 5; have h6 := hcomp 6
  fun_prop

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
