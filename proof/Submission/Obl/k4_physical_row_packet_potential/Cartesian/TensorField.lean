-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/TensorField.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/TensorField.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0358 (as merged
-- on branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/TensorField.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Mathlib
import Submission.Lib.K4PolynomialRemezThree

/-!
# The tensor Lagrange polynomial through a Cartesian anchor grid

Paper `tex-06-isotropic.tex`, Section 6, "Cartesian interpolation of the physical field": the
field values on a complete `(D+1)×(D+1)×(D+1)` grid of anchors `(a i, b j, c k)` are
interpolated by the tensor product of the univariate Lagrange bases.  We construct this
interpolant as an actual polynomial `tensorPoly a b c V : MvPolynomial (Fin 3) ℝ`:

* `totalDegree_tensorPoly`: total degree at most `3 D`;
* `eval_tensorPoly`: `eval x P = ∑ i j k, V i j k * lag a i (x 0) * lag b j (x 1) * lag c k (x 2)`,
  where `lag a i t = ∏_{j ≠ i} (t - a j) / (a i - a j)` (`lag_eq_eval_basis`: Mathlib's
  `Lagrange.basis`);
* `eval_tensorPoly_anchor`: `P (a i, b j, c k) = V i j k` for injective anchors;
* `abs_lag_le`: `|lag a i t| ≤ ((|t| + A) / δ)^D` when `|a j| ≤ A` and the anchors are
  `δ`-separated;
* `exists_tensorPoly_coeff_bound`: for each `D` one constant `C_D` with every coefficient at
  most `C_D (D+1)^3 ((1 + A)/δ)^(3D) B` when `|V| ≤ B` (through the accepted
  `Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_on_unit_cube`).

Each Lagrange factor is an explicit product of linear `MvPolynomial`s, so no univariate to
multivariate degree bridge is needed.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MvPolynomial

noncomputable section

variable {D : ℕ}

/-- The univariate Lagrange basis value at `t` for the nodes `a`, index `i`. -/
def lag (a : Fin (D + 1) → ℝ) (i : Fin (D + 1)) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (t - a j) / (a i - a j)

/-- The Lagrange basis polynomial in the coordinate `v` of `ℝ³`. -/
def lagMv (v : Fin 3) (a : Fin (D + 1) → ℝ) (i : Fin (D + 1)) : MvPolynomial (Fin 3) ℝ :=
  ∏ j ∈ Finset.univ.erase i, (C (a i - a j)⁻¹ * (X v - C (a j)))

/-- The tensor Lagrange interpolant of anchor values `V` on the grid `a × b × c`. -/
def tensorPoly (a b c : Fin (D + 1) → ℝ) (V : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ i, ∑ j, ∑ k, C (V i j k) * lagMv 0 a i * lagMv 1 b j * lagMv 2 c k

theorem eval_lagMv (v : Fin 3) (a : Fin (D + 1) → ℝ) (i : Fin (D + 1)) (x : Fin 3 → ℝ) :
    eval x (lagMv v a i) = lag a i (x v) := by
  simp only [lagMv, lag, map_prod, map_mul, eval_C, map_sub, eval_X]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [div_eq_inv_mul]

theorem totalDegree_lagMv_le (v : Fin 3) (a : Fin (D + 1) → ℝ) (i : Fin (D + 1)) :
    (lagMv v a i).totalDegree ≤ D := by
  classical
  unfold lagMv
  refine (totalDegree_finsetProd _ _).trans ?_
  have hfac : ∀ j ∈ Finset.univ.erase i,
      (C (a i - a j)⁻¹ * (X v - C (a j)) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by
    intro j _
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_X, totalDegree_C]
    simp
  calc ∑ j ∈ Finset.univ.erase i, (C (a i - a j)⁻¹ * (X v - C (a j)) :
        MvPolynomial (Fin 3) ℝ).totalDegree
      ≤ ∑ _j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum hfac
    _ = D := by simp [Finset.card_erase_of_mem]

theorem totalDegree_tensorPoly_le (a b c : Fin (D + 1) → ℝ)
    (V : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℝ) :
    (tensorPoly a b c V).totalDegree ≤ 3 * D := by
  classical
  unfold tensorPoly
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  refine (add_le_add (totalDegree_mul _ _) (totalDegree_lagMv_le 2 c k)).trans ?_
  refine (add_le_add (add_le_add (totalDegree_mul _ _) (totalDegree_lagMv_le 1 b j))
    le_rfl).trans ?_
  have h0 := totalDegree_lagMv_le 0 a i
  rw [totalDegree_C]
  omega

/-- The exact evaluation formula of the tensor interpolant. -/
theorem eval_tensorPoly (a b c : Fin (D + 1) → ℝ)
    (V : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℝ) (x : Fin 3 → ℝ) :
    eval x (tensorPoly a b c V) =
      ∑ i, ∑ j, ∑ k, V i j k * lag a i (x 0) * lag b j (x 1) * lag c k (x 2) := by
  simp only [tensorPoly, map_sum, map_mul, eval_C, eval_lagMv]

theorem lag_self (a : Fin (D + 1) → ℝ) (ha : Function.Injective a) (i : Fin (D + 1)) :
    lag a i (a i) = 1 := by
  unfold lag
  refine Finset.prod_eq_one (fun j hj => ?_)
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have : a i - a j ≠ 0 := sub_ne_zero.mpr (fun h => hji (ha h.symm))
  exact div_self this

theorem lag_of_ne (a : Fin (D + 1) → ℝ) {i j : Fin (D + 1)} (hij : j ≠ i) :
    lag a i (a j) = 0 := by
  unfold lag
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩) (by simp)

theorem lag_anchor (a : Fin (D + 1) → ℝ) (ha : Function.Injective a) (i j : Fin (D + 1)) :
    lag a i (a j) = if j = i then 1 else 0 := by
  split_ifs with h
  · subst h; exact lag_self a ha j
  · exact lag_of_ne a h

/-- The tensor interpolant takes the prescribed values at the anchors. -/
theorem eval_tensorPoly_anchor (a b c : Fin (D + 1) → ℝ) (ha : Function.Injective a)
    (hb : Function.Injective b) (hc : Function.Injective c)
    (V : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℝ) (i j k : Fin (D + 1)) :
    eval ![a i, b j, c k] (tensorPoly a b c V) = V i j k := by
  rw [eval_tensorPoly]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, lag_anchor a ha, lag_anchor b hb, lag_anchor c hc,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- The value `lag` is Mathlib's Lagrange basis polynomial evaluated at `t`. -/
theorem lag_eq_eval_basis (a : Fin (D + 1) → ℝ) (i : Fin (D + 1)) (t : ℝ) :
    lag a i t = (Lagrange.basis Finset.univ a i).eval t := by
  rw [Lagrange.basis, Polynomial.eval_prod, lag]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, div_eq_inv_mul]

/-- Size of a Lagrange basis value: `|lag a i t| ≤ ((|t| + A) / δ)^D` for nodes bounded by
`A` and `δ`-separated. -/
theorem abs_lag_le (a : Fin (D + 1) → ℝ) (A δ : ℝ) (hδ : 0 < δ) (hA : ∀ j, |a j| ≤ A)
    (hsep : ∀ i j, i ≠ j → δ ≤ |a i - a j|) (i : Fin (D + 1)) (t : ℝ) :
    |lag a i t| ≤ ((|t| + A) / δ) ^ D := by
  unfold lag
  rw [Finset.abs_prod]
  have hcard : (Finset.univ.erase i).card = D := by simp [Finset.card_erase_of_mem]
  calc ∏ j ∈ Finset.univ.erase i, |(t - a j) / (a i - a j)|
      ≤ ∏ _j ∈ Finset.univ.erase i, ((|t| + A) / δ) := by
        refine Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j hj => ?_)
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        have hsepij := hsep i j (Ne.symm hji)
        have hpos : 0 < |a i - a j| := lt_of_lt_of_le hδ hsepij
        rw [abs_div, div_le_div_iff₀ hpos hδ]
        have h1 : |t - a j| ≤ |t| + A := (abs_sub _ _).trans (by linarith [hA j])
        have h2 : 0 ≤ |t| + A := by linarith [abs_nonneg t, (abs_nonneg (a j)).trans (hA j)]
        calc |t - a j| * δ ≤ (|t| + A) * δ := by gcongr
          _ ≤ (|t| + A) * |a i - a j| := by gcongr
    _ = ((|t| + A) / δ) ^ D := by rw [Finset.prod_const, hcard]

/-- On the unit cube the tensor interpolant is at most `(D+1)^3 B ((1 + A)/δ)^(3D)`. -/
theorem abs_eval_tensorPoly_le (a b c : Fin (D + 1) → ℝ) (A δ B : ℝ) (hδ : 0 < δ)
    (hA0 : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ j, |a j| ≤ A) (hb : ∀ j, |b j| ≤ A) (hc : ∀ j, |c j| ≤ A)
    (hsa : ∀ i j, i ≠ j → δ ≤ |a i - a j|) (hsb : ∀ i j, i ≠ j → δ ≤ |b i - b j|)
    (hsc : ∀ i j, i ≠ j → δ ≤ |c i - c j|)
    (V : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℝ) (hV : ∀ i j k, |V i j k| ≤ B)
    (x : Fin 3 → ℝ) (hx : ∀ v, |x v| ≤ 1) :
    |eval x (tensorPoly a b c V)| ≤ ((D : ℝ) + 1) ^ 3 * B * ((1 + A) / δ) ^ (3 * D) := by
  rw [eval_tensorPoly]
  set E := ((1 + A) / δ) ^ D with hE
  have hE0 : 0 ≤ E := by positivity
  have hlag : ∀ (n : Fin (D + 1) → ℝ), (∀ j, |n j| ≤ A) →
      (∀ i j, i ≠ j → δ ≤ |n i - n j|) → ∀ i v, |lag n i (x v)| ≤ E := by
    intro n hn hsn i v
    refine (abs_lag_le n A δ hδ hn hsn i (x v)).trans ?_
    rw [hE]
    gcongr
    exact hx v
  have hterm : ∀ i j k, |V i j k * lag a i (x 0) * lag b j (x 1) * lag c k (x 2)| ≤ B * E ^ 3 := by
    intro i j k
    rw [abs_mul, abs_mul, abs_mul]
    have h1 := hV i j k
    have h2 := hlag a ha hsa i 0
    have h3 := hlag b hb hsb j 1
    have h4 := hlag c hc hsc k 2
    calc |V i j k| * |lag a i (x 0)| * |lag b j (x 1)| * |lag c k (x 2)|
        ≤ B * E * E * E := by gcongr
      _ = B * E ^ 3 := by ring
  calc |∑ i, ∑ j, ∑ k, V i j k * lag a i (x 0) * lag b j (x 1) * lag c k (x 2)|
      ≤ ∑ i, ∑ j, ∑ k, |V i j k * lag a i (x 0) * lag b j (x 1) * lag c k (x 2)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (D + 1), ∑ _j : Fin (D + 1), ∑ _k : Fin (D + 1), B * E ^ 3 := by
        gcongr with i _ j _ k _
        exact hterm i j k
    _ = ((D : ℝ) + 1) ^ 3 * B * ((1 + A) / δ) ^ (3 * D) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [hE, ← pow_mul, mul_comm D 3]
        push_cast
        ring

/-- **Coefficient bound for the tensor interpolant**: one constant `C_D` for each degree. -/
theorem exists_tensorPoly_coeff_bound (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b c : Fin (D + 1) → ℝ) (A δ B : ℝ), 0 < δ → 0 ≤ A → 0 ≤ B →
      (∀ j, |a j| ≤ A) → (∀ j, |b j| ≤ A) → (∀ j, |c j| ≤ A) →
      (∀ i j, i ≠ j → δ ≤ |a i - a j|) → (∀ i j, i ≠ j → δ ≤ |b i - b j|) →
      (∀ i j, i ≠ j → δ ≤ |c i - c j|) →
      ∀ V : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℝ, (∀ i j k, |V i j k| ≤ B) →
      ∀ d, |(tensorPoly a b c V).coeff d| ≤
        C * (((D : ℝ) + 1) ^ 3 * B * ((1 + A) / δ) ^ (3 * D)) := by
  obtain ⟨C, hC, hcoef⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_on_unit_cube 3 (3 * D)
  refine ⟨C, hC, ?_⟩
  intro a b c A δ B hδ hA0 hB ha hb hc hsa hsb hsc V hV d
  refine hcoef (tensorPoly a b c V) (totalDegree_tensorPoly_le a b c V) _ (by positivity)
    (fun x hx => ?_) d
  refine abs_eval_tensorPoly_le a b c A δ B hδ hA0 hB ha hb hc hsa hsb hsc V hV x (fun v => ?_)
  have h0 := hx.1 v
  have h1 := hx.2 v
  rw [abs_le]
  simp only [Pi.zero_apply, Pi.one_apply] at h0 h1
  constructor <;> linarith

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
