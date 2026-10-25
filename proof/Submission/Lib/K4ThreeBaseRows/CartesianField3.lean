/-
Adapted from: here:o266
Original: session x0947, branch x0947 of o266, file
Submission/Obl/k4_narrow_original_potential_atlas/CartesianField3.lean (commit eda26377).
Moved into a library namespace; imports only Mathlib and modules already in lib.
-/

import Submission.Lib.K4ScalarActualSwitching.GridSampling
import Submission.Lib.K4ScalarActualSwitching.TensorInterpolation

/-! CARTESIAN POLYNOMIAL FIELDS ON A THREE-DIMENSIONAL BASE `(t, y₀, y₁)`.

This generalizes the accepted two-dimensional kernel
`K4ScalarCoreTools.Finalization.exists_cartesian_polynomial_fields`, built on
`K4ScalarActualSwitching.{DenseProductGrid, GridSampling, TensorInterpolation}`, from a base
`X × Y` to a base `X × Y × Z`. The lib kernels are imported; the three-coordinate statements are
new and mirror the two-coordinate ones.

- `tensorInterpolant3` and `tensor3_interpolation_error`: tensor Lagrange interpolation in three
  variables. The error telescopes into three terms,
  `E((1+Λa) + Λa(1+Λb) + ΛaΛb(1+Λc))`.
- `original_product_grid_density3`: the complete 3-partite grid density
  `(E f)^(rst) ≤ E ∏_{ijk} f(x_i,y_j,z_k)`. It comes from the accepted 2D density for each
  third coordinate, plus Jensen.
- `exists_separated_original_grid_anchors3`: separated anchors in all three coordinates, keeping a
  positive density of complete target grids.
- `exists_cartesian_polynomial_fields3`: one bounded polynomial field of degree `≤ 3D` fitting a
  positive fraction of the original coordinate law. Its inputs are degree-`D` fits along `x`-, `y`-
  and `z`-fibers. The kernel consumes those fits; it does not construct qualifying witnesses. -/

namespace Submission.Lib.K4ThreeBaseRows

open Set MvPolynomial
open Submission.Lib.K4ScalarActualSwitching

noncomputable section

namespace CartesianField3

/-! ### Tensor interpolation in three variables -/

/-- A univariate polynomial placed on coordinate `i` of `ℝ³`. -/
def polyOn3 (i : Fin 3) (p : Polynomial ℝ) : MvPolynomial (Fin 3) ℝ := p.eval₂ MvPolynomial.C (X i)

theorem eval_polyOn3 (i : Fin 3) (p : Polynomial ℝ) (z : Fin 3 → ℝ) :
    eval z (polyOn3 i p) = p.eval (z i) := by
  classical
  simp only [polyOn3, Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum, map_sum,
    map_mul, map_pow, eval_C, eval_X]

theorem totalDegree_polyOn3 (i : Fin 3) (p : Polynomial ℝ) :
    (polyOn3 i p).totalDegree ≤ p.natDegree := by
  classical
  rw [polyOn3, Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply totalDegree_finsetSum_le
  intro n hn
  calc (C (p.coeff n) * X i ^ n).totalDegree ≤
        (C (p.coeff n) : MvPolynomial (Fin 3) ℝ).totalDegree + (X i ^ n).totalDegree :=
        totalDegree_mul _ _
    _ = n := by simp
    _ ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)

/-- The tensor Lagrange interpolant on the grid `a × b × c`. -/
def tensorInterpolant3 {D : ℕ} (a b c : Fin (D + 1) → ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ i, ∑ j, ∑ k, C (f (a i) (b j) (c k)) * polyOn3 0 (Lagrange.basis Finset.univ a i) *
    polyOn3 1 (Lagrange.basis Finset.univ b j) * polyOn3 2 (Lagrange.basis Finset.univ c k)

theorem eval_tensorInterpolant3 {D : ℕ} (a b c : Fin (D + 1) → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (x y z : ℝ) :
    eval ![x, y, z] (tensorInterpolant3 a b c f) =
      ∑ i, ∑ j, ∑ k, f (a i) (b j) (c k) * (Lagrange.basis Finset.univ a i).eval x *
        (Lagrange.basis Finset.univ b j).eval y * (Lagrange.basis Finset.univ c k).eval z := by
  classical
  simp only [tensorInterpolant3, map_sum, map_mul, eval_C, eval_polyOn3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem totalDegree_tensorInterpolant3 {D : ℕ} (a b c : Fin (D + 1) → ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hc : Function.Injective c)
    (f : ℝ → ℝ → ℝ → ℝ) : (tensorInterpolant3 a b c f).totalDegree ≤ 3 * D := by
  classical
  have hdegree (d : Fin (D + 1) → ℝ) (hd : Function.Injective d) (i : Fin (D + 1)) :
      (Lagrange.basis Finset.univ d i).natDegree = D := by
    simpa using Lagrange.natDegree_basis hd.injOn (Finset.mem_univ i)
  unfold tensorInterpolant3
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  apply totalDegree_finsetSum_le
  intro k _
  have h0 := totalDegree_polyOn3 0 (Lagrange.basis Finset.univ a i)
  have h1 := totalDegree_polyOn3 1 (Lagrange.basis Finset.univ b j)
  have h2 := totalDegree_polyOn3 2 (Lagrange.basis Finset.univ c k)
  rw [hdegree a ha i] at h0
  rw [hdegree b hb j] at h1
  rw [hdegree c hc k] at h2
  have hC : (C (f (a i) (b j) (c k)) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 0 := by simp
  calc (C (f (a i) (b j) (c k)) * polyOn3 0 (Lagrange.basis Finset.univ a i) *
        polyOn3 1 (Lagrange.basis Finset.univ b j) *
        polyOn3 2 (Lagrange.basis Finset.univ c k)).totalDegree
      ≤ (C (f (a i) (b j) (c k)) * polyOn3 0 (Lagrange.basis Finset.univ a i) *
          polyOn3 1 (Lagrange.basis Finset.univ b j)).totalDegree +
        (polyOn3 2 (Lagrange.basis Finset.univ c k)).totalDegree := totalDegree_mul _ _
    _ ≤ ((C (f (a i) (b j) (c k)) * polyOn3 0 (Lagrange.basis Finset.univ a i)).totalDegree +
          (polyOn3 1 (Lagrange.basis Finset.univ b j)).totalDegree) + D :=
        add_le_add (totalDegree_mul _ _) h2
    _ ≤ (((C (f (a i) (b j) (c k)) : MvPolynomial (Fin 3) ℝ).totalDegree +
          (polyOn3 0 (Lagrange.basis Finset.univ a i)).totalDegree) + D) + D :=
        add_le_add (add_le_add (totalDegree_mul _ _) h1) le_rfl
    _ ≤ ((0 + D) + D) + D := add_le_add (add_le_add (add_le_add hC h0) le_rfl) le_rfl
    _ = 3 * D := by ring

/-- **Three-variable tensor interpolation error.** The target needs a degree-`D` fit along its
`x`-fiber (through the `x`-anchors), fits along the `y`-fibers at the `x`-anchors, and fits along
the `z`-fibers at the anchor pairs. -/
theorem tensor3_interpolation_error {D : ℕ} (a b c : Fin (D + 1) → ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hc : Function.Injective c)
    (f : ℝ → ℝ → ℝ → ℝ) (x y z E : ℝ) (hE : 0 ≤ E)
    (hrow : ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ |f x y z - p.eval x| ≤ E ∧
      ∀ i, |f (a i) y z - p.eval (a i)| ≤ E)
    (hmid : ∀ i, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ |f (a i) y z - p.eval y| ≤ E ∧
      ∀ j, |f (a i) (b j) z - p.eval (b j)| ≤ E)
    (hdep : ∀ i j, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ |f (a i) (b j) z - p.eval z| ≤ E ∧
      ∀ k, |f (a i) (b j) (c k) - p.eval (c k)| ≤ E) :
    |f x y z - eval ![x, y, z] (tensorInterpolant3 a b c f)| ≤
      E * ((1 + ∑ i, |(Lagrange.basis Finset.univ a i).eval x|) +
        (∑ i, |(Lagrange.basis Finset.univ a i).eval x|) *
          (1 + ∑ j, |(Lagrange.basis Finset.univ b j).eval y|) +
        (∑ i, |(Lagrange.basis Finset.univ a i).eval x|) *
          (∑ j, |(Lagrange.basis Finset.univ b j).eval y|) *
          (1 + ∑ k, |(Lagrange.basis Finset.univ c k).eval z|)) := by
  classical
  set La := fun i => (Lagrange.basis Finset.univ a i).eval x with hLa
  set Lb := fun j => (Lagrange.basis Finset.univ b j).eval y with hLb
  set Lc := fun k => (Lagrange.basis Finset.univ c k).eval z with hLc
  set Λa := ∑ i, |La i| with hΛa
  set Λb := ∑ j, |Lb j| with hΛb
  set Λc := ∑ k, |Lc k| with hΛc
  let T1 := ∑ i, f (a i) y z * La i
  let T2 := ∑ i, ∑ j, f (a i) (b j) z * La i * Lb j
  have hΛa0 : 0 ≤ Λa := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hΛb0 : 0 ≤ Λb := Finset.sum_nonneg fun j _ => abs_nonneg _
  -- first term
  obtain ⟨p, hp, htarget, hnodes⟩ := hrow
  have h1 : |f x y z - T1| ≤ E * (1 + Λa) :=
    lagrange_approximation_error a ha p hp (fun x => f x y z) x E hE htarget hnodes
  -- second term
  have hmid' : ∀ i, |f (a i) y z - ∑ j, f (a i) (b j) z * Lb j| ≤ E * (1 + Λb) := by
    intro i
    obtain ⟨q, hq, ht, hn⟩ := hmid i
    exact lagrange_approximation_error b hb q hq (fun y => f (a i) y z) y E hE ht hn
  have h2 : |T1 - T2| ≤ Λa * (E * (1 + Λb)) := by
    have hid : T1 - T2 = ∑ i, (f (a i) y z - ∑ j, f (a i) (b j) z * Lb j) * La i := by
      simp only [T1, T2, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hid]
    calc |∑ i, (f (a i) y z - ∑ j, f (a i) (b j) z * Lb j) * La i|
        ≤ ∑ i, |(f (a i) y z - ∑ j, f (a i) (b j) z * Lb j) * La i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (E * (1 + Λb)) * |La i| := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hmid' i) (abs_nonneg _)
      _ = Λa * (E * (1 + Λb)) := by rw [← Finset.mul_sum]; ring
  -- third term
  have hdep' : ∀ i j, |f (a i) (b j) z - ∑ k, f (a i) (b j) (c k) * Lc k| ≤ E * (1 + Λc) := by
    intro i j
    obtain ⟨q, hq, ht, hn⟩ := hdep i j
    exact lagrange_approximation_error c hc q hq (fun z => f (a i) (b j) z) z E hE ht hn
  have h3 : |T2 - eval ![x, y, z] (tensorInterpolant3 a b c f)| ≤ Λa * Λb * (E * (1 + Λc)) := by
    rw [eval_tensorInterpolant3]
    show |T2 - ∑ i, ∑ j, ∑ k, f (a i) (b j) (c k) * La i * Lb j * Lc k| ≤
      Λa * Λb * (E * (1 + Λc))
    have hid : T2 - ∑ i, ∑ j, ∑ k, f (a i) (b j) (c k) * La i * Lb j * Lc k =
        ∑ i, ∑ j, (f (a i) (b j) z - ∑ k, f (a i) (b j) (c k) * Lc k) * (La i * Lb j) := by
      have hT2 : T2 = ∑ i, ∑ j, f (a i) (b j) z * La i * Lb j := rfl
      rw [hT2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sub_mul, Finset.sum_mul]
      have hk : ∀ k, f (a i) (b j) (c k) * La i * Lb j * Lc k =
          f (a i) (b j) (c k) * Lc k * (La i * Lb j) := fun k => by ring
      simp only [hk]
      ring
    rw [hid]
    calc |∑ i, ∑ j, (f (a i) (b j) z - ∑ k, f (a i) (b j) (c k) * Lc k) * (La i * Lb j)|
        ≤ ∑ i, |∑ j, (f (a i) (b j) z - ∑ k, f (a i) (b j) (c k) * Lc k) * (La i * Lb j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(f (a i) (b j) z - ∑ k, f (a i) (b j) (c k) * Lc k) * (La i * Lb j)| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, (E * (1 + Λc)) * (|La i| * |Lb j|) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_mul]; exact mul_le_mul_of_nonneg_right (hdep' i j) (by positivity)
      _ = Λa * Λb * (E * (1 + Λc)) := by
          rw [hΛa, hΛb, Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  have htri : |f x y z - eval ![x, y, z] (tensorInterpolant3 a b c f)| ≤
      |f x y z - T1| + |T1 - T2| + |T2 - eval ![x, y, z] (tensorInterpolant3 a b c f)| := by
    calc |f x y z - eval ![x, y, z] (tensorInterpolant3 a b c f)|
        = |(f x y z - T1) + (T1 - T2) + (T2 - eval ![x, y, z] (tensorInterpolant3 a b c f))| := by
          ring_nf
      _ ≤ |(f x y z - T1) + (T1 - T2)| + |T2 - eval ![x, y, z] (tensorInterpolant3 a b c f)| :=
          abs_add_le _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  calc |f x y z - eval ![x, y, z] (tensorInterpolant3 a b c f)|
      ≤ E * (1 + Λa) + Λa * (E * (1 + Λb)) + Λa * Λb * (E * (1 + Λc)) := by linarith
    _ = E * ((1 + Λa) + Λa * (1 + Λb) + Λa * Λb * (1 + Λc)) := by ring

/-- The three-variable interpolant is bounded by `H Λa Λb Λc` when the anchor values are `≤ H`. -/
theorem tensor3_interpolant_eval_bound {D : ℕ} (a b c : Fin (D + 1) → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (H : ℝ) (hH : 0 ≤ H) (hf : ∀ i j k, |f (a i) (b j) (c k)| ≤ H) (x y z : ℝ) :
    |eval ![x, y, z] (tensorInterpolant3 a b c f)| ≤
      H * (∑ i, |(Lagrange.basis Finset.univ a i).eval x|) *
        (∑ j, |(Lagrange.basis Finset.univ b j).eval y|) *
        (∑ k, |(Lagrange.basis Finset.univ c k).eval z|) := by
  classical
  rw [eval_tensorInterpolant3]
  calc |∑ i, ∑ j, ∑ k, f (a i) (b j) (c k) * (Lagrange.basis Finset.univ a i).eval x *
        (Lagrange.basis Finset.univ b j).eval y * (Lagrange.basis Finset.univ c k).eval z|
      ≤ ∑ i, ∑ j, ∑ k, |f (a i) (b j) (c k) * (Lagrange.basis Finset.univ a i).eval x *
        (Lagrange.basis Finset.univ b j).eval y * (Lagrange.basis Finset.univ c k).eval z| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, ∑ k, H * |(Lagrange.basis Finset.univ a i).eval x| *
        |(Lagrange.basis Finset.univ b j).eval y| * |(Lagrange.basis Finset.univ c k).eval z| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => by
          rw [abs_mul, abs_mul, abs_mul]
          gcongr
          exact hf i j k
    _ = _ := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-! ### Complete 3-partite grids -/

/-- The complete 3-partite product count, with repetitions and the original weights. -/
def productGridMean3 {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] (r s t : ℕ)
    (p : X → ℝ) (q : Y → ℝ) (u : Z → ℝ) (f : X → Y → Z → ℝ) : ℝ :=
  gridMean (gridProductWeights r p) (fun x => gridMean (gridProductWeights s q) (fun y =>
    gridMean (gridProductWeights t u) (fun z => ∏ i, ∏ j, ∏ k, f (x i) (y j) (z k))))

/-- **3-partite grid density.** `(E f)^(rst) ≤ E ∏_{ijk} f(x_i, y_j, z_k)` for `f ≥ 0`. It follows
from the accepted 2D density for each third coordinate, plus Jensen twice. -/
theorem original_product_grid_density3 {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (r s t : ℕ) (p : X → ℝ) (q : Y → ℝ) (u : Z → ℝ) (f : X → Y → Z → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (hu : ∀ z, 0 ≤ u z) (hu1 : ∑ z, u z = 1) (hf : ∀ x y z, 0 ≤ f x y z) :
    (gridMean p (fun x => gridMean q (fun y => gridMean u (f x y)))) ^ (r * s * t) ≤
      productGridMean3 r s t p q u f := by
  classical
  let G : (Fin r → X) → (Fin s → Y) → ℝ := fun x y =>
    gridMean u (fun z => ∏ i, ∏ j, f (x i) (y j) z)
  have hG0 : ∀ x y, 0 ≤ G x y := fun x y =>
    gridMean_nonneg hu fun z => Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => hf _ _ _
  have hpr := gridProductWeights_nonneg r hp
  have hqs := gridProductWeights_nonneg s hq
  have hpr1 := gridProductWeights_sum r p hp1
  have hqs1 := gridProductWeights_sum s q hq1
  -- the `z`-tuple mean is a `t`-th power
  have hinner : ∀ (x : Fin r → X) (y : Fin s → Y),
      gridMean (gridProductWeights t u) (fun z => ∏ i, ∏ j, ∏ k, f (x i) (y j) (z k)) =
        G x y ^ t := by
    intro x y
    rw [← gridMean_product t u (fun z => ∏ i, ∏ j, f (x i) (y j) z)]
    congr 1
    funext z
    calc ∏ i, ∏ j, ∏ k, f (x i) (y j) (z k) = ∏ i, ∏ k, ∏ j, f (x i) (y j) (z k) :=
          Finset.prod_congr rfl fun i _ => Finset.prod_comm
      _ = ∏ k, ∏ i, ∏ j, f (x i) (y j) (z k) := Finset.prod_comm
  have hP : productGridMean3 r s t p q u f =
      gridMean (gridProductWeights r p) (fun x => gridMean (gridProductWeights s q)
        (fun y => G x y ^ t)) := by
    unfold productGridMean3
    congr 1; funext x; congr 1; funext y
    exact hinner x y
  -- Jensen in the pair of tuples
  have hjensen : (gridMean (gridProductWeights r p) (fun x =>
      gridMean (gridProductWeights s q) (fun y => G x y))) ^ t ≤
      gridMean (gridProductWeights r p) (fun x => gridMean (gridProductWeights s q)
        (fun y => G x y ^ t)) := by
    calc (gridMean (gridProductWeights r p) (fun x =>
          gridMean (gridProductWeights s q) (fun y => G x y))) ^ t
        ≤ gridMean (gridProductWeights r p) (fun x =>
          (gridMean (gridProductWeights s q) (fun y => G x y)) ^ t) :=
          gridMean_pow_le t _ _ hpr hpr1 fun x => gridMean_nonneg hqs fun y => hG0 x y
      _ ≤ _ := gridMean_mono hpr fun x => gridMean_pow_le t _ _ hqs hqs1 fun y => hG0 x y
  -- the pair mean of `G` is a mean of 2D grid counts
  have hswap : gridMean (gridProductWeights r p) (fun x =>
      gridMean (gridProductWeights s q) (fun y => G x y)) =
      gridMean u (fun z => productGridMean r s p q (fun x y => f x y z)) := by
    have h1 : ∀ x : Fin r → X, gridMean (gridProductWeights s q)
        (fun y => gridMean u (fun z => ∏ i, ∏ j, f (x i) (y j) z)) =
        gridMean u (fun z => gridMean (gridProductWeights s q)
          (fun y => ∏ i, ∏ j, f (x i) (y j) z)) := fun x => gridMean_comm _ _ _
    calc gridMean (gridProductWeights r p) (fun x =>
          gridMean (gridProductWeights s q) (fun y => G x y))
        = gridMean (gridProductWeights r p) (fun x => gridMean u (fun z =>
            gridMean (gridProductWeights s q) (fun y => ∏ i, ∏ j, f (x i) (y j) z))) := by
          congr 1; funext x; exact h1 x
      _ = gridMean u (fun z => gridMean (gridProductWeights r p) (fun x =>
            gridMean (gridProductWeights s q) (fun y => ∏ i, ∏ j, f (x i) (y j) z))) :=
          gridMean_comm _ _ _
      _ = gridMean u (fun z => productGridMean r s p q (fun x y => f x y z)) := rfl
  have h2D : ∀ z, (gridMean p (fun x => gridMean q (fun y => f x y z))) ^ (r * s) ≤
      productGridMean r s p q (fun x y => f x y z) := fun z =>
    original_product_grid_density r s p q (fun x y => f x y z) hp hp1 hq hq1 fun x y => hf x y z
  have hmean0 : ∀ z, 0 ≤ gridMean p (fun x => gridMean q (fun y => f x y z)) := fun z =>
    gridMean_nonneg hp fun x => gridMean_nonneg hq fun y => hf x y z
  have hE : gridMean u (fun z => gridMean p (fun x => gridMean q (fun y => f x y z))) =
      gridMean p (fun x => gridMean q (fun y => gridMean u (f x y))) := by
    rw [gridMean_comm u p]
    congr 1; funext x
    exact gridMean_comm u q _
  have hstep : (gridMean p (fun x => gridMean q (fun y => gridMean u (f x y)))) ^ (r * s) ≤
      gridMean (gridProductWeights r p) (fun x =>
        gridMean (gridProductWeights s q) (fun y => G x y)) := by
    rw [hswap, ← hE]
    calc (gridMean u (fun z => gridMean p (fun x => gridMean q (fun y => f x y z)))) ^ (r * s)
        ≤ gridMean u (fun z => (gridMean p (fun x => gridMean q (fun y => f x y z))) ^ (r * s)) :=
          gridMean_pow_le (r * s) u _ hu hu1 hmean0
      _ ≤ _ := gridMean_mono hu h2D
  have hbase0 : 0 ≤ (gridMean p (fun x => gridMean q (fun y => gridMean u (f x y)))) :=
    gridMean_nonneg hp fun x => gridMean_nonneg hq fun y => gridMean_nonneg hu fun z => hf x y z
  rw [hP, pow_mul]
  exact (pow_le_pow_left₀ (pow_nonneg hbase0 _) hstep t).trans hjensen

/-- The product-grid density as a Boolean success event. -/
theorem original_product_grid_success3 {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (r s t : ℕ) (p : X → ℝ) (q : Y → ℝ) (u : Z → ℝ) (R : X → Y → Z → Prop)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (hu : ∀ z, 0 ≤ u z) (hu1 : ∑ z, u z = 1) (η : ℝ) (hη : 0 ≤ η)
    (hR : η ≤ gridMean p (fun x => gridMean q (fun y => gridMean u (fun z => gridFlag (R x y z))))) :
    η ^ (r * s * t) ≤ gridMean (gridProductWeights r p) (fun x =>
      gridMean (gridProductWeights s q) (fun y => gridMean (gridProductWeights t u) (fun z =>
        gridFlag (∀ i j k, R (x i) (y j) (z k))))) := by
  classical
  have h := (pow_le_pow_left₀ hη hR (r * s * t)).trans
    (original_product_grid_density3 r s t p q u (fun x y z => gridFlag (R x y z))
      hp hp1 hq hq1 hu hu1 fun x y z => gridFlag_nonneg _)
  refine h.trans (le_of_eq ?_)
  unfold productGridMean3
  congr 1; funext x; congr 1; funext y; congr 1; funext z
  simp only [gridFlag_eq_ite, Finset.prod_ite_one, Finset.mem_univ, forall_const]
  by_cases h1 : ∀ i j k, R (x i) (y j) (z k)
  · rw [if_pos h1]
    simp [h1]
  · rw [if_neg h1]
    push_neg at h1
    obtain ⟨i, j, k, hijk⟩ := h1
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hijk]

theorem gridFlag_restriction_budget3 (P A B C : Prop) :
    gridFlag P ≤ gridFlag (P ∧ ¬A ∧ ¬B ∧ ¬C) + gridFlag A + gridFlag B + gridFlag C := by
  classical
  by_cases hP : P <;> by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;>
    norm_num [gridFlag, hP, hA, hB, hC]

/-- Collision removal in three coordinates, charged to the original product law. -/
theorem original_separated_product_grid_budget3 {X Y Z : Type*} [Fintype X] [Fintype Y]
    [Fintype Z] (r s t : ℕ) (p : X → ℝ) (q : Y → ℝ) (u : Z → ℝ) (R : X → Y → Z → Prop)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (hu : ∀ z, 0 ≤ u z) (hu1 : ∑ z, u z = 1)
    (v : X → ℝ) (w : Y → ℝ) (o : Z → ℝ) (gap Bx By Bz η : ℝ)
    (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) (hBz : 0 ≤ Bz) (hη : 0 ≤ η)
    (hthinX : ∀ c, gridMean p (fun x => if |v x - c| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ c, gridMean q (fun y => if |w y - c| < gap then 1 else 0) ≤ By)
    (hthinZ : ∀ c, gridMean u (fun z => if |o z - c| < gap then 1 else 0) ≤ Bz)
    (hdensity : η ≤ gridMean p (fun x => gridMean q (fun y =>
      gridMean u (fun z => gridFlag (R x y z))))) :
    η ^ (r * s * t) ≤
      gridMean (gridProductWeights r p) (fun x => gridMean (gridProductWeights s q) (fun y =>
        gridMean (gridProductWeights t u) (fun z =>
          gridFlag ((∀ i j k, R (x i) (y j) (z k)) ∧
            (¬∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < gap) ∧
            (¬∃ i j, i ≠ j ∧ |w (y i) - w (y j)| < gap) ∧
            (¬∃ i j, i ≠ j ∧ |o (z i) - o (z j)| < gap))))) +
        (r : ℝ) ^ 2 * Bx + (s : ℝ) ^ 2 * By + (t : ℝ) ^ 2 * Bz := by
  classical
  have hpx := gridProductWeights_nonneg r hp
  have hqy := gridProductWeights_nonneg s hq
  have huz := gridProductWeights_nonneg t hu
  have hpx1 := gridProductWeights_sum r p hp1
  have hqy1 := gridProductWeights_sum s q hq1
  have huz1 := gridProductWeights_sum t u hu1
  have hgrid := original_product_grid_success3 r s t p q u R hp hp1 hq hq1 hu hu1 η hη hdensity
  have hmono := gridMean_mono hpx (fun x => gridMean_mono hqy (fun y => gridMean_mono huz
    (fun z => gridFlag_restriction_budget3 (∀ i j k, R (x i) (y j) (z k))
      (∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < gap) (∃ i j, i ≠ j ∧ |w (y i) - w (y j)| < gap)
      (∃ i j, i ≠ j ∧ |o (z i) - o (z j)| < gap))))
  simp only [gridMean_add, gridMean_const (gridProductWeights t u) huz1,
    gridMean_const (gridProductWeights s q) hqy1,
    gridMean_const (gridProductWeights r p) hpx1] at hmono
  have hX := gridMean_any_collision r p hp hp1 v gap Bx hBx hthinX
  have hY := gridMean_any_collision s q hq hq1 w gap By hBy hthinY
  have hZ := gridMean_any_collision t u hu hu1 o gap Bz hBz hthinZ
  simp only [← gridFlag_eq_ite] at hX hY hZ
  linarith

theorem gridMean_append_triple {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (r s t : ℕ) (p : X → ℝ) (q : Y → ℝ) (u : Z → ℝ)
    (F : (Fin (r + 1) → X) → (Fin (s + 1) → Y) → (Fin (t + 1) → Z) → ℝ) :
    gridMean (gridProductWeights (r + 1) p) (fun x => gridMean (gridProductWeights (s + 1) q)
      (fun y => gridMean (gridProductWeights (t + 1) u) (F x y))) =
      gridMean (gridProductWeights r p) (fun a => gridMean (gridProductWeights s q) (fun b =>
        gridMean (gridProductWeights t u) (fun c => gridMean p (fun x => gridMean q (fun y =>
          gridMean u (fun z => F (Fin.snoc a x) (Fin.snoc b y) (Fin.snoc c z))))))) := by
  have e1 : ∀ (x : Fin (r + 1) → X), gridMean (gridProductWeights (s + 1) q)
      (fun y => gridMean (gridProductWeights (t + 1) u) (F x y)) =
      gridMean (gridProductWeights s q) (fun b => gridMean q (fun y =>
        gridMean (gridProductWeights t u) (fun c => gridMean u (fun z =>
          F x (Fin.snoc b y) (Fin.snoc c z))))) := by
    intro x
    rw [gridMean_append s q]
    congr 1; funext b; congr 1; funext y
    exact gridMean_append t u _
  calc gridMean (gridProductWeights (r + 1) p) (fun x => gridMean (gridProductWeights (s + 1) q)
        (fun y => gridMean (gridProductWeights (t + 1) u) (F x y)))
      = gridMean (gridProductWeights (r + 1) p) (fun x => gridMean (gridProductWeights s q)
          (fun b => gridMean q (fun y => gridMean (gridProductWeights t u) (fun c =>
            gridMean u (fun z => F x (Fin.snoc b y) (Fin.snoc c z)))))) := by
        congr 1; funext x; exact e1 x
    _ = gridMean (gridProductWeights r p) (fun a => gridMean p (fun x =>
          gridMean (gridProductWeights s q) (fun b => gridMean q (fun y =>
            gridMean (gridProductWeights t u) (fun c => gridMean u (fun z =>
              F (Fin.snoc a x) (Fin.snoc b y) (Fin.snoc c z))))))) := gridMean_append r p _
    _ = _ := by
        congr 1; funext a
        calc gridMean p (fun x => gridMean (gridProductWeights s q) (fun b => gridMean q (fun y =>
              gridMean (gridProductWeights t u) (fun c => gridMean u (fun z =>
                F (Fin.snoc a x) (Fin.snoc b y) (Fin.snoc c z))))))
            = gridMean (gridProductWeights s q) (fun b => gridMean p (fun x => gridMean q (fun y =>
              gridMean (gridProductWeights t u) (fun c => gridMean u (fun z =>
                F (Fin.snoc a x) (Fin.snoc b y) (Fin.snoc c z)))))) := gridMean_comm _ _ _
          _ = _ := by
            congr 1; funext b
            calc gridMean p (fun x => gridMean q (fun y => gridMean (gridProductWeights t u)
                  (fun c => gridMean u (fun z => F (Fin.snoc a x) (Fin.snoc b y) (Fin.snoc c z)))))
                = gridMean p (fun x => gridMean (gridProductWeights t u) (fun c => gridMean q
                    (fun y => gridMean u (fun z =>
                      F (Fin.snoc a x) (Fin.snoc b y) (Fin.snoc c z))))) := by
                  congr 1; funext x; exact gridMean_comm _ _ _
              _ = _ := gridMean_comm _ _ _

/-- **Separated anchors in three coordinates.** -/
theorem exists_separated_original_grid_anchors3 {X Y Z : Type*} [Fintype X] [Fintype Y]
    [Fintype Z] (r s t : ℕ) (p : X → ℝ) (q : Y → ℝ) (u : Z → ℝ) (R : X → Y → Z → Prop)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (hu : ∀ z, 0 ≤ u z) (hu1 : ∑ z, u z = 1)
    (v : X → ℝ) (w : Y → ℝ) (o : Z → ℝ) (gap Bx By Bz η : ℝ)
    (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) (hBz : 0 ≤ Bz) (hη : 0 < η)
    (hthinX : ∀ c, gridMean p (fun x => if |v x - c| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ c, gridMean q (fun y => if |w y - c| < gap then 1 else 0) ≤ By)
    (hthinZ : ∀ c, gridMean u (fun z => if |o z - c| < gap then 1 else 0) ≤ Bz)
    (hdensity : η ≤ gridMean p (fun x => gridMean q (fun y =>
      gridMean u (fun z => gridFlag (R x y z)))))
    (hloss : ((r + 1 : ℕ) : ℝ) ^ 2 * Bx + ((s + 1 : ℕ) : ℝ) ^ 2 * By +
      ((t + 1 : ℕ) : ℝ) ^ 2 * Bz ≤ η ^ ((r + 1) * (s + 1) * (t + 1)) / 2) :
    ∃ (a : Fin r → X) (b : Fin s → Y) (c : Fin t → Z),
      Pairwise (fun i j => gap ≤ |v (a i) - v (a j)|) ∧
      Pairwise (fun i j => gap ≤ |w (b i) - w (b j)|) ∧
      Pairwise (fun i j => gap ≤ |o (c i) - o (c j)|) ∧
      η ^ ((r + 1) * (s + 1) * (t + 1)) / 2 ≤ gridMean p (fun x => gridMean q (fun y =>
        gridMean u (fun z => gridFlag (∀ i j k,
          R (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x i)
            (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y j)
            (Fin.snoc (α := fun _ : Fin (t + 1) => Z) c z k))))) := by
  classical
  let F := fun (x : Fin (r + 1) → X) (y : Fin (s + 1) → Y) (z : Fin (t + 1) → Z) =>
    gridFlag ((∀ i j k, R (x i) (y j) (z k)) ∧
      (¬∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < gap) ∧
      (¬∃ i j, i ≠ j ∧ |w (y i) - w (y j)| < gap) ∧
      (¬∃ i j, i ≠ j ∧ |o (z i) - o (z j)| < gap))
  set Bm := η ^ ((r + 1) * (s + 1) * (t + 1)) / 2 with hBm
  have hB : 0 < Bm := by rw [hBm]; positivity
  have hbudget := original_separated_product_grid_budget3 (r + 1) (s + 1) (t + 1)
    p q u R hp hp1 hq hq1 hu hu1 v w o gap Bx By Bz η hBx hBy hBz hη.le hthinX hthinY hthinZ
    hdensity
  have hmass : Bm ≤ gridMean (gridProductWeights (r + 1) p) (fun x =>
      gridMean (gridProductWeights (s + 1) q) (fun y =>
        gridMean (gridProductWeights (t + 1) u) (F x y))) := by
    rw [hBm]
    push_cast at hloss hbudget
    linarith
  rw [gridMean_append_triple r s t p q u F] at hmass
  have hpr := gridProductWeights_nonneg r hp
  have hqs := gridProductWeights_nonneg s hq
  have hut := gridProductWeights_nonneg t hu
  obtain ⟨a, ha⟩ := gridMean_exists_ge (gridProductWeights r p) _ hpr
    (gridProductWeights_sum r p hp1) Bm hmass
  obtain ⟨b, hb⟩ := gridMean_exists_ge (gridProductWeights s q) _ hqs
    (gridProductWeights_sum s q hq1) Bm ha
  obtain ⟨c, hc⟩ := gridMean_exists_ge (gridProductWeights t u) _ hut
    (gridProductWeights_sum t u hu1) Bm hb
  obtain ⟨x₀, hx₀⟩ := gridMean_exists_ge p _ hp hp1 Bm hc
  obtain ⟨y₀, hy₀⟩ := gridMean_exists_ge q _ hq hq1 Bm hx₀
  obtain ⟨z₀, hz₀⟩ := gridMean_exists_ge u _ hu hu1 Bm hy₀
  have hgood : (∀ i j k, R (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x₀ i)
        (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y₀ j)
        (Fin.snoc (α := fun _ : Fin (t + 1) => Z) c z₀ k)) ∧
      (¬∃ i j, i ≠ j ∧ |v (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x₀ i) -
        v (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x₀ j)| < gap) ∧
      (¬∃ i j, i ≠ j ∧ |w (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y₀ i) -
        w (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y₀ j)| < gap) ∧
      (¬∃ i j, i ≠ j ∧ |o (Fin.snoc (α := fun _ : Fin (t + 1) => Z) c z₀ i) -
        o (Fin.snoc (α := fun _ : Fin (t + 1) => Z) c z₀ j)| < gap) := by
    by_contra hn
    have hz : F (Fin.snoc a x₀) (Fin.snoc b y₀) (Fin.snoc c z₀) = 0 := by
      simp only [F, gridFlag, hn, ↓reduceIte]
    rw [hz] at hz₀
    linarith
  have hsepX := (not_grid_collision_iff (r + 1) v gap
    (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x₀)).mp hgood.2.1
  have hsepY := (not_grid_collision_iff (s + 1) w gap
    (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y₀)).mp hgood.2.2.1
  have hsepZ := (not_grid_collision_iff (t + 1) o gap
    (Fin.snoc (α := fun _ : Fin (t + 1) => Z) c z₀)).mp hgood.2.2.2
  refine ⟨a, b, c, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simpa only [Fin.snoc_castSucc] using hsepX (fun h => hij (Fin.castSucc_injective r h))
  · intro i j hij
    simpa only [Fin.snoc_castSucc] using hsepY (fun h => hij (Fin.castSucc_injective s h))
  · intro i j hij
    simpa only [Fin.snoc_castSucc] using hsepZ (fun h => hij (Fin.castSucc_injective t h))
  · exact hc.trans (gridMean_mono hp (fun x => gridMean_mono hq (fun y => gridMean_mono hu
      (fun z => gridFlag_mono (fun h => h.1)))))

/-! ### The field -/

theorem three_term_le_cube {Λa Λb Λc W : ℝ} (ha0 : 0 ≤ Λa) (hb0 : 0 ≤ Λb) (hc0 : 0 ≤ Λc)
    (ha : Λa ≤ W) (hb : Λb ≤ W) (hc : Λc ≤ W) :
    (1 + Λa) + Λa * (1 + Λb) + Λa * Λb * (1 + Λc) ≤ (1 + W) ^ 3 := by
  have hW : 0 ≤ W := ha0.trans ha
  have h1 : Λa * (1 + Λb) ≤ W * (1 + W) := mul_le_mul ha (by linarith) (by linarith) hW
  have h2 : Λa * Λb ≤ W * W := mul_le_mul ha hb hb0 hW
  have h3 : Λa * Λb * (1 + Λc) ≤ W * W * (1 + W) :=
    mul_le_mul h2 (by linarith) (by linarith) (by positivity)
  nlinarith [sq_nonneg W]

/-- **Cartesian polynomial fields on a three-dimensional base.** A dense retained Cartesian grid
`X × Y × Z`, with degree-`D` fits along its `x`-, `y`- and `z`-fibers, supplies one bounded
polynomial field per component. It has degree `≤ 3D` and fits a positive fraction of the original
coordinate law. It is the three-coordinate version of the accepted
`exists_cartesian_polynomial_fields`. -/
theorem exists_cartesian_polynomial_fields3 {ι X Y Z : Type*} [Fintype X] [Fintype Y]
    [Fintype Z] (D : ℕ) (p : X → ℝ) (q : Y → ℝ) (u : Z → ℝ) (R : X → Y → Z → Prop)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (hu : ∀ z, 0 ≤ u z) (hu1 : ∑ z, u z = 1)
    (v : X → ℝ) (w : Y → ℝ) (o : Z → ℝ) (B gap Bx By Bz η E H : ℝ)
    (hB : 0 ≤ B) (hgap : 0 < gap) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) (hBz : 0 ≤ Bz)
    (hη : 0 < η) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hv : ∀ x, |v x| ≤ B) (hw : ∀ y, |w y| ≤ B) (ho : ∀ z, |o z| ≤ B)
    (hthinX : ∀ c, gridMean p (fun x => if |v x - c| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ c, gridMean q (fun y => if |w y - c| < gap then 1 else 0) ≤ By)
    (hthinZ : ∀ c, gridMean u (fun z => if |o z - c| < gap then 1 else 0) ≤ Bz)
    (hdensity : η ≤ gridMean p (fun x => gridMean q (fun y =>
      gridMean u (fun z => gridFlag (R x y z)))))
    (hloss : ((D : ℝ) + 2) ^ 2 * Bx + ((D : ℝ) + 2) ^ 2 * By + ((D : ℝ) + 2) ^ 2 * Bz ≤
      η ^ ((D + 2) * (D + 2) * (D + 2)) / 2)
    (f : ι → ℝ → ℝ → ℝ → ℝ) (hvals : ∀ c x y z, R x y z → |f c (v x) (w y) (o z)| ≤ H)
    (hrows : ∀ c y z, ∃ a : Polynomial ℝ, a.natDegree ≤ D ∧
      ∀ x, R x y z → |f c (v x) (w y) (o z) - a.eval (v x)| ≤ E)
    (hmids : ∀ c x z, ∃ a : Polynomial ℝ, a.natDegree ≤ D ∧
      ∀ y, R x y z → |f c (v x) (w y) (o z) - a.eval (w y)| ≤ E)
    (hdeps : ∀ c x y, ∃ a : Polynomial ℝ, a.natDegree ≤ D ∧
      ∀ z, R x y z → |f c (v x) (w y) (o z) - a.eval (o z)| ≤ E) :
    ∃ P : ι → MvPolynomial (Fin 3) ℝ, (∀ c, (P c).totalDegree ≤ 3 * D) ∧
      (∀ c, ∀ x y z : ℝ, |x| ≤ B → |y| ≤ B → |z| ≤ B →
        |eval ![x, y, z] (P c)| ≤ H * (((D : ℝ) + 1) * (2 * B / gap) ^ D) ^ 3) ∧
      η ^ ((D + 2) * (D + 2) * (D + 2)) / 2 ≤ gridMean p (fun x => gridMean q (fun y =>
        gridMean u (fun z => gridFlag (R x y z ∧ ∀ c, |f c (v x) (w y) (o z) -
          eval ![v x, w y, o z] (P c)| ≤ E * (1 + ((D : ℝ) + 1) * (2 * B / gap) ^ D) ^ 3)))) := by
  classical
  set W := ((D : ℝ) + 1) * (2 * B / gap) ^ D with hWdef
  have hW : 0 ≤ W := by rw [hWdef]; positivity
  have hcount : ((D + 1 + 1 : ℕ) : ℝ) ^ 2 * Bx + ((D + 1 + 1 : ℕ) : ℝ) ^ 2 * By +
      ((D + 1 + 1 : ℕ) : ℝ) ^ 2 * Bz ≤ η ^ ((D + 1 + 1) * (D + 1 + 1) * (D + 1 + 1)) / 2 := by
    have hcast : ((D + 1 + 1 : ℕ) : ℝ) = (D : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    exact hloss
  obtain ⟨a, b, c, hsepA, hsepB, hsepC, hmass⟩ := exists_separated_original_grid_anchors3
    (D + 1) (D + 1) (D + 1) p q u R hp hp1 hq hq1 hu hu1 v w o gap Bx By Bz η hBx hBy hBz hη
    hthinX hthinY hthinZ hdensity hcount
  let Good : X → Y → Z → Prop := fun x y z => ∀ i j k,
    R (Fin.snoc (α := fun _ : Fin (D + 1 + 1) => X) a x i)
      (Fin.snoc (α := fun _ : Fin (D + 1 + 1) => Y) b y j)
      (Fin.snoc (α := fun _ : Fin (D + 1 + 1) => Z) c z k)
  change η ^ ((D + 1 + 1) * (D + 1 + 1) * (D + 1 + 1)) / 2 ≤ gridMean p (fun x =>
    gridMean q (fun y => gridMean u (fun z => gridFlag (Good x y z)))) at hmass
  have hgood : ∃ x y z, Good x y z := by
    by_contra hn
    push_neg at hn
    have hz : ∀ x y z, gridFlag (Good x y z) = 0 := by
      intro x y z
      simp [gridFlag, hn x y z]
    simp only [hz, gridMean, mul_zero, Finset.sum_const_zero] at hmass
    exact (not_le_of_gt (by positivity : 0 < η ^ ((D + 1 + 1) * (D + 1 + 1) * (D + 1 + 1)) / 2))
      hmass
  obtain ⟨x₀, y₀, z₀, h₀⟩ := hgood
  have hanchor (i j k : Fin (D + 1)) : R (a i) (b j) (c k) := by
    simpa only [Fin.snoc_castSucc] using h₀ i.castSucc j.castSucc k.castSucc
  have hparts (x : X) (y : Y) (z : Z) (h : Good x y z) :
      R x y z ∧ (∀ i, R (a i) y z) ∧ (∀ i j, R (a i) (b j) z) := by
    refine ⟨?_, fun i => ?_, fun i j => ?_⟩
    · simpa only [Fin.snoc_last] using h (Fin.last _) (Fin.last _) (Fin.last _)
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using h i.castSucc (Fin.last _) (Fin.last _)
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using h i.castSucc j.castSucc (Fin.last _)
  have hinjA : Function.Injective (fun i => v (a i)) := by
    intro i j heq
    by_contra hij
    have h : gap ≤ |v (a i) - v (a j)| := hsepA hij
    change v (a i) = v (a j) at heq
    rw [heq, sub_self, abs_zero] at h
    exact (not_le_of_gt hgap) h
  have hinjB : Function.Injective (fun j => w (b j)) := by
    intro i j heq
    by_contra hij
    have h : gap ≤ |w (b i) - w (b j)| := hsepB hij
    change w (b i) = w (b j) at heq
    rw [heq, sub_self, abs_zero] at h
    exact (not_le_of_gt hgap) h
  have hinjC : Function.Injective (fun k => o (c k)) := by
    intro i j heq
    by_contra hij
    have h : gap ≤ |o (c i) - o (c j)| := hsepC hij
    change o (c i) = o (c j) at heq
    rw [heq, sub_self, abs_zero] at h
    exact (not_le_of_gt hgap) h
  let P : ι → MvPolynomial (Fin 3) ℝ := fun κ =>
    tensorInterpolant3 (fun i => v (a i)) (fun j => w (b j)) (fun k => o (c k)) (f κ)
  have hwA (x : ℝ) (hx : |x| ≤ B) :
      (∑ i, |(Lagrange.basis Finset.univ (fun i => v (a i)) i).eval x|) ≤ W :=
    lagrange_weight_sum_bound _ B gap hB hgap (fun i => hv (a i)) hsepA x hx
  have hwB (y : ℝ) (hy : |y| ≤ B) :
      (∑ j, |(Lagrange.basis Finset.univ (fun j => w (b j)) j).eval y|) ≤ W :=
    lagrange_weight_sum_bound _ B gap hB hgap (fun j => hw (b j)) hsepB y hy
  have hwC (z : ℝ) (hz : |z| ≤ B) :
      (∑ k, |(Lagrange.basis Finset.univ (fun k => o (c k)) k).eval z|) ≤ W :=
    lagrange_weight_sum_bound _ B gap hB hgap (fun k => ho (c k)) hsepC z hz
  have hfit (κ : ι) (x : X) (y : Y) (z : Z) (h : Good x y z) :
      |f κ (v x) (w y) (o z) - eval ![v x, w y, o z] (P κ)| ≤ E * (1 + W) ^ 3 := by
    obtain ⟨hxyz, hayz, habz⟩ := hparts x y z h
    have hrow : ∃ e : Polynomial ℝ, e.natDegree ≤ D ∧
        |f κ (v x) (w y) (o z) - e.eval (v x)| ≤ E ∧
        ∀ i, |f κ (v (a i)) (w y) (o z) - e.eval (v (a i))| ≤ E := by
      obtain ⟨e, he, hefit⟩ := hrows κ y z
      exact ⟨e, he, hefit x hxyz, fun i => hefit (a i) (hayz i)⟩
    have hmid (i : Fin (D + 1)) : ∃ e : Polynomial ℝ, e.natDegree ≤ D ∧
        |f κ (v (a i)) (w y) (o z) - e.eval (w y)| ≤ E ∧
        ∀ j, |f κ (v (a i)) (w (b j)) (o z) - e.eval (w (b j))| ≤ E := by
      obtain ⟨e, he, hefit⟩ := hmids κ (a i) z
      exact ⟨e, he, hefit y (hayz i), fun j => hefit (b j) (habz i j)⟩
    have hdep (i j : Fin (D + 1)) : ∃ e : Polynomial ℝ, e.natDegree ≤ D ∧
        |f κ (v (a i)) (w (b j)) (o z) - e.eval (o z)| ≤ E ∧
        ∀ k, |f κ (v (a i)) (w (b j)) (o (c k)) - e.eval (o (c k))| ≤ E := by
      obtain ⟨e, he, hefit⟩ := hdeps κ (a i) (b j)
      exact ⟨e, he, hefit z (habz i j), fun k => hefit (c k) (hanchor i j k)⟩
    have herr := tensor3_interpolation_error (fun i => v (a i)) (fun j => w (b j))
      (fun k => o (c k)) hinjA hinjB hinjC (f κ) (v x) (w y) (o z) E hE hrow hmid hdep
    refine herr.trans (mul_le_mul_of_nonneg_left ?_ hE)
    exact three_term_le_cube (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (hwA _ (hv x)) (hwB _ (hw y)) (hwC _ (ho z))
  refine ⟨P, fun κ => totalDegree_tensorInterpolant3 _ _ _ hinjA hinjB hinjC (f κ), ?_, ?_⟩
  · intro κ x y z hx hy hz
    refine (tensor3_interpolant_eval_bound _ _ _ (f κ) H hH
      (fun i j k => hvals κ _ _ _ (hanchor i j k)) x y z).trans ?_
    have h1 := hwA x hx
    have h2 := hwB y hy
    have h3 := hwC z hz
    have h0a : 0 ≤ ∑ i, |(Lagrange.basis Finset.univ (fun i => v (a i)) i).eval x| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h0b : 0 ≤ ∑ j, |(Lagrange.basis Finset.univ (fun j => w (b j)) j).eval y| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h0c : 0 ≤ ∑ k, |(Lagrange.basis Finset.univ (fun k => o (c k)) k).eval z| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc H * (∑ i, |(Lagrange.basis Finset.univ (fun i => v (a i)) i).eval x|) *
          (∑ j, |(Lagrange.basis Finset.univ (fun j => w (b j)) j).eval y|) *
          (∑ k, |(Lagrange.basis Finset.univ (fun k => o (c k)) k).eval z|)
        ≤ H * W * W * W := by gcongr
      _ = H * W ^ 3 := by ring
  · have hmono : gridMean p (fun x => gridMean q (fun y => gridMean u (fun z =>
        gridFlag (Good x y z)))) ≤ gridMean p (fun x => gridMean q (fun y => gridMean u (fun z =>
        gridFlag (R x y z ∧ ∀ κ, |f κ (v x) (w y) (o z) - eval ![v x, w y, o z] (P κ)| ≤
          E * (1 + W) ^ 3)))) :=
      gridMean_mono hp fun x => gridMean_mono hq fun y => gridMean_mono hu fun z =>
        gridFlag_mono fun h => ⟨(hparts x y z h).1, fun κ => hfit κ x y z h⟩
    have hexp : (D + 1 + 1) * (D + 1 + 1) * (D + 1 + 1) = (D + 2) * (D + 2) * (D + 2) := by ring
    rw [hexp] at hmass
    exact hmass.trans hmono

end CartesianField3

end

end Submission.Lib.K4ThreeBaseRows
