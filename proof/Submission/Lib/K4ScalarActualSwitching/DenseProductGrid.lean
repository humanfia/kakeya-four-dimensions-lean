/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 5d4285028d58add87cf09665e156b5aba0b683af,
Submission/Obl/k4_scalar_mesh_projection/DenseProductGrid.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Mathlib

namespace Submission.Lib.K4ScalarActualSwitching

open Set

noncomputable def gridMean {X : Type*} [Fintype X] (p f : X → ℝ) : ℝ :=
  ∑ x, p x * f x

noncomputable def gridProductWeights {X : Type*} [Fintype X] (n : ℕ)
    (p : X → ℝ) (x : Fin n → X) : ℝ := ∏ i, p (x i)

theorem gridMean_nonneg {X : Type*} [Fintype X] {p f : X → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hf : ∀ x, 0 ≤ f x) : 0 ≤ gridMean p f := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (hf x)

theorem gridMean_mono {X : Type*} [Fintype X] {p f g : X → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hfg : ∀ x, f x ≤ g x) : gridMean p f ≤ gridMean p g := by
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hp x)

theorem gridMean_comm {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (q : Y → ℝ) (f : X → Y → ℝ) :
    gridMean p (fun x => gridMean q (f x)) =
      gridMean q (fun y => gridMean p (fun x => f x y)) := by
  classical
  simp only [gridMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem gridProductWeights_nonneg {X : Type*} [Fintype X] (n : ℕ)
    {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) : ∀ x, 0 ≤ gridProductWeights n p x := by
  intro x
  exact Finset.prod_nonneg fun i _ => hp (x i)

theorem gridMean_product {X : Type*} [Fintype X] (n : ℕ) (p f : X → ℝ) :
    gridMean (gridProductWeights n p) (fun x => ∏ i, f (x i)) = (gridMean p f) ^ n := by
  classical
  have h := Finset.sum_pow' (Finset.univ : Finset X) (fun x => p x * f x) n
  simpa only [Fintype.piFinset_univ, gridMean, gridProductWeights, Finset.prod_mul_distrib] using h.symm

theorem gridProductWeights_sum {X : Type*} [Fintype X] (n : ℕ)
    (p : X → ℝ) (hp : ∑ x, p x = 1) : ∑ x, gridProductWeights n p x = 1 := by
  have h := gridMean_product n p (fun _ => 1)
  simpa only [gridMean, Finset.prod_const_one, mul_one, hp, one_pow] using h

theorem gridMean_pow_le {X : Type*} [Fintype X] (n : ℕ) (p f : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hf : ∀ x, 0 ≤ f x) :
    (gridMean p f) ^ n ≤ gridMean p (fun x => f x ^ n) := by
  classical
  simpa only [gridMean, smul_eq_mul] using
    (convexOn_pow (𝕜 := ℝ) n).map_sum_le (t := Finset.univ) (w := p) (p := f)
      (fun x _ => hp x) hp1 (fun x _ => hf x)

/-- The complete rectangular product count, with repetitions allowed and
the original coordinate probability weights kept explicit. -/
noncomputable def productGridMean {X Y : Type*} [Fintype X] [Fintype Y]
    (r s : ℕ) (p : X → ℝ) (q : Y → ℝ) (f : X → Y → ℝ) : ℝ :=
  gridMean (gridProductWeights r p) (fun x =>
    gridMean (gridProductWeights s q) (fun y => ∏ i, ∏ j, f (x i) (y j)))

/-- A dense relation has many complete product grids. Two applications
of Jensen preserve a fixed power of the original density. -/
theorem original_product_grid_density {X Y : Type*} [Fintype X] [Fintype Y]
    (r s : ℕ) (p : X → ℝ) (q : Y → ℝ) (f : X → Y → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (hf : ∀ x y, 0 ≤ f x y) :
    (gridMean p (fun x => gridMean q (f x))) ^ (r * s) ≤ productGridMean r s p q f := by
  classical
  let g : (Fin r → X) → ℝ := fun x => gridMean q (fun y => ∏ i, f (x i) y)
  have hg : ∀ x, 0 ≤ g x := by
    intro x
    apply gridMean_nonneg hq
    intro y
    exact Finset.prod_nonneg fun i _ => hf _ _
  have hfirst : (gridMean p (fun x => gridMean q (f x))) ^ r ≤
      gridMean (gridProductWeights r p) g := by
    rw [gridMean_comm p q f]
    have h := gridMean_pow_le r q (fun y => gridMean p (fun x => f x y)) hq hq1
      (fun y => gridMean_nonneg hp (fun x => hf x y))
    apply h.trans_eq
    simp_rw [← gridMean_product r p]
    exact (gridMean_comm q (gridProductWeights r p) _).trans rfl
  have hfirst0 : 0 ≤ (gridMean p (fun x => gridMean q (f x))) ^ r :=
    pow_nonneg (gridMean_nonneg hp (fun x => gridMean_nonneg hq (hf x))) r
  have hsecond := gridMean_pow_le s (gridProductWeights r p) g
    (gridProductWeights_nonneg r hp) (gridProductWeights_sum r p hp1) hg
  calc
    _ = ((gridMean p (fun x => gridMean q (f x))) ^ r) ^ s := by rw [pow_mul]
    _ ≤ (gridMean (gridProductWeights r p) g) ^ s := pow_le_pow_left₀ hfirst0 hfirst s
    _ ≤ gridMean (gridProductWeights r p) (fun x => g x ^ s) := hsecond
    _ = productGridMean r s p q f := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      dsimp only [g]
      rw [← gridMean_product s q]
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      exact Finset.prod_comm

end Submission.Lib.K4ScalarActualSwitching
