-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/CartesianGrids.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/CartesianGrids.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/CartesianGrids.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Mathlib

/-!
Weighted Cartesian grid counts for the interpolation step in Section 6.
All laws are finite probabilities, and no independence is assumed beyond
the explicitly displayed independent coordinate draws.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian.Cartesian

open scoped BigOperators

noncomputable section

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

def mean (p : X → ℝ) (f : X → ℝ) : ℝ := ∑ x, p x * f x

def tupleWeight (p : X → ℝ) {k : ℕ} (xs : Fin k → X) : ℝ := ∏ i, p (xs i)

def jointWeight (p : X → ℝ) (q : Y → ℝ) (xy : X × Y) : ℝ := p xy.1 * q xy.2

theorem mean_nonneg (p f : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ mean p f := Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (hf x))

theorem mean_comm (p : X → ℝ) (q : Y → ℝ) (f : X → Y → ℝ) :
    mean p (fun x => mean q (f x)) = mean q (fun y => mean p (fun x => f x y)) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem mean_jointWeight (p : X → ℝ) (q : Y → ℝ) (f : X × Y → ℝ) :
    mean (jointWeight p q) f = mean p (fun x => mean q (fun y => f (x, y))) := by
  simp only [mean, jointWeight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

omit [Fintype X] in
theorem tupleWeight_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) {k : ℕ} (xs : Fin k → X) :
    0 ≤ tupleWeight p xs := Finset.prod_nonneg (fun i _ => hp (xs i))

theorem sum_tupleWeight (p : X → ℝ) (k : ℕ) :
    (∑ xs : Fin k → X, tupleWeight p xs) = (∑ x, p x) ^ k :=
  (Fintype.sum_pow p k).symm

theorem sum_jointWeight (p : X → ℝ) (q : Y → ℝ) :
    (∑ xy : X × Y, jointWeight p q xy) = (∑ x, p x) * ∑ y, q y := by
  simp only [jointWeight, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]

theorem mean_tuple_product (p f : X → ℝ) (k : ℕ) :
    mean (tupleWeight p) (fun xs : Fin k → X => ∏ i, f (xs i)) = mean p f ^ k := by
  rw [mean, mean, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro xs _
  exact (Finset.prod_mul_distrib : _ = _).symm

/-- Jensen's inequality for finite probability weights. -/
theorem mean_pow_le (p f : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (hf : ∀ x, 0 ≤ f x) (k : ℕ) (hk : 1 ≤ k) :
    mean p f ^ k ≤ mean p (fun x => f x ^ k) := by
  have h := (convexOn_rpow (by exact_mod_cast hk : (1 : ℝ) ≤ k)).map_sum_le
    (t := Finset.univ) (w := p) (p := f) (fun x _ => hp x) hsum (fun x _ => hf x)
  simpa only [mean, smul_eq_mul, Real.rpow_natCast] using h

/-- Replicating one coordinate raises a density to at most the corresponding
power. This is the one-coordinate step in the Cartesian grid inequality. -/
theorem density_pow_le_clone (p : X → ℝ) (q : Y → ℝ) (f : X → Y → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) (hqsum : ∑ y, q y = 1)
    (hf : ∀ x y, 0 ≤ f x y) (k : ℕ) (hk : 1 ≤ k) :
    mean p (fun x => mean q (f x)) ^ k ≤
      mean (tupleWeight p) (fun xs : Fin k → X => mean q (fun y => ∏ i, f (xs i) y)) := by
  rw [mean_comm p q f]
  calc
    mean q (fun y => mean p (fun x => f x y)) ^ k ≤
        mean q (fun y => mean p (fun x => f x y) ^ k) :=
      mean_pow_le q _ hq hqsum (fun y => mean_nonneg p _ hp (fun x => hf x y)) k hk
    _ = mean q (fun y => mean (tupleWeight p) (fun xs : Fin k → X => ∏ i, f (xs i) y)) := by
      congr 1
      funext y
      exact (mean_tuple_product p (fun x => f x y) k).symm
    _ = _ := (mean_comm (tupleWeight p) q _).symm

/-- Density of complete `k` by `k` by `k` grids under independent axis draws. -/
def gridDensity3 (p : X → ℝ) (q : Y → ℝ) (r : Z → ℝ) (f : X → Y → Z → ℝ) (k : ℕ) : ℝ :=
  mean (tupleWeight p) (fun xs : Fin k → X =>
    mean (tupleWeight q) (fun ys : Fin k → Y =>
      mean (tupleWeight r) (fun zs : Fin k → Z =>
        ∏ c : Fin k, ∏ b : Fin k, ∏ a : Fin k, f (xs a) (ys b) (zs c))))

/-- Three repeated Jensen steps give the complete-grid density estimate.
For an indicator of a dense set this is the probability that every grid
vertex belongs to that set. Repeated anchors are allowed at this stage. -/
theorem density_pow_cube_le_gridDensity3
    (p : X → ℝ) (q : Y → ℝ) (r : Z → ℝ) (f : X → Y → Z → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) (hr : ∀ z, 0 ≤ r z)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ y, q y = 1) (hrsum : ∑ z, r z = 1)
    (hf : ∀ x y z, 0 ≤ f x y z) (k : ℕ) (hk : 1 ≤ k) :
    mean p (fun x => mean q (fun y => mean r (f x y))) ^ (k ^ 3) ≤
      gridDensity3 p q r f k := by
  let d0 := mean p (fun x => mean q (fun y => mean r (f x y)))
  let d1 := mean (tupleWeight p) (fun xs : Fin k → X =>
    mean q (fun y => mean r (fun z => ∏ a : Fin k, f (xs a) y z)))
  let d2 := mean (tupleWeight p) (fun xs : Fin k → X =>
    mean (tupleWeight q) (fun ys : Fin k → Y =>
      mean r (fun z => ∏ b : Fin k, ∏ a : Fin k, f (xs a) (ys b) z)))
  have hd0 : 0 ≤ d0 := mean_nonneg p _ hp (fun x =>
    mean_nonneg q _ hq (fun y => mean_nonneg r _ hr (hf x y)))
  have h1 : d0 ^ k ≤ d1 := by
    have h := density_pow_le_clone p (jointWeight q r) (fun x yz => f x yz.1 yz.2)
      hp (fun yz => mul_nonneg (hq yz.1) (hr yz.2))
      (by rw [sum_jointWeight, hqsum, hrsum, one_mul]) (fun x yz => hf x yz.1 yz.2) k hk
    simpa only [mean_jointWeight] using h
  have h2 : d1 ^ k ≤ d2 := by
    have h := density_pow_le_clone q (jointWeight (tupleWeight p) r)
      (fun y xz => ∏ a : Fin k, f (xz.1 a) y xz.2)
      hq (fun xz => mul_nonneg (tupleWeight_nonneg p hp xz.1) (hr xz.2))
      (by rw [sum_jointWeight, sum_tupleWeight, hpsum, hrsum, one_pow, one_mul])
      (fun y xz => Finset.prod_nonneg (fun a _ => hf (xz.1 a) y xz.2)) k hk
    simp only [mean_jointWeight] at h
    have hleft : mean q (fun y => mean (tupleWeight p) (fun xs : Fin k → X =>
        mean r (fun z => ∏ a : Fin k, f (xs a) y z))) = d1 := by
      exact mean_comm q (tupleWeight p) _
    have hright : mean (tupleWeight q) (fun ys : Fin k → Y =>
        mean (tupleWeight p) (fun xs : Fin k → X =>
          mean r (fun z => ∏ b : Fin k, ∏ a : Fin k, f (xs a) (ys b) z))) = d2 := by
      exact mean_comm (tupleWeight q) (tupleWeight p) _
    rwa [hleft, hright] at h
  have h3 : d2 ^ k ≤ gridDensity3 p q r f k := by
    have h := density_pow_le_clone r (jointWeight (tupleWeight p) (tupleWeight q))
      (fun z xy => ∏ b : Fin k, ∏ a : Fin k, f (xy.1 a) (xy.2 b) z)
      hr (fun xy => mul_nonneg (tupleWeight_nonneg p hp xy.1) (tupleWeight_nonneg q hq xy.2))
      (by rw [sum_jointWeight, sum_tupleWeight, sum_tupleWeight, hpsum, hqsum, one_pow, one_mul])
      (fun z xy => Finset.prod_nonneg (fun b _ => Finset.prod_nonneg (fun a _ =>
        hf (xy.1 a) (xy.2 b) z))) k hk
    simp only [mean_jointWeight] at h
    have hleft : mean r (fun z => mean (tupleWeight p) (fun xs : Fin k → X =>
        mean (tupleWeight q) (fun ys : Fin k → Y =>
          ∏ b : Fin k, ∏ a : Fin k, f (xs a) (ys b) z))) = d2 := by
      rw [mean_comm r (tupleWeight p)]
      congr 1
      funext xs
      exact mean_comm r (tupleWeight q) _
    have hright : mean (tupleWeight r) (fun zs : Fin k → Z =>
        mean (tupleWeight p) (fun xs : Fin k → X =>
          mean (tupleWeight q) (fun ys : Fin k → Y =>
            ∏ c : Fin k, ∏ b : Fin k, ∏ a : Fin k, f (xs a) (ys b) (zs c)))) =
        gridDensity3 p q r f k := by
      rw [mean_comm (tupleWeight r) (tupleWeight p)]
      congr 1
      funext xs
      exact mean_comm (tupleWeight r) (tupleWeight q) _
    rwa [hleft, hright] at h
  have h12 : (d0 ^ k) ^ k ≤ d2 := (pow_le_pow_left₀ (pow_nonneg hd0 k) h1 k).trans h2
  have h123 : ((d0 ^ k) ^ k) ^ k ≤ gridDensity3 p q r f k :=
    (pow_le_pow_left₀ (pow_nonneg (pow_nonneg hd0 k) k) h12 k).trans h3
  simpa only [← pow_mul, show k * k * k = k ^ 3 by ring] using h123

/-- After excluding a small set of bad anchors, one good anchor retains a
fixed fraction of the complete-grid probability as target density. -/
theorem exists_good_anchor_with_dense_targets
    (p : X → ℝ) (q : Y → ℝ) (f : X → Y → ℝ) (good : X → Prop) [DecidablePred good]
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ y, q y = 1)
    (hf : ∀ x y, f x y ≤ 1) (a b : ℝ) (hba : b < a)
    (hdensity : a ≤ mean p (fun x => mean q (f x)))
    (hbad : mean p (fun x => if good x then 0 else 1) ≤ b) :
    ∃ x, good x ∧ (a - b) / 2 ≤ mean q (f x) := by
  classical
  by_contra! h
  have hθ : 0 < (a - b) / 2 := by linarith
  have hpoint (x : X) : mean q (f x) ≤ (a - b) / 2 + (if good x then 0 else 1) := by
    by_cases hx : good x
    · simpa only [hx, ↓reduceIte, add_zero] using (h x hx).le
    · have hf' : mean q (f x) ≤ 1 := by
        calc
          mean q (f x) ≤ ∑ y, q y * 1 :=
            Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hf x y) (hq y))
          _ = 1 := by simpa only [mul_one] using hqsum
      simp only [hx, ↓reduceIte]
      linarith
  have htotal : mean p (fun x => mean q (f x)) ≤
      (a - b) / 2 + mean p (fun x => if good x then 0 else 1) := by
    calc
      mean p (fun x => mean q (f x)) ≤
          ∑ x, p x * ((a - b) / 2 + (if good x then 0 else 1)) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hp x))
      _ = _ := by
        simp only [mean, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hpsum, one_mul]
  linarith

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian.Cartesian
