/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/CartesianVectorField.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Shared-component construction: x0511/f3c3c1bc9c177be75b864fc46a55e921a9da6d27, CartesianVectorField.lean.
Extends the scalar construction of x0212/4049ef60, CartesianInterpolation.lean,
using accepted original grid sampling and tensor interpolation at common anchors.
-/

import Submission.Lib.K4ScalarActualSwitching.GridSampling
import Submission.Lib.K4ScalarActualSwitching.TensorInterpolation

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MvPolynomial
open Submission.Lib.K4ScalarActualSwitching

/-- A dense retained Cartesian grid, with an actual polynomial fit on
each of its fibers, supplies one bounded polynomial field fitting a
positive fraction of the original coordinate law. -/
theorem exists_cartesian_polynomial_fields {ι X Y : Type*} [Fintype X] [Fintype Y]
    (D : ℕ) (p : X → ℝ) (q : Y → ℝ) (R : X → Y → Prop)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (v : X → ℝ) (w : Y → ℝ) (B gap Bx By η E H : ℝ)
    (hB : 0 ≤ B) (hgap : 0 < gap) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hη : 0 < η) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hv : ∀ x, |v x| ≤ B) (hw : ∀ y, |w y| ≤ B)
    (hthinX : ∀ z, gridMean p (fun x => if |v x - z| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ z, gridMean q (fun y => if |w y - z| < gap then 1 else 0) ≤ By)
    (hdensity : η ≤ gridMean p (fun x => gridMean q (fun y => gridFlag (R x y))))
    (hloss : ((D : ℝ) + 2)^2 * Bx + ((D : ℝ) + 2)^2 * By ≤ η^((D+2)^2) / 2)
    (f : ι → ℝ → ℝ → ℝ) (hvals : ∀ c x y, R x y → |f c (v x) (w y)| ≤ H)
    (hrows : ∀ c y, ∃ a : Polynomial ℝ, a.natDegree ≤ D ∧
      ∀ x, R x y → |f c (v x) (w y) - a.eval (v x)| ≤ E)
    (hcols : ∀ c x, ∃ a : Polynomial ℝ, a.natDegree ≤ D ∧
      ∀ y, R x y → |f c (v x) (w y) - a.eval (w y)| ≤ E) :
    let W := ((D : ℝ) + 1) * (2 * B / gap)^D
    ∃ P : ι → MvPolynomial (Fin 2) ℝ, (∀ c, (P c).totalDegree ≤ 2*D) ∧
      (∀ c, ∀ x y : ℝ, |x| ≤ B → |y| ≤ B → |eval ![x,y] (P c)| ≤ H * W^2) ∧
      η^((D+2)^2) / 2 ≤ gridMean p (fun x => gridMean q (fun y =>
        gridFlag (R x y ∧ ∀ c, |f c (v x) (w y) - eval ![v x,w y] (P c)| ≤ E*(1+2*W+W^2)))) := by
  classical
  dsimp only
  let W := ((D : ℝ) + 1) * (2 * B / gap)^D
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hcount : ((D + 1 + 1 : ℕ) : ℝ)^2 * Bx + ((D + 1 + 1 : ℕ) : ℝ)^2 * By ≤
      η^((D+1+1)*(D+1+1)) / 2 := by
    have hsum : (D : ℝ) + 1 + 1 = (D : ℝ) + 2 := by ring
    simpa only [Nat.cast_add, Nat.cast_one, hsum, pow_two] using hloss
  obtain ⟨a,b,hsepA,hsepB,hmass⟩ := exists_separated_original_grid_anchors (D+1) (D+1)
    p q R hp hp1 hq hq1 v w gap Bx By η hBx hBy hη hthinX hthinY hdensity hcount
  let Good : X → Y → Prop := fun x y => ∀ i j,
    R (Fin.snoc (α := fun _ : Fin (D+1+1) => X) a x i)
      (Fin.snoc (α := fun _ : Fin (D+1+1) => Y) b y j)
  change η^((D+1+1)*(D+1+1)) / 2 ≤ gridMean p (fun x => gridMean q
    (fun y => gridFlag (Good x y))) at hmass
  have hgood : ∃ x y, Good x y := by
    by_contra hn
    push Not at hn
    have hz : ∀ x y, gridFlag (Good x y) = 0 := by
      intro x y
      simp [gridFlag, hn x y]
    simp only [hz, gridMean, mul_zero, Finset.sum_const_zero] at hmass
    exact (not_le_of_gt (by positivity : 0 < η^((D+1+1)*(D+1+1)) / 2)) hmass
  obtain ⟨x₀,y₀,h₀⟩ := hgood
  have hanchor (i j : Fin (D+1)) : R (a i) (b j) := by
    simpa only [Fin.snoc_castSucc] using h₀ i.castSucc j.castSucc
  have hgoodparts (x : X) (y : Y) (h : Good x y) :
      R x y ∧ (∀ i, R (a i) y) ∧ (∀ i j, R (a i) (b j)) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Fin.snoc_last] using h (Fin.last (D+1)) (Fin.last (D+1))
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using h i.castSucc (Fin.last (D+1))
    · exact hanchor
  have hgoodrow (x : X) (y : Y) (h : Good x y) (i : Fin (D+1)) : R (a i) y :=
    (hgoodparts x y h).2.1 i
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
  let P : ι → MvPolynomial (Fin 2) ℝ := fun c =>
    tensorInterpolant (fun i => v (a i)) (fun j => w (b j)) (f c)
  have hweightsA (x : ℝ) (hx : |x| ≤ B) :
      (∑ i, |(Lagrange.basis Finset.univ (fun i => v (a i)) i).eval x|) ≤ W :=
    lagrange_weight_sum_bound _ B gap hB hgap (fun i => hv (a i)) hsepA x hx
  have hweightsB (y : ℝ) (hy : |y| ≤ B) :
      (∑ j, |(Lagrange.basis Finset.univ (fun j => w (b j)) j).eval y|) ≤ W :=
    lagrange_weight_sum_bound _ B gap hB hgap (fun j => hw (b j)) hsepB y hy
  have hfit (c : ι) (x : X) (y : Y) (h : Good x y) :
      |f c (v x) (w y) - eval ![v x,w y] (P c)| ≤ E*(1+2*W+W^2) := by
    have hrow : ∃ u : Polynomial ℝ, u.natDegree ≤ D ∧
        |f c (v x) (w y) - u.eval (v x)| ≤ E ∧
        ∀ i, |f c (v (a i)) (w y) - u.eval (v (a i))| ≤ E := by
      obtain ⟨u,hu,hufit⟩ := hrows c y
      exact ⟨u,hu,hufit x (hgoodparts x y h).1, fun i => hufit (a i) (hgoodrow x y h i)⟩
    have hcol (i : Fin (D+1)) : ∃ u : Polynomial ℝ, u.natDegree ≤ D ∧
        |f c (v (a i)) (w y) - u.eval (w y)| ≤ E ∧
        ∀ j, |f c (v (a i)) (w (b j)) - u.eval (w (b j))| ≤ E := by
      obtain ⟨u,hu,hufit⟩ := hcols c (a i)
      exact ⟨u,hu,hufit y (hgoodrow x y h i), fun j => hufit (b j) (hanchor i j)⟩
    rw [pow_two]
    apply (tensor_interpolation_error _ _ hinjA hinjB (f c) (v x) (w y) E hE hrow hcol).trans
    gcongr
    · exact hweightsA (v x) (hv x)
    · exact hweightsA (v x) (hv x)
    · exact hweightsB (w y) (hw y)
  refine ⟨P, (fun c => totalDegree_tensorInterpolant _ _ hinjA hinjB (f c)), ?_, ?_⟩
  · intro c x y hx hy
    apply (tensor_interpolant_eval_bound _ _ (f c) H hH (fun i j => hvals c _ _ (hanchor i j)) x y).trans
    calc
      _ ≤ H * W * W := by gcongr; exact hweightsA x hx; exact hweightsB y hy
      _ = _ := by ring
  · have hmono : gridMean p (fun x => gridMean q (fun y => gridFlag (Good x y))) ≤
        gridMean p (fun x => gridMean q (fun y => gridFlag
          (R x y ∧ ∀ c, |f c (v x) (w y) - eval ![v x,w y] (P c)| ≤ E*(1+2*W+W^2)))) := by
      apply gridMean_mono hp
      intro x
      apply gridMean_mono hq
      intro y
      apply gridFlag_mono
      intro h
      exact ⟨(hgoodparts x y h).1, fun c => hfit c x y h⟩
    simpa only [pow_two] using hmass.trans hmono


/-- The scalar application is a specialization of the common-component construction. -/
theorem exists_cartesian_polynomial_field {X Y : Type*} [Fintype X] [Fintype Y]
    (D : ℕ) (p : X → ℝ) (q : Y → ℝ) (R : X → Y → Prop)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (v : X → ℝ) (w : Y → ℝ) (B gap Bx By η E H : ℝ)
    (hB : 0 ≤ B) (hgap : 0 < gap) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hη : 0 < η) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hv : ∀ x, |v x| ≤ B) (hw : ∀ y, |w y| ≤ B)
    (hthinX : ∀ z, gridMean p (fun x => if |v x - z| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ z, gridMean q (fun y => if |w y - z| < gap then 1 else 0) ≤ By)
    (hdensity : η ≤ gridMean p (fun x => gridMean q (fun y => gridFlag (R x y))))
    (hloss : ((D : ℝ) + 2)^2 * Bx + ((D : ℝ) + 2)^2 * By ≤ η^((D+2)^2) / 2)
    (f : ℝ → ℝ → ℝ) (hvals : ∀ x y, R x y → |f (v x) (w y)| ≤ H)
    (hrows : ∀ y, ∃ a : Polynomial ℝ, a.natDegree ≤ D ∧
      ∀ x, R x y → |f (v x) (w y) - a.eval (v x)| ≤ E)
    (hcols : ∀ x, ∃ a : Polynomial ℝ, a.natDegree ≤ D ∧
      ∀ y, R x y → |f (v x) (w y) - a.eval (w y)| ≤ E) :
    let W := ((D : ℝ) + 1) * (2 * B / gap)^D
    ∃ P : MvPolynomial (Fin 2) ℝ, P.totalDegree ≤ 2*D ∧
      (∀ x y : ℝ, |x| ≤ B → |y| ≤ B → |eval ![x,y] P| ≤ H * W^2) ∧
      η^((D+2)^2) / 2 ≤ gridMean p (fun x => gridMean q (fun y =>
        gridFlag (R x y ∧ |f (v x) (w y) - eval ![v x,w y] P| ≤ E*(1+2*W+W^2)))) := by
  classical
  dsimp only
  obtain ⟨P, hdegree, hnorm, hsuccess⟩ := exists_cartesian_polynomial_fields (ι := Unit)
    D p q R hp hp1 hq hq1 v w B gap Bx By η E H hB hgap hBx hBy hη hE hH hv hw
    hthinX hthinY hdensity hloss (fun _ => f) (fun _ => hvals) (fun _ => hrows) (fun _ => hcols)
  refine ⟨P Unit.unit, hdegree _, hnorm _, ?_⟩
  apply hsuccess.trans
  apply gridMean_mono hp
  intro x
  apply gridMean_mono hq
  intro y
  apply gridFlag_mono
  intro h
  exact ⟨h.1, h.2 Unit.unit⟩

end Submission.Lib.K4ScalarCoreTools.Finalization
