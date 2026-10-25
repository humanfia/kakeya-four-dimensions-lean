-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/CartesianInterpolation.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.GridSampling
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.TensorInterpolation

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MvPolynomial

/-- A dense retained Cartesian grid, with an actual polynomial fit on
each of its fibers, supplies one bounded polynomial field fitting a
positive fraction of the original coordinate law. -/
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
  let P := tensorInterpolant (fun i => v (a i)) (fun j => w (b j)) f
  have hweightsA (x : ℝ) (hx : |x| ≤ B) :
      (∑ i, |(Lagrange.basis Finset.univ (fun i => v (a i)) i).eval x|) ≤ W :=
    lagrange_weight_sum_bound _ B gap hB hgap (fun i => hv (a i)) hsepA x hx
  have hweightsB (y : ℝ) (hy : |y| ≤ B) :
      (∑ j, |(Lagrange.basis Finset.univ (fun j => w (b j)) j).eval y|) ≤ W :=
    lagrange_weight_sum_bound _ B gap hB hgap (fun j => hw (b j)) hsepB y hy
  have hfit (x : X) (y : Y) (h : Good x y) :
      |f (v x) (w y) - eval ![v x,w y] P| ≤ E*(1+2*W+W^2) := by
    have hrow : ∃ u : Polynomial ℝ, u.natDegree ≤ D ∧
        |f (v x) (w y) - u.eval (v x)| ≤ E ∧
        ∀ i, |f (v (a i)) (w y) - u.eval (v (a i))| ≤ E := by
      obtain ⟨u,hu,hufit⟩ := hrows y
      exact ⟨u,hu,hufit x (hgoodparts x y h).1, fun i => hufit (a i) (hgoodrow x y h i)⟩
    have hcol (i : Fin (D+1)) : ∃ u : Polynomial ℝ, u.natDegree ≤ D ∧
        |f (v (a i)) (w y) - u.eval (w y)| ≤ E ∧
        ∀ j, |f (v (a i)) (w (b j)) - u.eval (w (b j))| ≤ E := by
      obtain ⟨u,hu,hufit⟩ := hcols (a i)
      exact ⟨u,hu,hufit y (hgoodrow x y h i), fun j => hufit (b j) (hanchor i j)⟩
    rw [pow_two]
    apply (tensor_interpolation_error _ _ hinjA hinjB f (v x) (w y) E hE hrow hcol).trans
    gcongr
    · exact hweightsA (v x) (hv x)
    · exact hweightsA (v x) (hv x)
    · exact hweightsB (w y) (hw y)
  refine ⟨P, totalDegree_tensorInterpolant _ _ hinjA hinjB f, ?_, ?_⟩
  · intro x y hx hy
    apply (tensor_interpolant_eval_bound _ _ f H hH (fun i j => hvals _ _ (hanchor i j)) x y).trans
    calc
      _ ≤ H * W * W := by gcongr; exact hweightsA x hx; exact hweightsB y hy
      _ = _ := by ring
  · have hmono : gridMean p (fun x => gridMean q (fun y => gridFlag (Good x y))) ≤
        gridMean p (fun x => gridMean q (fun y => gridFlag
          (R x y ∧ |f (v x) (w y) - eval ![v x,w y] P| ≤ E*(1+2*W+W^2)))) := by
      apply gridMean_mono hp
      intro x
      apply gridMean_mono hq
      intro y
      apply gridFlag_mono
      intro h
      exact ⟨(hgoodparts x y h).1,hfit x y h⟩
    simpa only [pow_two] using hmass.trans hmono

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
