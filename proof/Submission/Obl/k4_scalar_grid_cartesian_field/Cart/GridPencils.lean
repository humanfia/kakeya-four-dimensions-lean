-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/GridPencils.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.CartesianCells
import Submission.Lib.K4IncidenceWitnesses

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set

/-- A regular finite coordinate grid has the pencil cap required by the
Cartesian sampler, including the discretization error at the endpoints. -/
theorem regular_grid_pencil_count (n : ℕ) (origin step radius center : ℝ)
    (hstep : 0 < step) (hradius : 0 ≤ radius) :
    ((Finset.univ.filter (fun i : Fin n => |origin + step*(i : ℝ) - center| < radius)).card : ℝ) ≤
      4 * radius / step + 3 := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => |origin + step*(i : ℝ) - center| < radius)
  let code : Fin n → Fin 1 → ℤ := fun i _ => ((i : ℕ) : ℤ)
  have hinj : Function.Injective code := by
    intro i j hij
    apply Fin.ext
    have h := congrFun hij 0
    change ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) at h
    exact_mod_cast h
  have hdiam : ∀ p ∈ S.image code, ∀ q ∈ S.image code, ∀ k,
      |(p k : ℝ) - (q k : ℝ)| ≤ 2 * radius / step := by
    intro p hp q hq k
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    change |(i : ℝ) - (j : ℝ)| ≤ 2 * radius / step
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have htri := abs_sub_le (origin + step*(i : ℝ)) center (origin + step*(j : ℝ))
    rw [abs_sub_comm center] at htri
    have heq : origin + step*(i : ℝ) - (origin + step*(j : ℝ)) =
        step*((i : ℝ)-(j : ℝ)) := by ring
    rw [heq, abs_mul, abs_of_pos hstep] at htri
    apply (le_div_iff₀ hstep).mpr
    nlinarith
  have hbound := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter
    (S.image code) (show 0 ≤ 2 * radius / step by positivity) hdiam
  rw [Finset.card_image_of_injective _ hinj] at hbound
  simpa only [Fintype.card_fin, pow_one, show 2*(2*radius/step)+3 = 4*radius/step+3 by ring]
    using hbound

theorem regular_grid_pencil_probability (n : ℕ) (origin step radius center : ℝ)
    (hstep : 0 < step) (hradius : 0 ≤ radius) :
    gridMean (finiteUniformWeights (Fin n))
      (fun i => if |origin + step*(i : ℝ) - center| < radius then 1 else 0) ≤
      (4 * radius / step + 3) / n := by
  classical
  rw [gridMean_uniform, Finset.sum_boole]
  have h := regular_grid_pencil_count n origin step radius center hstep hradius
  simpa only [Fintype.card_fin, div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (n : ℝ)⁻¹)

/-- A grid spanning unit length has thin-pencil probability at most
seven times the radius once its step is smaller than that radius. -/
theorem regular_grid_pencil_small (n : ℕ) (origin step radius center : ℝ)
    (hstep : 0 < step) (hradius : 0 ≤ radius)
    (hspan : 1 ≤ (n : ℝ)*step) (hmesh : step ≤ radius) :
    gridMean (finiteUniformWeights (Fin n))
      (fun i => if |origin + step*(i : ℝ) - center| < radius then 1 else 0) ≤
      7 * radius := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hspan
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  apply (regular_grid_pencil_probability n origin step radius center hstep hradius).trans
  apply (div_le_iff₀ hn).mpr
  have heq : 4*radius/step+3 = (4*radius+3*step)/step := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ hstep).mpr
  calc
    4*radius+3*step ≤ 7*radius := by linarith
    _ ≤ 7*radius*((n : ℝ)*step) := by
      have h := mul_le_mul_of_nonneg_left hspan (by positivity : 0 ≤ 7*radius)
      simpa only [mul_one] using h
    _ = _ := by ring

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
