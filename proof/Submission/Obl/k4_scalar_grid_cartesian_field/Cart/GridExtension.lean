-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/GridExtension.lean;
-- only the namespace was renamed into o230's.
import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

noncomputable def cartesianGridExtension {X Y : Type*}
    (v : X → ℝ) (w : Y → ℝ) (f : X → Y → ℝ) : ℝ → ℝ → ℝ := by
  classical
  exact fun t u => if hx : ∃ x, v x=t then
    if hy : ∃ y, w y=u then f (Classical.choose hx) (Classical.choose hy) else 0 else 0

theorem cartesianGridExtension_at {X Y : Type*}
    (v : X → ℝ) (w : Y → ℝ) (hv : Function.Injective v) (hw : Function.Injective w)
    (f : X → Y → ℝ) (x : X) (y : Y) :
    cartesianGridExtension v w f (v x) (w y) = f x y := by
  classical
  have hx : ∃ x', v x'=v x := ⟨x,rfl⟩
  have hy : ∃ y', w y'=w y := ⟨y,rfl⟩
  have hxc : Classical.choose hx=x := hv (Classical.choose_spec hx)
  have hyc : Classical.choose hy=y := hw (Classical.choose_spec hy)
  simp only [cartesianGridExtension, dite_eq_left hx, dite_eq_left hy, hxc, hyc]

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
