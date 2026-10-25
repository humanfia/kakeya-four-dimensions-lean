/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/LiftAtlas.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.Remainder
import Submission.Obl.k4_native_finite_terminal_atlas_lift.AffineGeometry
import Submission.Obl.k4_native_finite_terminal_atlas_lift.FrameComposition
import Submission.Obl.k4_native_finite_terminal_atlas_lift.DyadicComposition
import Submission.Obl.k4_native_finite_terminal_atlas_lift.NativeTests
import Submission.Obl.k4_native_finite_terminal_atlas_lift.ProductTransport

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

namespace Remainder

variable {p q : Data} {r h w : ℝ} (rem : Remainder p q r h w)

abbrev parentIndex (k : ℕ) (b : Fin (q.W k)) : Fin (rem.parent k).C :=
  rem.worlds k b

noncomputable abbrev timeLength (k : ℕ) : ℝ := ((2 : ℝ) ^ (rem.parent k).T)⁻¹

noncomputable abbrev initialTime (k : ℕ) (b : Fin (q.W k)) : ℝ :=
  ((rem.parent k).j (rem.parentIndex k b) : ℝ) / (2 : ℝ) ^ (rem.parent k).T

theorem timeLength_pos (k : ℕ) : 0 < rem.timeLength k := by unfold timeLength; positivity

theorem coefficient_map_formula (k : ℕ) (b : Fin (q.W k)) :
    (rem.coefficient_map k b : Trajectory → Trajectory) =
      normalizedTrajectory (rem.initialTime k b) (rem.timeLength k)
        ((rem.parent k).c (rem.parentIndex k b)) ((rem.parent k).u (rem.parentIndex k b))
        ((rem.parent k).Q (rem.parentIndex k b))⁻¹ := by
  apply coefficient_map_eq_normalized
  · exact rem.index_preserved k b
  · intro l τ
    simpa only [initialTime, timeLength, parentIndex, div_eq_mul_inv, mul_comm] using
      rem.planar_map k b l τ
  · intro l τ
    simpa only [initialTime, timeLength, parentIndex, div_eq_mul_inv, mul_comm] using
      rem.hidden_map k b l τ

theorem selected_pullback_equiv (k : ℕ) (b : Fin (q.W k)) {z : Incidence}
    (hz : z ∈ q.E k b) :
    (normalizedIncidenceEquiv (rem.coefficient_map k b) (rem.initialTime k b)
      (rem.timeLength k) (rem.timeLength_pos k).ne').symm z ∈
      (rem.parent k).F (rem.parentIndex k b) := by
  rw [normalizedIncidenceEquiv_symm_apply]
  simpa only [initialTime, timeLength, parentIndex, div_eq_mul_inv, mul_comm] using
    rem.selected_pullback k b z hz

/-- The complete original finite atlas obtained by composing a child system
through the retained parent frames. The number of child labels is unchanged. -/
noncomputable abbrev liftAtlas (k : ℕ) (a : Atlas q k) : Atlas p (rem.φ k) where
  κ := 2 * (rem.parent k).κ * a.κ
  T := (rem.parent k).T + a.T
  C := a.C
  γ b := (rem.parent k).γ (rem.parentIndex k (a.γ b))
  j b := compositeBlock ((rem.parent k).j (rem.parentIndex k (a.γ b))) (a.j b)
  c b := compositeCenter (rem.initialTime k (a.γ b)) (rem.timeLength k)
    ((rem.parent k).c (rem.parentIndex k (a.γ b))) (a.c b)
    ((rem.parent k).u (rem.parentIndex k (a.γ b))) (a.u b)
    ((rem.parent k).Q (rem.parentIndex k (a.γ b)))
  u b := compositeVelocity (rem.timeLength k) ((rem.parent k).u (rem.parentIndex k (a.γ b)))
    (a.u b) ((rem.parent k).Q (rem.parentIndex k (a.γ b)))
  Q b := (rem.parent k).Q (rem.parentIndex k (a.γ b)) * a.Q b
  R b := liftedTest (δ (p.N (rem.φ k)) r) (rem.initialTime k (a.γ b)) (rem.timeLength k)
    ((rem.parent k).c (rem.parentIndex k (a.γ b)))
    ((rem.parent k).u (rem.parentIndex k (a.γ b)))
    ((rem.parent k).Q (rem.parentIndex k (a.γ b)))⁻¹ (a.R b)
  A b := (rem.parent k).A (rem.parentIndex k (a.γ b)) ∩ rem.coefficient_map k (a.γ b) ⁻¹' a.A b
  F b := normalizedIncidenceEquiv (rem.coefficient_map k (a.γ b))
    (rem.initialTime k (a.γ b)) (rem.timeLength k) (rem.timeLength_pos k).ne' ⁻¹' a.F b

end Remainder

end Submission.Obl.k4_native_finite_terminal_atlas_lift
