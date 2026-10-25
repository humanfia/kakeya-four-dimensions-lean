-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.NarrowGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.SubprismGeometry
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PrismCrossing

/-! Extending a point cap to its natural tube-intersection length. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open wz_measurable_angular_selection (pd)

/-- Tubes through one point in a small angular cap cross a common prism of
length `10*d/theta`; their local pieces lie in its interior core. -/
theorem narrow_cap_prism {d θ : ℝ} (hd : 0 < d) (hθ : 0 < θ)
    (hθsmall : θ ≤ 1/10000) (p u : V) (hu : ‖u‖ = 1) :
    ∃ e : V ≃ₗᵢ[ℝ] V,
      ∀ x v : V, ‖v‖ = 1 → p ∈ T d x v → pd v u ≤ 2*θ →
        40*(d/θ) ≤ dist p x → 40*(d/θ) ≤ dist p (x+v) →
        Crosses d (10000*d) (10000*d) (10*(d/θ)) x v p e ∧
        T d x v ∩ ball p ((d/θ)/2) ⊆
          P ((10000*d)/8) ((10000*d)/8) ((10*(d/θ))/8) p e := by
  obtain ⟨e, he⟩ := wz_broad_grains_initialization.frame_last_of_unit hu
  have he2 := frame_last_inner he
  refine ⟨e, ?_⟩
  intro x v hv hp hang hleft hright
  have hell : 0 < d/θ := div_pos hd hθ
  have hshort (j : Fin 3) (hj : j ≠ 2) : |e v j| ≤ 2*θ :=
    (frame_short_le_pd e hu he2 j hj).trans hang
  have hlong : 1/2 ≤ |e v 2| := abs_long_of_transverse_small e hv
    ((hshort 0 (by decide)).trans (by linarith)) ((hshort 1 (by decide)).trans (by linarith))
  have hside : 10000*d ≤ 10*(d/θ) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hθ).mpr
    nlinarith
  have hprod (j : Fin 3) (hj : j ≠ 2) : (10*(d/θ))*|e v j| ≤ (10000*d)/100 := by
    have hh := mul_le_mul_of_nonneg_left (hshort j hj) (show 0 ≤ 10*(d/θ) by positivity)
    have heq : 10*(d/θ)*(2*θ) = 20*d := by field_simp; ring
    rw [heq] at hh
    linarith
  refine ⟨prism_crosses_of_core_abs hd (by positivity) le_rfl hside (by linarith)
    e hv hlong (hprod 0 (by decide)) (hprod 1 (by decide)) hp ?_
    (by linarith) (by linarith), ?_⟩
  · simp only [P, sub_self, map_zero, PiLp.zero_apply, abs_zero, mem_setOf_eq]
    exact ⟨by positivity, by positivity, by positivity⟩
  · intro q hq
    have hnorm : ‖q-p‖ ≤ (d/θ)/2 := by
      exact (show dist q p < (d/θ)/2 from hq.2).le
    have hin₀ : |inner ℝ v (q-p)| ≤ ‖q-p‖ := by
      simpa only [hv, one_mul] using abs_real_inner_le_norm v (q-p)
    have hin := hin₀.trans hnorm
    have hsmall (j : Fin 3) (hj : j ≠ 2) : |e (q-p) j| ≤ 5*d := by
      have herr := tube_projected_coordinate_error hv e hp hq.1 j
      have hmul := mul_le_mul hin (hshort j hj) (abs_nonneg _) (by positivity : 0 ≤ (d/θ)/2)
      have heq : (d/θ)/2*(2*θ) = d := by field_simp
      rw [heq, ← abs_mul] at hmul
      have hh := abs_sub_abs_le_abs_sub (e (q-p) j) (inner ℝ v (q-p)*e v j)
      linarith
    have hlast₀ : |e (q-p) 2| ≤ ‖q-p‖ := by
      simpa only [e.norm_map] using wz_move_two_long_grains_gain.abs_coord_le_norm (e (q-p)) 2
    have hlast := hlast₀.trans hnorm
    exact ⟨by linarith [hsmall 0 (by decide)], by linarith [hsmall 1 (by decide)], by linarith⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
