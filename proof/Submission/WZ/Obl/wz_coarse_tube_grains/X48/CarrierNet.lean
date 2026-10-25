-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.X48.CarrierNet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.X48.Defs

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains.X48

open Set Metric

/-- Moving the start and direction by a total of at most `R - δ` puts the
whole fine tube in the new carrier. -/
theorem tube_containment_of_parameters {δ R : ℝ} {x v y w : V}
    (h : δ + dist x y + dist v w ≤ R) : T δ x v ⊆ T R y w := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hseg : y + t • w ∈ segment ℝ y (y + w) := by
    rw [segment_eq_image']
    exact ⟨t, ht, by simp⟩
  have hd : dist (x + t • v) (y + t • w) ≤ dist x y + dist v w := by
    simp only [dist_eq_norm]
    calc
      _ = ‖(x - y) + t • (v - w)‖ := by congr 1; module
      _ ≤ ‖x - y‖ + ‖t • (v - w)‖ := norm_add_le _ _
      _ ≤ ‖x - y‖ + ‖v - w‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht.1]
        exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg (v - w)) ht.2)
  exact mem_thickening_iff.mpr ⟨y + t • w, hseg,
    lt_of_le_of_lt (dist_triangle p (x + t • v) (y + t • w)) (by linarith)⟩

/-- A fixed finite collection of half-radius carriers contains every tube
of radius at most `1/100` whose start lies in the unit ball. All carriers
have unit direction. The number of carriers is independent of the fine
radius and of the finite tube family. -/
theorem exists_finite_half_carriers :
    ∃ (K : ℕ), 0 < K ∧ ∃ (y w : Fin K → V),
      (∀ k, ‖w k‖ = 1) ∧ ∀ (δ : ℝ), δ ≤ 1 / 100 →
      ∀ (x v : V), ‖x‖ ≤ 1 → ‖v‖ = 1 → ∃ k, T δ x v ⊆ T (1 / 2) (y k) (w k) := by
  classical
  let C : Set (V × V) := closedBall (0 : V) 1 ×ˢ sphere (0 : V) 1
  have hC : IsCompact C := (isCompact_closedBall (0 : V) 1).prod (isCompact_sphere (0 : V) 1)
  obtain ⟨D, hDC, hDfin, hcover⟩ := hC.finite_cover_balls (by norm_num : (0 : ℝ) < 1 / 8)
  have hCne : C.Nonempty := by
    refine ⟨(0, EuclideanSpace.single (0 : Fin 3) 1), ?_⟩
    simp [C]
  obtain ⟨a, ha⟩ := hCne
  obtain ⟨b, hb, _⟩ := mem_iUnion₂.mp (hcover ha)
  letI : Fintype D := hDfin.fintype
  let e : Fin (Fintype.card D) ≃ D := (Fintype.equivFin D).symm
  refine ⟨Fintype.card D, Fintype.card_pos_iff.mpr ⟨⟨b, hb⟩⟩,
    (fun k => (e k).val.1), (fun k => (e k).val.2), ?_, ?_⟩
  · intro k
    simpa only [mem_sphere, dist_zero_right] using (hDC (e k).property).2
  · intro δ hδ x v hx hv
    have hpair : (x, v) ∈ C :=
      ⟨mem_closedBall_zero_iff.mpr hx, by simpa only [mem_sphere, dist_zero_right] using hv⟩
    obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp (hcover hpair)
    refine ⟨e.symm ⟨c, hc⟩, ?_⟩
    simp only [Equiv.apply_symm_apply]
    apply tube_containment_of_parameters
    have hdist : dist (x, v) c < (1 / 8 : ℝ) := mem_ball.mp hpc
    rw [Prod.dist_eq, max_lt_iff] at hdist
    have hx' : dist x c.1 < (1 / 8 : ℝ) := hdist.1
    have hv' : dist v c.2 < (1 / 8 : ℝ) := hdist.2
    linarith

end WangZahlLot.Obl.wz_coarse_tube_grains.X48
