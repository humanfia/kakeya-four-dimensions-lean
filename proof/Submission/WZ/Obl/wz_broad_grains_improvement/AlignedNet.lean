-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedNet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedGrid
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Extraction

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint)
open WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy (NetSeparated)

set_option maxHeartbeats 800000

abbrev AlignedColors := (Fin 3 → ZMod 100000000) × (Fin 3 → ZMod 100000000)

noncomputable def alignedGridCost : ℝ := Fintype.card AlignedColors

theorem alignedGridCost_pos : 0 < alignedGridCost := by
  exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr (inferInstance : Nonempty AlignedColors))

/-- A fixed fraction of any positively weighted aligned family can be assigned
by midpoint-direction cells to a separated net of unit carriers. -/
theorem aligned_grid_selection {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1/100000000)
    {L : ℕ} (x v : Fin L → V) {u : V} {h : ℝ}
    (hunit : ∀ j, ‖v j‖ = 1) (hcap : ∀ j, ‖v j-u‖ ≤ 1/10)
    (hmid : ∀ j, ‖axisMidpoint (x j) (v j)‖ ≤ 1)
    (halign : ∀ j, inner ℝ (v j) (axisMidpoint (x j) (v j)) = h)
    (F : Finset (Fin L)) (weight : Fin L → ℝ) (hmass : 0 < ∑ j ∈ F, weight j) :
    ∃ (S : Finset (Fin L)) (N : ℕ) (rep : Fin N → Fin L) (f : Fin L → Fin N),
      S ⊆ F ∧ 0 < N ∧ (∀ k, rep k ∈ S) ∧
      (∑ j ∈ F, weight j) ≤ alignedGridCost * ∑ j ∈ S, weight j ∧
      (∀ j ∈ S, alignedCell r (x j) (v j) =
        alignedCell r (x (rep (f j))) (v (rep (f j)))) ∧
      NetSeparated (10000*r) (x ∘ rep) (v ∘ rep) := by
  classical
  let ec : AlignedColors ≃ Fin (Fintype.card AlignedColors) := Fintype.equivFin _
  let color : Fin L → Fin (Fintype.card AlignedColors) :=
    fun j => ec (alignedColor r (x j) (v j))
  obtain ⟨k, hk⟩ := WangZahlLot.Obl.wz_move_two_dense_broad_prisms.weighted_scale_selection
    (Fintype.card_pos_iff.mpr (inferInstance : Nonempty AlignedColors)) F color weight
  let S := F.filter (fun j => color j = k)
  have hmassS : (∑ j ∈ F, weight j) ≤ alignedGridCost * ∑ j ∈ S, weight j := hk
  have hS : S.Nonempty := by
    by_contra hne
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Finset.sum_empty, mul_zero] at hmassS
    linarith
  let C := S.image (fun j => alignedCell r (x j) (v j))
  have hC : C.Nonempty := Finset.Nonempty.image hS _
  have hN : 0 < C.card := Finset.card_pos.mpr hC
  let e : C ≃ Fin C.card := C.equivFin
  have hex : ∀ cell : C, ∃ j ∈ S, alignedCell r (x j) (v j) = cell.1 := by
    intro cell
    exact Finset.mem_image.mp cell.2
  let rep₀ : C → Fin L := fun cell => (hex cell).choose
  have hrepS (cell : C) : rep₀ cell ∈ S := (hex cell).choose_spec.1
  have hrepcell (cell : C) : alignedCell r (x (rep₀ cell)) (v (rep₀ cell)) = cell.1 :=
    (hex cell).choose_spec.2
  let rep : Fin C.card → Fin L := rep₀ ∘ e.symm
  let f : Fin L → Fin C.card := fun j =>
    if hj : j ∈ S then e ⟨_, Finset.mem_image_of_mem _ hj⟩ else ⟨0,hN⟩
  refine ⟨S, C.card, rep, f, Finset.filter_subset _ _, hN,
    fun k => hrepS _, hmassS, ?_, ?_⟩
  · intro j hj
    simp only [f, dite_eq_left hj, rep, Function.comp_apply, Equiv.symm_apply_apply]
    exact (hrepcell ⟨alignedCell r (x j) (v j), Finset.mem_image_of_mem _ hj⟩).symm
  · intro j j' hjj'
    have hne : alignedCell r (x (rep j)) (v (rep j)) ≠
        alignedCell r (x (rep j')) (v (rep j')) := by
      change alignedCell r (x (rep₀ (e.symm j))) (v (rep₀ (e.symm j))) ≠
        alignedCell r (x (rep₀ (e.symm j'))) (v (rep₀ (e.symm j')))
      rw [hrepcell, hrepcell]
      exact fun he => hjj' (e.symm.injective (Subtype.ext he))
    have hcolor : alignedColor r (x (rep j)) (v (rep j)) =
        alignedColor r (x (rep j')) (v (rep j')) := by
      apply ec.injective
      exact (Finset.mem_filter.mp (hrepS (e.symm j))).2.trans
        (Finset.mem_filter.mp (hrepS (e.symm j'))).2.symm
    exact aligned_color_separated hr hr1 (hunit _) (hunit _) (hcap _) (hcap _)
      (hmid _) ((halign _).trans (halign _).symm) hcolor hne

/-- The separated net has precisely the overlap bound in the frozen cover. -/
theorem aligned_net_distinct {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1/100000000)
    {N : ℕ} {x v : Fin N → V} (hunit : ∀ j, ‖v j‖ = 1)
    (hnet : NetSeparated (10000*r) x v) : X (10000*r) N x v := by
  intro j k hjk
  rcases hnet j k hjk with hangle | hfar
  · exact WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.half_overlap_of_transverse
      (by positivity) (by linarith) (hunit j) (hunit k) hangle
  · exact WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.half_overlap_of_far hfar

end WangZahlLot.Obl.wz_broad_grains_improvement
