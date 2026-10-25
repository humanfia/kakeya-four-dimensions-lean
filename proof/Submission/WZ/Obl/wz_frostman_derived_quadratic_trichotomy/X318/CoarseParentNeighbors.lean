-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CoarseParentNeighbors.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.TubeNeighbors
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.ParentAdjacency

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file CoarseParentNeighbors.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization (ncard_fintype)

def UnorientedNear (r : ℝ) (v w : Space) : Prop := ‖v - w‖ ≤ r ∨ ‖v + w‖ ≤ r

lemma UnorientedNear.symm {r : ℝ} {v w : Space} (h : UnorientedNear r v w) :
    UnorientedNear r w v := by
  rcases h with h | h
  · exact Or.inl (by simpa only [norm_sub_rev] using h)
  · exact Or.inr (by simpa only [add_comm] using h)

lemma UnorientedNear.mono {r s : ℝ} {v w : Space}
    (h : UnorientedNear r v w) (hrs : r ≤ s) : UnorientedNear s v w :=
  h.imp (fun h => h.trans hrs) (fun h => h.trans hrs)

lemma UnorientedNear.trans {r s : ℝ} {u v w : Space}
    (h₁ : UnorientedNear r u v) (h₂ : UnorientedNear s v w) :
    UnorientedNear (r + s) u w := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · left
    calc
      _ = ‖(u - v) + (v - w)‖ := by congr 1; module
      _ ≤ ‖u - v‖ + ‖v - w‖ := norm_add_le _ _
      _ ≤ _ := add_le_add h₁ h₂
  · right
    calc
      _ = ‖(u - v) + (v + w)‖ := by congr 1; module
      _ ≤ ‖u - v‖ + ‖v + w‖ := norm_add_le _ _
      _ ≤ _ := add_le_add h₁ h₂
  · right
    calc
      _ = ‖(u + v) - (v - w)‖ := by congr 1; module
      _ ≤ ‖u + v‖ + ‖v - w‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add h₁ h₂
  · left
    calc
      _ = ‖(u + v) - (v + w)‖ := by congr 1; module
      _ ≤ ‖u + v‖ + ‖v + w‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add h₁ h₂

/-- If child centers and axes track their coarse unit-tube parents at scale tau,
the exact b-neighborhood of a child sees only boundedly many parent labels. -/
theorem bounded_coarse_parent_neighbors_of_card {p q : ℕ} {a b τ C M : ℝ}
    (hτ : 0 < τ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hab : a ≤ b) (hbτ : b ≤ τ)
    (hb1 : b ≤ 1) (z w : Fin q → Space)
    (hcard : ∀ l, (ncard {l' |
      ‖center (z l') (w l') - center (z l) (w l)‖ ≤ (2 * C + 10) * τ ∧
      (‖w l' - w l‖ ≤ 2 * ((2 * C + 10) * τ) ∨
        ‖w l' + w l‖ ≤ 2 * ((2 * C + 10) * τ))} : ℝ) ≤ M)
    (c e₁ e₂ e₃ : Fin p → Space) (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j])
    (label : Fin p → Fin q)
    (hcenter : ∀ j, ‖c j - center (z (label j)) (w (label j))‖ ≤ C * τ)
    (haxis : ∀ j, UnorientedNear (C * τ) (e₃ j) (w (label j))) :
    ∃ neighbors : Fin p → Finset (Fin q),
      (∀ j, ((neighbors j).card : ℝ) ≤ M) ∧
      ∀ j j', Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆
        Metric.thickening b (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
          label j' ∈ neighbors j := by
  classical
  let neighbors (j : Fin p) := Finset.univ.filter fun l =>
    ‖center (z l) (w l) - center (z (label j)) (w (label j))‖ ≤ (2 * C + 10) * τ ∧
    (‖w l - w (label j)‖ ≤ 2 * ((2 * C + 10) * τ) ∨
      ‖w l + w (label j)‖ ≤ 2 * ((2 * C + 10) * τ))
  refine ⟨neighbors, ?_, ?_⟩
  · intro j
    have hc := hcard (label j)
    rw [ncard_fintype] at hc
    convert hc using 1
    congr 2
    ext l
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  · intro j j' hnear
    have hc := prism_centers_close_of_subset_thickening hab ha (ha.trans hab) hb1
      (he j) (he j') hnear
    have hparentcenter : ‖center (z (label j')) (w (label j')) -
        center (z (label j)) (w (label j))‖ ≤ (2 * C + 10) * τ := by
      have htriangle : ‖center (z (label j')) (w (label j')) -
          center (z (label j)) (w (label j))‖ ≤
          ‖c j' - center (z (label j')) (w (label j'))‖ +
          (‖c j' - c j‖ + ‖c j - center (z (label j)) (w (label j))‖) := by
        calc
          _ ≤ ‖center (z (label j')) (w (label j')) - c j'‖ +
              ‖c j' - center (z (label j)) (w (label j))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := by
            rw [norm_sub_rev (center (z (label j')) (w (label j'))) (c j')]
            exact add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
      nlinarith [hcenter j, hcenter j']
    obtain ⟨s, hs, hdir⟩ := prism_axes_close_of_subset_thickening hab ha (ha.trans hab)
      (he j) (he j') hnear
    have hchildaxis : UnorientedNear (4 * b) (e₃ j') (e₃ j) := by
      have hbound : ‖e₃ j' - s • e₃ j‖ ≤ 4 * b := by linarith
      rcases hs with rfl | rfl
      · exact Or.inl (by simpa only [one_smul] using hbound)
      · exact Or.inr (by simpa only [neg_one_smul, sub_neg_eq_add] using hbound)
    have hparentaxis := ((haxis j').symm.trans hchildaxis).trans (haxis j)
    have hparentaxis' : UnorientedNear (2 * ((2 * C + 10) * τ))
        (w (label j')) (w (label j)) :=
      hparentaxis.mono (by nlinarith [mul_nonneg hC hτ.le])
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparentcenter, hparentaxis'⟩

theorem bounded_coarse_parent_neighbors {p q : ℕ} {a b τ C : ℝ}
    (hτ : 0 < τ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hab : a ≤ b) (hbτ : b ≤ τ)
    (hb1 : b ≤ 1) (hscale : (1 + 2 * (2 * C + 10)) * τ ≤ 1)
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1)
    (hsep : Distinct (fun l => Tube τ (z l) (w l)))
    (c e₁ e₂ e₃ : Fin p → Space) (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j])
    (label : Fin p → Fin q)
    (hcenter : ∀ j, ‖c j - center (z (label j)) (w (label j))‖ ≤ C * τ)
    (haxis : ∀ j, UnorientedNear (C * τ) (e₃ j) (w (label j))) :
    ∃ neighbors : Fin p → Finset (Fin q),
      (∀ j, ((neighbors j).card : ℝ) ≤ 147456000000 * (1 + 2 * (2 * C + 10)) ^ 4) ∧
      ∀ j j', Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆
        Metric.thickening b (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
          label j' ∈ neighbors j := by
  apply bounded_coarse_parent_neighbors_of_card hτ hC ha hab hbτ hb1 z w
    (fun l => tube_parameter_neighbor_card hτ (by linarith) hscale
      z w hw hsep (z l) (w l) (hw l)) c e₁ e₂ e₃ he label hcenter haxis

/-- A bound for all coarse scales at most one. -/
theorem bounded_coarse_parent_neighbors_unit {p q : ℕ} {a b τ C : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C) (ha : 0 ≤ a) (hab : a ≤ b) (hbτ : b ≤ τ)
    (hb1 : b ≤ 1)
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1)
    (hsep : Distinct (fun l => Tube τ (z l) (w l)))
    (c e₁ e₂ e₃ : Fin p → Space) (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j])
    (label : Fin p → Fin q)
    (hcenter : ∀ j, ‖c j - center (z (label j)) (w (label j))‖ ≤ C * τ)
    (haxis : ∀ j, UnorientedNear (C * τ) (e₃ j) (w (label j))) :
    ∃ neighbors : Fin p → Finset (Fin q),
      (∀ j, ((neighbors j).card : ℝ) ≤ 147456000000 * (1 + 2 * (2 * C + 10)) ^ 6) ∧
      ∀ j j', Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆
        Metric.thickening b (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
          label j' ∈ neighbors j := by
  apply bounded_coarse_parent_neighbors_of_card hτ hC ha hab hbτ hb1 z w
    (fun l => tube_parameter_neighbor_card_unit hτ hτ1 (by linarith)
      z w hw hsep (z l) (w l) (hw l)) c e₁ e₂ e₃ he label hcenter haxis

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
