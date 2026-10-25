-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.EndpointGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSGeometry

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, EndpointGeometry.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V P T)

/-- A prism whose center stays away from both coarse endpoints gives
endpoint clearance for every contained fine tube crossing that prism. -/
def PrismData.Away {n : ℕ} (D : PrismData n) (ρ c R : ℝ) (j : Fin D.L) : Prop :=
  R + c + 3 * ρ < dist (D.z j) (D.y (D.γ j)) ∧
    R + c + 3 * ρ < dist (D.z j) (D.y (D.γ j) + D.w (D.γ j))

theorem prism_endpoint_clearance {ω ζ δ h ρ c R : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hv : ∀ i, ‖v i‖ = 1)
    (H : D.Valid ω ζ δ h ρ c x v Y 1)
    {i : Fin n} {j : Fin D.L} (hi : (D.W i j).Nonempty)
    (hj : D.Away ρ c R j) :
    ∀ p ∈ P D.a (ρ * c) c (D.z j) (D.e j),
      R < dist p (x i) ∧ R < dist p (x i + v i) := by
  rcases H with ⟨ha, hab, hbc, _, _, _, _, hcross, _, _, hw, hcover, _⟩
  have ht := (hcross i j hi).1
  rw [(hcover (by norm_num)).1] at ht
  have hends := WangZahlLot.Obl.wz_extremal_lipschitz_grains.endpoints_close hδ (hv i) (hw (D.γ j)) ht
  simp only [← dist_eq_norm] at hends
  intro p hp
  have hpz : dist (D.z j) p ≤ c := by
    rw [dist_comm, dist_eq_norm]
    exact WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_norm (hδ.le.trans ha) hab hbc _ _ hp
  rcases hends with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · constructor
    · have ht := dist_triangle (D.z j) p (D.y (D.γ j))
      have ht' := dist_triangle p (x i) (D.y (D.γ j))
      linarith [hj.1]
    · have ht := dist_triangle (D.z j) p (D.y (D.γ j) + D.w (D.γ j))
      have ht' := dist_triangle p (x i + v i) (D.y (D.γ j) + D.w (D.γ j))
      linarith [hj.2]
  · constructor
    · have ht := dist_triangle (D.z j) p (D.y (D.γ j) + D.w (D.γ j))
      have ht' := dist_triangle p (x i) (D.y (D.γ j) + D.w (D.γ j))
      linarith [hj.2]
    · have ht := dist_triangle (D.z j) p (D.y (D.γ j))
      have ht' := dist_triangle p (x i + v i) (D.y (D.γ j))
      linarith [hj.1]

/-- Every incidence in a prism failing the coarse-end clearance test lies
near an endpoint of its own fine tube. Thus whole bad prisms can be removed
using the ordinary fine-tube endpoint volume budget. -/
theorem bad_prism_near_fine_ends {ω ζ δ h ρ c R : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hv : ∀ i, ‖v i‖ = 1)
    (H : D.Valid ω ζ δ h ρ c x v Y 1)
    {i : Fin n} {j : Fin D.L} (hj : ¬ D.Away ρ c R j) :
    D.W i j ⊆ closedBall (x i) (R + 2 * c + 6 * ρ) ∪
      closedBall (x i + v i) (R + 2 * c + 6 * ρ) := by
  rcases H with ⟨ha, hab, hbc, _, hW, _, _, hcross, _, _, hw, hcover, _⟩
  intro p hp
  have ht := (hcross i j ⟨p, hp⟩).1
  rw [(hcover (by norm_num)).1] at ht
  have hends := WangZahlLot.Obl.wz_extremal_lipschitz_grains.endpoints_close hδ (hv i) (hw (D.γ j)) ht
  simp only [← dist_eq_norm] at hends
  have hpz : dist p (D.z j) ≤ c := by
    rw [dist_eq_norm]
    exact WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_norm
      (hδ.le.trans ha) hab hbc _ _ ((hW i j).2.1 hp).2
  have hbad : dist (D.z j) (D.y (D.γ j)) ≤ R + c + 3 * ρ ∨
      dist (D.z j) (D.y (D.γ j) + D.w (D.γ j)) ≤ R + c + 3 * ρ := by
    simpa only [PrismData.Away, not_and_or, not_lt] using hj
  have hnear (q r : V) (hq : dist (D.z j) q ≤ R + c + 3 * ρ)
      (hr : dist r q ≤ 3 * ρ) : dist p r ≤ R + 2 * c + 6 * ρ := by
    have ht := dist_triangle p (D.z j) q
    have ht' := dist_triangle p q r
    rw [dist_comm q r] at ht'
    linarith
  rcases hends with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rcases hbad with hb | hb
    · exact Or.inl (hnear _ _ hb hl)
    · exact Or.inr (hnear _ _ hb hr)
  · rcases hbad with hb | hb
    · exact Or.inr (hnear _ _ hb hr)
    · exact Or.inl (hnear _ _ hb hl)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
