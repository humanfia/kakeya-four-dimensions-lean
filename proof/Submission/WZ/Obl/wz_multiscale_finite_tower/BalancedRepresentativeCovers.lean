-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.BalancedRepresentativeCovers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.BalancedCovers
import Submission.WZ.Obl.wz_multiscale_finite_tower.RepresentativeCount
import Submission.WZ.Obl.wz_multiscale_finite_tower.RepresentativeSlabs
import Submission.WZ.Obl.wz_multiscale_finite_tower.BufferedGeometry

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound doubled convexExpansionLoss)

lemma BalancedPhysicalCover.representative_old_tube {d r s ζ C ω H B : ℝ}
    {n : ℕ} {x v : Fin n → Space} (P : BalancedPhysicalCover d r s ζ C ω H B n x v)
    (k : Fin P.card) :
    Tube s (x (P.representative k)) (v (P.representative k)) ⊆ doubled P.radius (P.position k) (P.direction k) := by
  simpa only [P.representative_assign] using P.containment (P.representative k) (P.representative_mem k)

lemma BalancedPhysicalCover.representative_contains {d r s ζ C ω H B h : ℝ}
    {n : ℕ} {x v : Fin n → Space} (P : BalancedPhysicalCover d r s ζ C ω H B n x v)
    (hs : 0 < s) (hsρ : s ≤ P.radius) (hρ : P.radius ≤ 1 / 160)
    {u : Space} (hv : ∀ i, ‖v i‖ = 1) (hcap : ∀ i, ‖v i - u‖ ≤ 1 / 10)
    (hmid : ∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1)
    (halign : ∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = h)
    (i : Fin n) (hi : i ∈ P.selected) :
    Tube s (x i) (v i) ⊆ Tube (320 * P.radius)
      (x (P.representative (P.assign i))) (v (P.representative (P.assign i))) := by
  exact aligned_common_cover hs hsρ hρ (hv i) (hv (P.representative (P.assign i)))
    (P.unit (P.assign i)) (hcap i) (hcap (P.representative (P.assign i))) (hmid i)
    ((halign i).trans (halign (P.representative (P.assign i))).symm)
    (P.containment i hi) (P.representative_old_tube (P.assign i))

lemma BalancedPhysicalCover.representative_count {d r s R ζ C ω H B : ℝ}
    {n : ℕ} {x v : Fin n → Space} (P : BalancedPhysicalCover d r s ζ C ω H B n x v)
    (hd : 0 ≤ d) (hs : 0 < s) (hR : 320 * P.radius ≤ R) (hR1 : R ≤ 1)
    (hv : ∀ i, ‖v i‖ = 1) (hmid : ∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1) :
    ConvexCount R ((R / P.radius) ^ 2 * d ^ (-ζ) * convexExpansionLoss 6) (fun _ => True)
      (fun k => Tube R (x (P.representative k)) (v (P.representative k))) := by
  exact representative_convex_count hs P.radius_pos hR hR1 (Real.rpow_nonneg hd _) (fun _ => True)
    (x ∘ P.representative) (v ∘ P.representative) P.position P.direction
    (fun k _ => hv _) (fun k _ => P.unit k) (fun k _ => hmid _)
    (fun k _ => P.representative_old_tube k) P.count

lemma BalancedPhysicalCover.representative_parent_containment {d r s R ζ C ω H B : ℝ}
    {n : ℕ} {x v : Fin n → Space} (P : BalancedPhysicalCover d r s ζ C ω H B n x v)
    (hd : 0 < d) (hr : 0 ≤ r) (hR : R ≤ r / 64) {y w : Space}
    (hbuf : ∀ i, Tube d (x i) (v i) ⊆ Tube ((31 / 32) * r) y w)
    (k : Fin P.card) : Tube R (x (P.representative k)) (v (P.representative k)) ⊆ Tube r y w :=
  (buffered_tube_containment hd hR (hbuf _)).trans (thickening_mono (by linarith) _)

lemma BalancedPhysicalCover.representative_child_buffer {d r s R ζ C ω H B h : ℝ}
    {n : ℕ} {x v : Fin n → Space} (P : BalancedPhysicalCover d r s ζ C ω H B n x v)
    (hds : d ≤ s) (hs : 0 < s) (hsρ : s ≤ P.radius) (hρ : P.radius ≤ 1 / 160)
    (hR : 1024 * P.radius ≤ R) {u : Space} (hv : ∀ i, ‖v i‖ = 1)
    (hcap : ∀ i, ‖v i - u‖ ≤ 1 / 10) (hmid : ∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1)
    (halign : ∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = h)
    (i : Fin n) (hi : i ∈ P.selected) :
    Tube d (x i) (v i) ⊆ Tube ((31 / 32) * R)
      (x (P.representative (P.assign i))) (v (P.representative (P.assign i))) :=
  (thickening_mono hds _).trans
    ((P.representative_contains hs hsρ hρ hv hcap hmid halign i hi).trans
      (thickening_mono (by have := P.radius_pos; linarith) _))

lemma BalancedPhysicalCover.representative_fine_slab {d r s R ζ C ω H B h : ℝ}
    {n : ℕ} {x v : Fin n → Space} (P : BalancedPhysicalCover d r s ζ C ω H B n x v)
    (hs : 0 < s) (hsρ : s ≤ P.radius) (hρ : P.radius ≤ 1 / 160)
    (hR : 320 * P.radius ≤ R) (hR1 : R ≤ 1) {u : Space} (hv : ∀ i, ‖v i‖ = 1)
    (hcap : ∀ i, ‖v i - u‖ ≤ 1 / 10) (hmid : ∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1)
    (halign : ∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = h) (k : Fin P.card) :
    SlabBound (doubled R (x (P.representative k)) (v (P.representative k)))
      (262144 * (R / P.radius) ^ 2 * d ^ (-ζ))
      (fun i => i ∈ P.selected ∧ P.assign i = k) (fun i => Tube s (x i) (v i)) := by
  apply representative_fibre_slab hs le_rfl P.radius_pos
    (by have := P.radius_pos; linarith) hR1 (hv _) (P.unit k) (P.representative_old_tube k)
    (fun i => i ∈ P.selected ∧ P.assign i = k) x v
  · intro i hi
    simpa only [hi.2] using P.containment i hi.1
  · intro i hi
    have hTi := (P.representative_contains hs hsρ hρ hv hcap hmid halign i hi.1).trans
      (thickening_mono hR _)
    rw [hi.2] at hTi
    apply hTi
    exact self_subset_thickening hs _ (by
      simpa only [axisMidpoint, zero_smul, add_zero] using
        WangZahlLot.Obl.wz_rescaled_fibre_alternatives.centered_segment (x i) (v i) (a := 0) (by norm_num))
  · exact P.slab k

lemma BalancedPhysicalCover.representative_coarse_slab {d r s R θ ζ C ω H B h : ℝ}
    {y w : Space} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (P : BalancedPhysicalCover d r s ζ C ω H B n x v) (F : PhysicalFrame d r s θ y w n x v Y)
    (hd : 0 ≤ d) (hr : 0 < r) (hs : 0 < s) (hH : 0 < H) (hB : 0 ≤ B)
    (hsρ : s ≤ P.radius) (hρ : P.radius ≤ 1 / 160) (hR : 320 * P.radius ≤ R)
    {u : Space} (hcap : ∀ i, ‖v i - u‖ ≤ 1 / 10) (hmid : ∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1)
    (halign : ∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = h) :
    SlabBound (doubled r y w) (2000000 * (B * d ^ (-θ) / H)) (fun _ => True)
      (fun k => Tube R (x (P.representative k)) (v (P.representative k))) := by
  have hR0 : 0 < R := (mul_pos (by norm_num) P.radius_pos).trans_le hR
  apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.parent_cover_slab hr hR0 F.1 P.selected P.assign
    id Function.injective_id hB hH (Real.rpow_nonneg hd _) P.retained P.balanced y w x v
    (x ∘ P.representative) (v ∘ P.representative)
    (fun i => (F.2.1 i).2.1)
  · intro k
    apply (F.2.1 (P.representative k)).2.1
    exact self_subset_thickening hs _ (by
      simpa only [Function.comp_apply, zero_smul, add_zero] using
        WangZahlLot.Obl.wz_rescaled_fibre_alternatives.centered_segment
          (x (P.representative k)) (v (P.representative k)) (a := 0) (by norm_num))
  · intro i hi
    exact ((P.representative_contains hs hsρ hρ (fun i => (F.2.1 i).1) hcap hmid halign i hi).trans
      (thickening_mono hR _)).trans
      (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.tube_subset_doubled hR0.le _ _)
  · exact F.2.2.2.2

end WangZahlLot.Obl.wz_multiscale_finite_tower
