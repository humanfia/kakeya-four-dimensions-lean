import Submission.Obl.k4_weighted_convex_tubes.Basic
import Submission.WZ.Obl.wz_nsp_convex_test_family
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.TerminalCount

namespace Submission.Obl.k4_weighted_convex_tubes

open MeasureTheory Set
open scoped Classical

theorem finite_convex_tests :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
    ∃ (H : ℕ) (P : Fin H → Set Space),
      (H : ℝ) ≤ B * r ^ (-B) ∧
      (∀ h, Convex ℝ (P h) ∧ MeasurableSet (P h) ∧
        0 < volume (P h) ∧ volume (P h) ≠ ⊤) ∧
      ∀ (n : ℕ) (x v : Fin n → Space),
      (∀ i, ‖v i‖ = 1) → (∀ i, tube r (x i) (v i) ⊆ Metric.ball 0 1) →
      ∀ (M : ℝ) (S : Finset (Fin n)),
      (∀ h, ENNReal.ofReal (((S.filter fun i => tube r (x i) (v i) ⊆ P h).card : ℝ)
        * r ^ 2) ≤ ENNReal.ofReal M * volume (P h)) →
      ConvexCount r (B * M) x v S := by
  classical
  obtain ⟨B, hB, htests⟩ := WangZahlLot.wz_nsp_convex_test_family tube rfl
  refine ⟨B, hB, fun r hr hr1 => ?_⟩
  obtain ⟨H, P, hH, hP, hcontrol⟩ := htests r hr hr1
  refine ⟨H, P, hH, hP, ?_⟩
  intro n x v hv hball M S htest
  let e : Fin S.card → Fin n := fun i => (S.equivFin.symm i).1
  have he : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have heS (i) : e i ∈ S := (S.equivFin.symm i).2
  have hcard (Q : Set Space) :
      {q : Fin 1 × Fin S.card | True ∧
        tube r (x (e q.2)) (v (e q.2)) ⊆ Q}.ncard =
        (S.filter fun i => tube r (x i) (v i) ⊆ Q).card := by
    have hbij : Set.BijOn (fun q : Fin 1 × Fin S.card => e q.2)
        {q | True ∧ tube r (x (e q.2)) (v (e q.2)) ⊆ Q}
        (↑(S.filter fun i => tube r (x i) (v i) ⊆ Q) : Set (Fin n)) := by
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        exact Finset.mem_filter.mpr ⟨heS q.2, hq.2⟩
      · intro q hq q' hq' hqq
        exact Prod.ext (Subsingleton.elim _ _) (he hqq)
      · intro i hi
        have hiS := (Finset.mem_filter.mp hi).1
        let j := S.equivFin ⟨i, hiS⟩
        have hj : e j = i := by simp [e, j]
        exact ⟨(0, j), ⟨trivial, by simpa only [hj] using (Finset.mem_filter.mp hi).2⟩, hj⟩
    simpa only [Set.ncard_coe_finset] using hbij.ncard_eq
  have hlarge (W : Set Space) (hW : Convex ℝ W) :
      ENNReal.ofReal (((S.filter fun i => tube r (x i) (v i) ⊆ W).card : ℝ) * r ^ 2) ≤
        ENNReal.ofReal (B * M) * volume W := by
    have hh := hcontrol 1 1 S.card (fun q => x (e q.2)) (fun q => v (e q.2))
      (fun _ => (0 : Fin 1)) M
      (fun q => ⟨hv (e q.2), (hball (e q.2)).trans (Metric.ball_subset_ball (by norm_num))⟩)
      (fun k h => by
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        simpa only [hcard] using htest h) (0 : Fin 1) W hW
    simpa only [hcard] using hh
  intro W hW F hFS hFW
  have hsub : F ⊆ S.filter (fun i => tube r (x i) (v i) ⊆ W) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨hFS hi, hFW i hi⟩
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub))
      (sq_nonneg r))).trans (hlarge W hW)

theorem tube_volume_lower {r : ℝ} (hr : 0 < r) (x v : Space) (hv : ‖v‖ = 1) :
    ENNReal.ofReal (r ^ 2) ≤ volume (tube r x v) :=
  WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hr x v hv

theorem tube_volume_upper {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (tube r x v) ≤ ENNReal.ofReal (56 * r ^ 2) :=
  WangZahlLot.Obl.wz_normalized_projection_coarse_fine.tube_volume_upper hr hr1 x v hv

end Submission.Obl.k4_weighted_convex_tubes
