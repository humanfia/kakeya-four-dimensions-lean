-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.KatzTaoExtraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.FrostmanExtraction
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.Counting

/-!
# Absolute counting bounds for the extracted point set

The dyadic extraction gives an absolute `36 * ρ / r` bound up to radius
one half. A fixed finite cover of the bounded ambient ball extends this to
all radii and bounds the total number of extracted points by `A / r`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

theorem bounded_frostman_katz_tao_extraction : ∃ A : ℝ, 1 ≤ A ∧
    ∀ (r C : ℝ) (P : Set (EuclideanSpace ℝ (Fin 2))),
      0 < r → r ≤ 1 / 2 → 1 ≤ C → P.Finite → P.Nonempty →
      (∀ p ∈ P, ‖p‖ ≤ 4) →
      (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ →
        ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ * P.ncard) →
      ∃ Q ⊆ P, Q.Finite ∧ Q.Nonempty ∧
        1 / (40 * C * r) ≤ (Q.ncard : ℝ) ∧ (Q.ncard : ℝ) ≤ A / r ∧
        (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → r ≤ dist x y) ∧
        (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ →
          ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ 1440 * C * ρ * Q.ncard) ∧
        ∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ →
          ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ A * (ρ / r) := by
  classical
  obtain ⟨S, hcover⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 4).elim_finite_subcover
    (fun x => Metric.ball x (1 / 2 : ℝ)) (fun _ => Metric.isOpen_ball)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  let A : ℝ := 36 * ((S.card : ℝ) + 1)
  have hA36 : 36 ≤ A := by dsimp [A]; nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
  refine ⟨A, by linarith, ?_⟩
  intro r C P hr hrhalf hC hP hPne hPnorm hFr
  obtain ⟨Q, hQP, hQ, hQne, hmass, hsep, hQfr, hlocal⟩ :=
    planar_frostman_separated_subset_with_local_bound hr (by linarith) hC hP hPne hFr
  have hQcover : Q ⊆ ⋃ x ∈ S, Q ∩ Metric.closedBall x (1 / 2 : ℝ) := by
    intro q hq
    have hqball : q ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 4 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hPnorm q (hQP hq)
    obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.mp (hcover hqball)
    exact Set.mem_iUnion₂.mpr ⟨x, hx, hq, (Metric.mem_ball.mp hqx).le⟩
  have hglobal : (Q.ncard : ℝ) ≤ 18 * (S.card : ℝ) / r := by
    calc (Q.ncard : ℝ)
        ≤ ((⋃ x ∈ S, Q ∩ Metric.closedBall x (1 / 2 : ℝ)).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hQcover
            (Set.Finite.biUnion S.finite_toSet (fun _ _ => hQ.inter_of_left _))
      _ ≤ ∑ x ∈ S, ((Q ∩ Metric.closedBall x (1 / 2 : ℝ)).ncard : ℝ) :=
        ncard_biUnion_finset_le S _
      _ ≤ ∑ _x ∈ S, (36 * (1 / 2 : ℝ) / r) :=
        Finset.sum_le_sum (fun x _ => hlocal x (1 / 2) hrhalf le_rfl)
      _ = 18 * (S.card : ℝ) / r := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  refine ⟨Q, hQP, hQ, hQne, hmass, ?_, hsep, hQfr, ?_⟩
  · exact hglobal.trans (div_le_div_of_nonneg_right
      (by dsimp [A]; nlinarith [Nat.cast_nonneg (α := ℝ) S.card]) hr.le)
  · intro x ρ hρ
    have hρpos := hr.trans_le hρ
    by_cases hρhalf : ρ ≤ 1 / 2
    · calc ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ 36 * ρ / r := hlocal x ρ hρ hρhalf
        _ = 36 * (ρ / r) := by ring
        _ ≤ A * (ρ / r) := mul_le_mul_of_nonneg_right hA36 (by positivity)
    · have hc : ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ Q.ncard := by
        exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left hQ
      calc ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ Q.ncard := hc
        _ ≤ 18 * (S.card : ℝ) / r := hglobal
        _ ≤ (A * ρ) / r := by
          apply div_le_div_of_nonneg_right _ hr.le
          dsimp [A]
          have hρhalf' : 1 / 2 ≤ ρ := le_of_not_ge hρhalf
          nlinarith [mul_le_mul_of_nonneg_left hρhalf' (Nat.cast_nonneg (α := ℝ) S.card)]
        _ = A * (ρ / r) := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
