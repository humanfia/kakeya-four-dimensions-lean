import Submission.Obl.k4_matching_switching_target_certificate.TargetRecords
import Submission.Obl.k4_matching_switching_target_certificate.TargetCounting

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set MeasureTheory
open Submission.Obl.k4_matching_homogeneous_records (StageType)

def stageFromRecord {n₁ n₂ : ℕ} (J q v : ℕ) (β : ℕ → ℝ) (N : ℝ)
    (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ))
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (code : ℕ) : StageType J :=
  recordValue S (F v) (referenceStage J v q β N h f₁ f₂) (0, fun _ => (0, 0)) code

lemma Det.stageFromRecord_eq {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
    {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (H : Det J β γ q k m z N ε f₁ f₂ h F S) {v : ℕ} (hv : v ≤ q)
    {e : (Fin n₁ × Fin n₂) × ℝ} (he : e ∈ S) :
    stageFromRecord J q v β N h F S f₁ f₂ (F v e) = referenceStage J v q β N h f₁ f₂ e := by
  apply recordValue_eq _ _ he
  intro x hx y hy hxy
  obtain ⟨ht, hj⟩ := (H.hrec v hv x hx y hy).mp hxy v le_rfl
  apply Prod.ext ht
  funext j
  exact Prod.ext (hj j (by omega)).1 (hj j (by omega)).2

/-- Both colours' target tubes over a finite family of final record labels. -/
def recordTubeUnion {J m : ℕ} (β : ℕ → ℝ) (N ac : ℝ) (Hk Hc : ℕ)
    (ta s₀ : ℝ) (frame initial : ℕ → ℝ) (data : ℕ → StageType J)
    (Codes : Finset ℕ) (W : ℝ) (q : ℕ) (pad : ℝ := 0) : Set (ℝ × (Fin m → ℝ)) :=
  ⋃ i ∈ Codes.product (Finset.univ : Finset Bool),
    tube (paddedStageTimeInterval Hk Hc ta (data i.1) pad)
      (stageTargetCenter β N ac Hk Hc ta s₀ frame initial (data i.1) i.2)
      (fun j : Fin m => W * N ^ (-(((j : ℝ) + 1) / (m : ℝ)) / (q : ℝ)))

lemma measurableSet_recordTubeUnion {J m : ℕ} (hmJ : m ≤ J) (β : ℕ → ℝ)
    (N ac : ℝ) (Hk Hc : ℕ) (ta s₀ : ℝ) (frame initial : ℕ → ℝ)
    (data : ℕ → StageType J) (Codes : Finset ℕ) (W : ℝ) (q : ℕ) (pad : ℝ := 0) :
    MeasurableSet (recordTubeUnion (m := m) β N ac Hk Hc ta s₀ frame initial data Codes W q pad) := by
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro hi
  exact measurableSet_tube _ measurableSet_Icc
    (fun j => (continuous_stageTargetCenter hmJ β N ac Hk Hc ta s₀ frame initial (data i.1) i.2 j).measurable)

theorem volume_recordTubeUnion_le {J m q : ℕ} (hm : 1 ≤ m) (hmJ : m ≤ J)
    (β : ℕ → ℝ) {N : ℝ} (hN : 0 < N) (ac : ℝ) (Hk Hc : ℕ)
    (ta s₀ : ℝ) (frame initial : ℕ → ℝ) (data : ℕ → StageType J)
    (Codes : Finset ℕ) {W C Δ pad : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hcard : (Codes.card : ℝ) ≤ C * N ^ Δ)
    (htime : (2 : ℝ) ^ Hk / (2 : ℝ) ^ Hc + 2 * pad ≤ W * N ^ (-(1 / (m : ℝ)) / (q : ℝ))) :
    volume (recordTubeUnion (m := m) β N ac Hk Hc ta s₀ frame initial data Codes W q pad) ≤
      ENNReal.ofReal (2 * C * W * (2 * W) ^ m *
        N ^ (Δ - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ))) := by
  apply volume_step_target_le (m := m) (q := q) hm (Codes.product (Finset.univ : Finset Bool))
    (N := N) (B := W) (A := 2 * C) (Δ := Δ)
    (S := fun i => paddedStageTimeInterval Hk Hc ta (data i.1) pad)
    (c := fun i => stageTargetCenter β N ac Hk Hc ta s₀ frame initial (data i.1) i.2)
    hN hW (by positivity)
    (fun _ => measurableSet_Icc)
    (fun i j => (continuous_stageTargetCenter hmJ β N ac Hk Hc ta s₀ frame initial (data i.1) i.2 j).measurable)
  · intro i hi
    rw [volume_paddedStageTimeInterval]
    exact ENNReal.ofReal_le_ofReal htime
  · change ((Codes.product (Finset.univ : Finset Bool)).card : ℝ) ≤ 2 * C * N ^ Δ
    rw [Finset.product_eq_sprod, Finset.card_product]
    norm_num only [Finset.card_univ, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    have hh : (Codes.card : ℝ) * 2 ≤ 2 * C * N ^ Δ := by nlinarith
    exact hh

theorem Det.volume_descendant_targets_le {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ}
    {q k m z : ℕ} {N ε : ℝ}
    {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (H : Det J β γ q k m z N ε f₁ f₂ h F S)
    (hfinite : (F (k + 1) '' S).Finite) (A : Finset ℕ) {Δ W : ℝ} (hW : 4 ≤ W)
    (hdesc : ∀ x ∈ S, ((F (k + 1) '' {y | y ∈ S ∧ F k y = F k x}).ncard : ℝ) ≤ N ^ (Δ + ε))
    (ta s₀ : ℝ) (frame initial : ℕ → ℝ) :
    volume (recordTubeUnion (m := m) β N (((k + 1 : ℕ) : ℝ) / (q : ℝ)) (h k) (h (k + 1)) ta s₀
      frame initial (stageFromRecord J q (k + 1) β N h F S f₁ f₂)
      (childrenOver S (F k) (F (k + 1)) hfinite A) W q (N ^ (-(1 / (m : ℝ)) / (q : ℝ)))) ≤
    ENNReal.ofReal (2 * (A.card : ℝ) * W * (2 * W) ^ m * N ^ ε *
      N ^ (Δ - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ))) := by
  have hc := childrenOver_card_le hfinite A (H.Npow_pos _).le hdesc
  have ht : (2 : ℝ) ^ h k / (2 : ℝ) ^ h (k + 1) +
      2 * N ^ (-(1 / (m : ℝ)) / (q : ℝ)) ≤ W * N ^ (-(1 / (m : ℝ)) / (q : ℝ)) := by
    have hr := H.step_time_ratio
    have hp := (H.Npow_pos (-(1 / (m : ℝ)) / (q : ℝ))).le
    nlinarith
  have hv := volume_recordTubeUnion_le H.hm H.hmJ β H.N_pos (((k + 1 : ℕ) : ℝ) / (q : ℝ))
    (h k) (h (k + 1)) ta s₀ frame initial (stageFromRecord J q (k + 1) β N h F S f₁ f₂)
    (childrenOver S (F k) (F (k + 1)) hfinite A) (by linarith) (Nat.cast_nonneg A.card) hc ht
  refine hv.trans_eq ?_
  congr 1
  rw [show Δ + ε - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ) =
    ε + (Δ - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ)) by ring, Real.rpow_add H.N_pos]
  ring

end Submission.Obl.k4_matching_switching_target_certificate
