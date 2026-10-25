import Submission.Obl.k4_matching_switching_target_certificate.PathRecordTargets
import Submission.Obl.k4_matching_switching_target_certificate.UniformCenters
import Submission.Obl.k4_matching_switching_target_certificate.FinalRecords
import Submission.Obl.k4_matching_switching_target_certificate.Certificate

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set MeasureTheory
open Submission.Obl.k4_matching_homogeneous_records (StageType stageFromCell)

/-- The fixed coefficient in the enlarged target widths. -/
def targetWidthConstant (m : ℕ) : ℝ := endpointLoss m + 4

def targetVolumeConstant (m : ℕ) : ℝ :=
  2 * targetWidthConstant m * (2 * targetWidthConstant m) ^ m

lemma targetWidthConstant_ge_four (m : ℕ) : 4 ≤ targetWidthConstant m := by
  have := endpointLoss_pos m
  unfold targetWidthConstant
  linarith

lemma targetVolumeConstant_nonneg (m : ℕ) : 0 ≤ targetVolumeConstant m := by
  have := targetWidthConstant_ge_four m
  unfold targetVolumeConstant
  positivity

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

/-- A perturbed endpoint lies in the enlarged tube of its exact final record. -/
theorem jitter_mem_recordTubeUnion (a : (Fin n₁ × Fin n₂) × ℝ)
    {e : (Fin n₁ × Fin n₂) × ℝ} (he : e ∈ S) (κ : Bool)
    (Codes : Finset ℕ) (hcode : F (k + 1) e ∈ Codes)
    (U : Fin (m + 1) → ℝ) {B L δ pad W : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) (hpad : δ ≤ pad)
    (hU : ∀ p, |U p| ≤ B) (hs₀ : |ntime h k a a.2| ≤ 1)
    (hc : ∀ j s t, |s| ≤ 1 → |t| ≤ 1 →
      |tcen J β q k m N f₁ f₂ h a e κ j s -
        tcen J β q k m N f₁ f₂ h a e κ j t| ≤ L * |s - t|)
    (y : ℝ × (Fin m → ℝ)) (hy : |y.1| ≤ 1 / 2 ∧ ∀ p, |y.2 p| ≤ 1 / 2)
    (hytime : y.1 ∈ tset h k a e)
    (hyjet : ∀ j, |(endpointMap m U (ntime h k a a.2) y).2 j -
        tcen J β q k m N f₁ f₂ h a e κ j y.1| ≤
      endpointLoss m * N ^ ε * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))))
    (hw : ∀ j : Fin m,
      endpointLoss m * N ^ ε * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))) +
        (B * (m : ℝ) * (4 * (m : ℝ) + 1) * 2 ^ m + L) * δ ≤
      W * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))))
    (x : ℝ × (Fin m → ℝ)) (hx1 : |x.1 - y.1| ≤ δ)
    (hx2 : ∀ p, |x.2 p - y.2 p| ≤ δ) :
    endpointMap m U (ntime h k a a.2) x ∈
      recordTubeUnion (m := m) β N (((k + 1 : ℕ) : ℝ) / q) (h k) (h (k + 1))
        (dcenter h k a.2) (ntime h k a a.2) (cref f₁ h k a) (jet0 J β m N f₁ h k a)
        (stageFromRecord J q (k + 1) β N h F S f₁ f₂) Codes W q pad := by
  let data := referenceStage J (k + 1) q β N h f₁ f₂ e
  let lo := (((data.1 : ℝ) / (2 : ℝ) ^ h (k + 1) - dcenter h k a.2) * (2 : ℝ) ^ h k)
  let hi := ((((data.1 : ℝ) + 1) / (2 : ℝ) ^ h (k + 1) - dcenter h k a.2) * (2 : ℝ) ^ h k)
  have hyt : y.1 ∈ Icc lo hi := by
    change y.1 ∈ stageTimeInterval (h k) (h (k + 1)) (dcenter h k a.2) data
    rw [stageTimeInterval_referenceStage]
    exact hytime
  have hjit := endpointMap_mem_tube_of_near U (ntime h k a a.2) hB hδ hL hU hs₀
    y hy hδ2 (tcen J β q k m N f₁ f₂ h a e κ)
    (fun j => endpointLoss m * N ^ ε * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))))
    (fun j => W * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))))
    hc hyt hyjet hw x hx1 hx2
  have hmem : (F (k + 1) e, !κ) ∈ Codes.product (Finset.univ : Finset Bool) := by
    simpa only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, and_true]
      using hcode
  apply Set.mem_iUnion_of_mem (F (k + 1) e, !κ)
  apply Set.mem_iUnion_of_mem hmem
  rw [H.stageFromRecord_eq H.child_le_q he]
  refine ⟨?_, fun j => ?_⟩
  · change x.1 ∈ Icc (lo - pad) (hi + pad)
    have ht : lo - δ ≤ x.1 ∧ x.1 ≤ hi + δ := hjit.1
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rw [stageTargetCenter_referenceStage, Bool.not_not]
    simpa only [neg_div] using hjit.2 j

theorem volume_uniform_targets_le (hfinite : (F (k + 1) '' S).Finite)
    (A : Finset ℕ) (u : ℕ → ℝ)
    (hdesc : ∀ x ∈ S, ((F (k + 1) '' {y | y ∈ S ∧ F k y = F k x}).ncard : ℝ) ≤
      N ^ (u (k + 1) - u k + ε)) (a : (Fin n₁ × Fin n₂) × ℝ) :
    volume (recordTubeUnion (m := m) β N (((k + 1 : ℕ) : ℝ) / q) (h k) (h (k + 1))
      (dcenter h k a.2) (ntime h k a a.2) (cref f₁ h k a) (jet0 J β m N f₁ h k a)
      (stageFromRecord J q (k + 1) β N h F S f₁ f₂)
      (childrenOver S (F k) (F (k + 1)) hfinite A) (targetWidthConstant m * N ^ ε) q
      (N ^ (-(1 / (m : ℝ)) / (q : ℝ)))) ≤
      ENNReal.ofReal (targetVolumeConstant m * A.card * N ^ (((m : ℝ) + 2) * ε) *
        N ^ (u (k + 1) - u k - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ))) := by
  have hW : 4 ≤ targetWidthConstant m * N ^ ε :=
    (targetWidthConstant_ge_four m).trans
      (le_mul_of_one_le_right (by linarith [targetWidthConstant_ge_four m]) H.Nε_ge_one)
  have hv := H.volume_descendant_targets_le hfinite A hW hdesc
    (dcenter h k a.2) (ntime h k a a.2) (cref f₁ h k a) (jet0 J β m N f₁ h k a)
  convert hv using 1
  congr 1
  have hp : N ^ (((m : ℝ) + 2) * ε) = N ^ ε * (N ^ ε) ^ m * N ^ ε := by
    rw [show ((m : ℝ) + 2) * ε = ε + ε * (m : ℝ) + ε by ring,
      Real.rpow_add H.N_pos, Real.rpow_add H.N_pos, Real.rpow_mul_natCast H.N_pos.le]
  rw [hp]
  unfold targetVolumeConstant
  rw [show 2 * (targetWidthConstant m * N ^ ε) = (2 * targetWidthConstant m) * N ^ ε by ring]
  simp only [mul_pow]
  ring

end Det

end Submission.Obl.k4_matching_switching_target_certificate
