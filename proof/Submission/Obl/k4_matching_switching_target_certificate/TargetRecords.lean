import Submission.Obl.k4_matching_switching_target_certificate.DetControls
import Submission.Obl.k4_matching_switching_target_certificate.TargetGeometry

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set MeasureTheory
open Submission.Obl.k4_matching_homogeneous_records (StageType)

def stageBins {J : ℕ} (data : StageType J) (κ : Bool) (j : ℕ) : ℤ :=
  if hj : j ≤ J then colourValue (data.2 ⟨j, by omega⟩) κ else 0

/-- The normalized final-time interval recorded by one child label. -/
def stageTimeInterval {J : ℕ} (Hk Hc : ℕ) (ta : ℝ) (data : StageType J) : Set ℝ :=
  Icc (((data.1 : ℝ) / (2 : ℝ) ^ Hc - ta) * (2 : ℝ) ^ Hk)
    ((((data.1 : ℝ) + 1) / (2 : ℝ) ^ Hc - ta) * (2 : ℝ) ^ Hk)

lemma volume_stageTimeInterval {J : ℕ} (Hk Hc : ℕ) (ta : ℝ) (data : StageType J) :
    volume (stageTimeInterval Hk Hc ta data) = ENNReal.ofReal ((2 : ℝ) ^ Hk / (2 : ℝ) ^ Hc) := by
  rw [stageTimeInterval, Real.volume_Icc]
  congr 1
  ring

def paddedStageTimeInterval {J : ℕ} (Hk Hc : ℕ) (ta : ℝ) (data : StageType J)
    (pad : ℝ) : Set ℝ :=
  Icc ((((data.1 : ℝ) / (2 : ℝ) ^ Hc - ta) * (2 : ℝ) ^ Hk) - pad)
    (((((data.1 : ℝ) + 1) / (2 : ℝ) ^ Hc - ta) * (2 : ℝ) ^ Hk) + pad)

lemma volume_paddedStageTimeInterval {J : ℕ} (Hk Hc : ℕ) (ta : ℝ) (data : StageType J) (pad : ℝ) :
    volume (paddedStageTimeInterval Hk Hc ta data pad) =
      ENNReal.ofReal ((2 : ℝ) ^ Hk / (2 : ℝ) ^ Hc + 2 * pad) := by
  rw [paddedStageTimeInterval, Real.volume_Icc]
  congr 1
  ring

/-- The moving low-jet center determined by one child record and one final colour. -/
def stageTargetCenter {J m : ℕ} (β : ℕ → ℝ) (N ac : ℝ) (Hk Hc : ℕ)
    (ta s₀ : ℝ) (frame initial : ℕ → ℝ) (data : StageType J) (κ : Bool)
    (j : Fin m) (s : ℝ) : ℝ :=
  let lam := ((2 : ℝ) ^ Hk)⁻¹
  let i := m - 1 - (j : ℕ)
  N ^ β m * (lam ^ m)⁻¹ * lam ^ i *
    (binJet J β N ac (stageBins data κ) (((data.1 : ℝ) + 1 / 2) / (2 : ℝ) ^ Hc) i (ta + lam * s) -
      iteratedDeriv i (taylorPoly J frame ta) (ta + lam * s)) - freeJet m initial s₀ s j

lemma continuous_stageTargetCenter {J m : ℕ} (hmJ : m ≤ J) (β : ℕ → ℝ) (N ac : ℝ)
    (Hk Hc : ℕ) (ta s₀ : ℝ) (frame initial : ℕ → ℝ) (data : StageType J) (κ : Bool) (j : Fin m) :
    Continuous (stageTargetCenter β N ac Hk Hc ta s₀ frame initial data κ j) := by
  have hi : m - 1 - (j : ℕ) ≤ J + 1 := by omega
  unfold stageTargetCenter
  simp only [iteratedDeriv_taylorPoly J frame ta hi]
  unfold binJet freeJet
  fun_prop

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma step_time_ratio : (2 : ℝ) ^ h k / (2 : ℝ) ^ h (k + 1) ≤
    2 * N ^ (-(1 / (m : ℝ)) / (q : ℝ)) := by
  have hk1 : k + 1 ≤ k + 6 * (J + 1) := by omega
  have hkq : k ≤ q := by have := H.hkq; omega
  have hkcq : k + 1 ≤ q := hk1.trans H.hkq
  have ha := (H.hadm ((k : ℝ) / q) (H.level_mem H.hzk (by omega))).1
  have hb := (H.hadm (((k + 1 : ℕ) : ℝ) / q) (H.level_mem (by have := H.hzk; omega) hk1)).1
  have hdiff : jetRadius J β ((k : ℝ) / q) - jetRadius J β (((k + 1 : ℕ) : ℝ) / q) =
      -(1 / (m : ℝ)) / (q : ℝ) := by
    rw [ha, hb]
    push_cast
    ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ h (k + 1))]
  calc (2 : ℝ) ^ h k ≤ 2 * N ^ jetRadius J β ((k : ℝ) / q) := (H.hdepth k hkq).2
    _ = 2 * N ^ (-(1 / (m : ℝ)) / (q : ℝ)) *
        N ^ jetRadius J β (((k + 1 : ℕ) : ℝ) / q) := by
      rw [← hdiff, mul_assoc, ← Real.rpow_add H.N_pos]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (H.hdepth (k + 1) hkcq).1
      (mul_nonneg (by norm_num) (H.Npow_pos _).le)

lemma stageTimeInterval_volume_le (ta : ℝ) (data : StageType J) :
    volume (stageTimeInterval (h k) (h (k + 1)) ta data) ≤
      ENNReal.ofReal (2 * N ^ (-(1 / (m : ℝ)) / (q : ℝ))) := by
  rw [volume_stageTimeInterval]
  exact ENNReal.ofReal_le_ofReal H.step_time_ratio

end Det

end Submission.Obl.k4_matching_switching_target_certificate
