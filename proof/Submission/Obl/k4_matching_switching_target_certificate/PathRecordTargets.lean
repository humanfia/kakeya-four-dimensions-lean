import Submission.Obl.k4_matching_switching_target_certificate.Target
import Submission.Obl.k4_matching_switching_target_certificate.RecordTargetFamily

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set MeasureTheory
open Submission.Obl.k4_matching_homogeneous_records (StageType stageFromCell)

variable {n₁ n₂ : ℕ}

/-- The path API labels the first arm by `false`; record controls label it by `true`. -/
lemma stageBins_referenceStage (J q k : ℕ) (β : ℕ → ℝ) (N : ℝ) (h : ℕ → ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (y : (Fin n₁ × Fin n₂) × ℝ) (κ : Bool) {i : ℕ} (hi : i ≤ J) :
    stageBins (referenceStage J (k + 1) q β N h f₁ f₂ y) κ i =
      finBins J β q k N f₁ f₂ h y (!κ) i := by
  cases κ <;> simp [stageBins, hi, referenceStage, stageFromCell, colourValue,
    finBins, arm, dcenter]

lemma binJet_referenceStage (J q k : ℕ) (β : ℕ → ℝ) (N : ℝ) (h : ℕ → ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (y : (Fin n₁ × Fin n₂) × ℝ) (κ : Bool) (tc : ℝ) (i : ℕ) (t : ℝ) :
    binJet J β N (((k + 1 : ℕ) : ℝ) / q)
        (stageBins (referenceStage J (k + 1) q β N h f₁ f₂ y) κ) tc i t =
      binJet J β N (((k + 1 : ℕ) : ℝ) / q) (finBins J β q k N f₁ f₂ h y (!κ)) tc i t := by
  unfold binJet
  apply Finset.sum_congr rfl
  intro i' hi'
  rw [stageBins_referenceStage J q k β N h f₁ f₂ y κ (by
    have := Finset.mem_range.mp hi'; omega)]

lemma stageTargetCenter_referenceStage (J q k m : ℕ) (β : ℕ → ℝ) (N : ℝ)
    (h : ℕ → ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (a y : (Fin n₁ × Fin n₂) × ℝ) (κ : Bool) :
    stageTargetCenter (m := m) β N (((k + 1 : ℕ) : ℝ) / q) (h k) (h (k + 1))
        (dcenter h k a.2) (ntime h k a a.2) (cref f₁ h k a) (jet0 J β m N f₁ h k a)
        (referenceStage J (k + 1) q β N h f₁ f₂ y) κ =
      tcen J β q k m N f₁ f₂ h a y (!κ) := by
  funext j s
  unfold stageTargetCenter tcen
  dsimp only
  rw [binJet_referenceStage]
  rfl

lemma stageTimeInterval_referenceStage (J q k : ℕ) (β : ℕ → ℝ) (N : ℝ)
    (h : ℕ → ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (a y : (Fin n₁ × Fin n₂) × ℝ) :
    stageTimeInterval (h k) (h (k + 1)) (dcenter h k a.2)
        (referenceStage J (k + 1) q β N h f₁ f₂ y) = tset h k a y := by
  have hl := lamk_pos h k
  have hset : tset h k a y = Icc ((dleft h (k + 1) y.2 - dcenter h k a.2) / lamk h k)
      ((dleft h (k + 1) y.2 + ((2 : ℝ) ^ h (k + 1))⁻¹ - dcenter h k a.2) / lamk h k) := by
    ext s
    simp only [tset, Set.mem_ofPred_eq, mem_Icc]
    rw [div_le_iff₀ hl, le_div_iff₀ hl]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset]
  unfold stageTimeInterval
  congr 1 <;> dsimp [referenceStage, stageFromCell, dleft, lamk] <;>
    simp only [div_inv_eq_mul] <;> ring

lemma stageTimeInterval_subset_padded {J : ℕ} (Hk Hc : ℕ) (ta : ℝ) (data : StageType J)
    {pad : ℝ} (hpad : 0 ≤ pad) :
    stageTimeInterval Hk Hc ta data ⊆ paddedStageTimeInterval Hk Hc ta data pad := by
  intro s hs
  obtain ⟨hl, hu⟩ := hs
  constructor <;> linarith

/-- The record-and-palette control in the frame of one fixed start. -/
def startControl (J m k z q : ℕ) (β : ℕ → ℝ) (N : ℝ) (h : ℕ → ℕ)
    (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ))
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (a : (Fin n₁ × Fin n₂) × ℝ) : ℕ → (ℤ × ℤ) → Bool → ℝ :=
  codedControl J m k z q β N (dcenter h k a.2) (cref f₁ h k a m) h F S f₁ f₂

namespace Det

variable {J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

theorem ptube_subset_recordTubeUnion (a : (Fin n₁ × Fin n₂) × ℝ)
    {y : (Fin n₁ × Fin n₂) × ℝ} (hy : y ∈ S) (Codes : Finset ℕ)
    (hcode : F (k + 1) y ∈ Codes) (κ : Bool) {W₀ W pad : ℝ}
    (hW : W₀ ≤ W) (hpad : 0 ≤ pad) :
    ptube J β q k m N W₀ f₁ f₂ h a y κ ⊆
      recordTubeUnion (m := m) β N (((k + 1 : ℕ) : ℝ) / q) (h k) (h (k + 1))
        (dcenter h k a.2) (ntime h k a a.2) (cref f₁ h k a) (jet0 J β m N f₁ h k a)
        (stageFromRecord J q (k + 1) β N h F S f₁ f₂) Codes W q pad := by
  intro x hx
  have hk1 : k + 1 ≤ q := by have := H.hkq; omega
  have hmem : (F (k + 1) y, !κ) ∈ Codes.product (Finset.univ : Finset Bool) := by
    simpa only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, and_true]
      using hcode
  apply Set.mem_iUnion_of_mem (F (k + 1) y, !κ)
  apply Set.mem_iUnion_of_mem hmem
  rw [H.stageFromRecord_eq hk1 hy]
  constructor
  · apply stageTimeInterval_subset_padded _ _ _ _ hpad
    rw [stageTimeInterval_referenceStage]
    exact hx.1
  · intro j
    rw [stageTargetCenter_referenceStage, Bool.not_not]
    apply (hx.2 j).trans
    simpa only [twidth, neg_div] using
      mul_le_mul_of_nonneg_right hW
        (H.Npow_pos (-(((j : ℝ) + 1) / (m : ℝ)) / (q : ℝ))).le

/-- Palette controls put every exact path endpoint in the finite record target. -/
theorem path_coded_endpoint_mem (hεq : ε ≤ 1 / (q : ℝ)) (hroot : 32 ≤ N ^ (1 / (q : ℝ)))
    {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ)
    (Codes : Finset ℕ) (hcode : F (k + 1) (E (m + 1)) ∈ Codes)
    {Wd pad : ℝ} (hWd : pathWidth m N ε 1 ≤ Wd) (hpad : 0 ≤ pad) :
    endpointMap m
        (fun p => startControl J m k z q β N h F S f₁ f₂ (E 0) (F k (W p))
          (referencePalette m z q β N h f₁ f₂ (W p)) (!(κ p)))
        (ntime h k (E 0) (E 0).2)
        (ntime h k (E 0) (E (m + 1)).2, fun p => ntime h k (E 0) (E ((p : ℕ) + 1)).2) ∈
      recordTubeUnion (m := m) β N (((k + 1 : ℕ) : ℝ) / q) (h k) (h (k + 1))
        (dcenter h k (E 0).2) (ntime h k (E 0) (E 0).2) (cref f₁ h k (E 0))
        (jet0 J β m N f₁ h k (E 0))
        (stageFromRecord J q (k + 1) β N h F S f₁ f₂) Codes Wd q pad := by
  apply H.ptube_subset_recordTubeUnion (E 0) (hP.memE (m + 1) le_rfl) Codes hcode
    (κ m) hWd hpad
  apply H.path_endpoint_mem hP
    (fun p => startControl J m k z q β N h F S f₁ f₂ (E 0) (F k (W p))
      (referencePalette m z q β N h f₁ f₂ (W p)) (!(κ p)))
    (e₀ := N ^ (-(2 / (q : ℝ)))) (E₀ := 1) (H.Npow_pos _).le
  · simp only [one_mul]
    apply Real.rpow_le_rpow_of_exponent_le H.hN
    have hq := H.q_pos
    have : 1 / (q : ℝ) ≤ 2 / (q : ℝ) := by gcongr; norm_num
    linarith
  · intro p hp
    have hf := ((H.path_floor hP).2 p hp).symm
    have he := H.coded_control_error_small hεq hroot (hP.memE 0 (by omega))
      (hP.memW p hp) hf (cref f₁ h k (E 0) m) (!(κ p))
    cases hκ : κ p <;> simpa only [startControl, arm, hκ, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true] using he

end Det

end Submission.Obl.k4_matching_switching_target_certificate
