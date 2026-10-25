import Submission.Obl.k4_matching_switching_target_certificate.PaddedRecordTargets
import Submission.Obl.k4_matching_switching_target_certificate.Assembly

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set MeasureTheory

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

/-- The positive perturbation allowance is chosen once for every start and path. -/
theorem uniform_targetCovers (u : ℕ → ℝ)
    (hεq : ε ≤ 1 / (q : ℝ)) (hroot : 32 ≤ N ^ (1 / (q : ℝ)))
    (hfinite : (F (k + 1) '' S).Finite)
    (hdesc : ∀ x ∈ S, ((F (k + 1) '' {y | y ∈ S ∧ F k y = F k x}).ncard : ℝ) ≤
      N ^ (u (k + 1) - u k + ε)) :
    ∃ δ : ℝ, 0 < δ ∧ H.TargetCovers u (targetVolumeConstant m) δ := by
  classical
  have hN0 := H.N_pos
  obtain ⟨L, hL, hcenter⟩ := H.exists_tcen_lipschitz
  let B : ℝ := (neighborRadius J m N ε : ℝ) + 2 + 5 * N ^ ε
  let P : ℝ := B * (m : ℝ) * (4 * (m : ℝ) + 1) * 2 ^ m
  let pad : ℝ := N ^ (-(1 / (m : ℝ)) / (q : ℝ))
  let jetPad : ℝ := N ^ (-(1 / (q : ℝ)))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpad : 0 < pad := H.Npow_pos _
  have hjetPad : 0 < jetPad := H.Npow_pos _
  have hden : 0 < P + L + 1 := by linarith
  let δ := min (1 / 2 : ℝ) (min pad (jetPad / (P + L + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min hpad (div_pos hjetPad hden))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδpad : δ ≤ pad := (min_le_right _ _).trans (min_le_left _ _)
  have hδjet : (P + L) * δ ≤ jetPad := by
    have hd : δ ≤ jetPad / (P + L + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ hden).mp hd
    nlinarith [hδ.le]
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  let A := H.neighborRecords a
  let Codes := childrenOver S (F k) (F (k + 1)) hfinite A
  let Wd := targetWidthConstant m * N ^ ε
  let T := recordTubeUnion (m := m) β N (((k + 1 : ℕ) : ℝ) / q) (h k) (h (k + 1))
    (dcenter h k a.2) (ntime h k a a.2) (cref f₁ h k a) (jet0 J β m N f₁ h k a)
    (stageFromRecord J q (k + 1) β N h F S f₁ f₂) Codes Wd q pad
  refine ⟨T, measurableSet_recordTubeUnion H.hmJ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    H.volume_uniform_targets_le hfinite A u hdesc a, ?_⟩
  intro E W κ hE0 hpath x hx1 hx2
  subst a
  let U : Fin (m + 1) → ℝ := fun p =>
    codedControl J m k z q β N (dcenter h k (E 0).2) (cref f₁ h k (E 0) m)
      h F S f₁ f₂ (F k (W p)) (referencePalette m z q β N h f₁ f₂ (W p)) (!(κ p))
  let y : ℝ × (Fin m → ℝ) :=
    (ntime h k (E 0) (E (m + 1)).2, fun p => ntime h k (E 0) (E ((p : ℕ) + 1)).2)
  obtain ⟨hEA, hWA⟩ := H.path_neighbor_records hpath
  have hU : ∀ p, |U p| ≤ B := by
    intro p
    exact H.neighbor_controls_bound hεq hroot ha (hpath.memW p (by omega))
      (hWA p (by omega)) (!(κ p))
  have hs₀ : |ntime h k (E 0) (E 0).2| ≤ 1 :=
    (abs_ntime_le rfl).trans (by norm_num)
  have hy : |y.1| ≤ 1 / 2 ∧ ∀ p, |y.2 p| ≤ 1 / 2 := by
    refine ⟨abs_ntime_le ((H.path_floor hpath).1 (m + 1) le_rfl).symm, ?_⟩
    intro p
    exact abs_ntime_le ((H.path_floor hpath).1 ((p : ℕ) + 1) (by omega)).symm
  have hytime : y.1 ∈ tset h k (E 0) (E (m + 1)) := by
    change dcenter h k (E 0).2 + lamk h k * ntime h k (E 0) (E (m + 1)).2 ∈
      Icc (dleft h (k + 1) (E (m + 1)).2)
        (dleft h (k + 1) (E (m + 1)).2 + ((2 : ℝ) ^ h (k + 1))⁻¹)
    have heq : dcenter h k (E 0).2 + lamk h k * ntime h k (E 0) (E (m + 1)).2 =
        (E (m + 1)).2 := by
      unfold ntime
      field_simp [(lamk_pos h k).ne']
      ring
    rw [heq]
    exact ⟨dleft_le h _ _, (lt_dleft_add h _ _).le⟩
  have hcode : F (k + 1) (E (m + 1)) ∈ Codes := by
    exact (mem_childrenOver hfinite).mpr
      ⟨E (m + 1), hpath.memE (m + 1) le_rfl, hEA (m + 1) le_rfl, rfl⟩
  have hwidth : ∀ j : Fin m,
      endpointLoss m * N ^ ε * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))) +
        (B * (m : ℝ) * (4 * (m : ℝ) + 1) * 2 ^ m + L) * δ ≤
      Wd * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))) := by
    intro j
    have hm : (0 : ℝ) < m := by exact_mod_cast H.hm
    have hje : (((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ) ≤ 1 / (q : ℝ) := by
      apply div_le_div_of_nonneg_right _ H.q_pos.le
      apply (div_le_one hm).mpr
      exact_mod_cast j.isLt
    have hratio : jetPad ≤ N ^ ε * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))) := by
      apply (Real.rpow_le_rpow_of_exponent_le H.hN (neg_le_neg hje)).trans
      exact le_mul_of_one_le_left (H.Npow_pos _).le H.Nε_ge_one
    have herror := hδjet.trans hratio
    change (P + L) * δ ≤ _ at herror
    dsimp only [Wd, targetWidthConstant]
    nlinarith [H.Npow_pos (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))), H.Npow_pos ε]
  exact H.jitter_mem_recordTubeUnion (E 0) (hpath.memE (m + 1) le_rfl) (κ m)
    Codes hcode U hB hL hδ.le hδ2 hδpad hU hs₀
    (hcenter (E 0) ha (E (m + 1)) (hpath.memE (m + 1) le_rfl) (κ m)) y hy hytime
    (H.coded_path_endpoint hεq hroot hpath) hwidth x hx1 hx2

end Det

/-- Uniform geometric target construction with a coefficient depending only on the order. -/
theorem targetConstruction : TargetConstruction := by
  intro J q k m z β u γ
  refine ⟨targetVolumeConstant m, targetVolumeConstant_nonneg m, ?_⟩
  intro ε N n₁ n₂ f₁ f₂ h F S H hεq hroot hfinite hdesc
  exact H.uniform_targetCovers u hεq hroot (hfinite (k + 1) H.child_le_q).2
    (hdesc k (k + 1) (Nat.le_succ k) H.child_le_q)

end Submission.Obl.k4_matching_switching_target_certificate
