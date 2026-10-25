-- Adapted from this LOT tree, o080/x0272 commit 4d767e4, Submission/Obl/k4_matching_geometric_path_cover/ControlsOnNeighbors.lean.
import Submission.Obl.k4_matching_switching_target_certificate.PathNeighbors
import Submission.Obl.k4_matching_switching_target_certificate.CodedEndpoint

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma neighbor_controls_bound (hεq : ε ≤ 1 / (q : ℝ)) (hroot : 32 ≤ N ^ (1 / (q : ℝ)))
    {a e : (Fin n₁ × Fin n₂) × ℝ} (ha : a ∈ S) (he : e ∈ S)
    (hA : F k e ∈ H.neighborRecords a) (c : Bool) :
    |codedControl J m k z q β N (dcenter h k a.2) (cref f₁ h k a m)
      h F S f₁ f₂ (F k e) (referencePalette m z q β N h f₁ f₂ e) c| ≤
      (neighborRadius J m N ε : ℝ) + 2 + 5 * N ^ ε := by
  have hne := H.mem_neighborEvents_of_record he hA
  have hadm := H.active_at H.hzk (Nat.le_add_right k _)
  have hacc := jetAccuracy_active_order H.hJ β (H.level_nonneg k) H.hm H.hmJ hadm
  have hcenter : |iteratedDeriv m (if c then f₁ e.1.1 else f₂ e.1.2) (dcenter h k a.2) -
      cref f₁ h k a m| ≤ ((neighborRadius J m N ε : ℝ) + 1 + 5 * N ^ ε) * N ^ (-β m) := by
    have hb := H.neighbor_frame ha hne (!c) H.hmJ
    cases c <;> simpa only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false,
      ite_true, arm_false, arm_true, cref, hacc] using hb
  have h := H.coded_control_bound hεq hroot ha he (H.neighbor_floor hne).symm
    (cref f₁ h k a m) ((neighborRadius J m N ε : ℝ) + 1 + 5 * N ^ ε) c hcenter
  linarith

lemma neighbor_controls_separated (hεq : ε ≤ 1 / (q : ℝ))
    (hroot : 32 ≤ N ^ (1 / (q : ℝ))) {K : ℝ} (hK : 0 < K) (h4 : 4 * N ^ ε ≤ K)
    {a e : (Fin n₁ × Fin n₂) × ℝ} (ha : a ∈ S) (he : e ∈ S)
    (hA : F k e ∈ H.neighborRecords a) :
    2 / K ≤ |codedControl J m k z q β N (dcenter h k a.2) (cref f₁ h k a m)
        h F S f₁ f₂ (F k e) (referencePalette m z q β N h f₁ f₂ e) true -
      codedControl J m k z q β N (dcenter h k a.2) (cref f₁ h k a m)
        h F S f₁ f₂ (F k e) (referencePalette m z q β N h f₁ f₂ e) false| := by
  have hne := H.mem_neighborEvents_of_record he hA
  apply le_trans (b := N ^ (-ε) / 2)
  · calc 2 / K ≤ (1 / 2 : ℝ) / N ^ ε :=
        (div_le_div_iff₀ hK (H.Npow_pos ε)).mpr (by linarith)
      _ = N ^ (-ε) / 2 := by rw [Real.rpow_neg H.N_pos.le]; ring
  · exact H.coded_control_separation hεq hroot ha he (H.neighbor_floor hne).symm _

end Det

end Submission.Obl.k4_matching_switching_target_certificate
