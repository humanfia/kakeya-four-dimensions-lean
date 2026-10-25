-- Adapted from this LOT tree, o080/x0272, Submission/Obl/k4_matching_geometric_path_cover/FinalRecords.lean.
import Submission.Obl.k4_matching_switching_target_certificate.Endpoint

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

lemma ntime_mem_child_interval {n₁ n₂ : ℕ} (h : ℕ → ℕ) (k : ℕ)
    (a y : (Fin n₁ × Fin n₂) × ℝ) :
    ntime h k a y.2 ∈ Icc (ntime h k a (dleft h (k + 1) y.2))
      (ntime h k a (dleft h (k + 1) y.2 + ((2 : ℝ) ^ h (k + 1))⁻¹)) := by
  constructor
  · exact div_le_div_of_nonneg_right (sub_le_sub_right (dleft_le h (k + 1) y.2) _)
      (lamk_pos h k).le
  · exact div_le_div_of_nonneg_right (sub_le_sub_right (lt_dleft_add h (k + 1) y.2).le _)
      (lamk_pos h k).le

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma child_le_q : k + 1 ≤ q := by have := H.hkq; omega

lemma child_center_eq {x y : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : F (k + 1) x = F (k + 1) y) :
    dcenter h (k + 1) x.2 = dcenter h (k + 1) y.2 :=
  dcenter_congr (H.rec_floor H.child_le_q hx hy hxy le_rfl)

lemma child_left_eq {x y : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : F (k + 1) x = F (k + 1) y) :
    dleft h (k + 1) x.2 = dleft h (k + 1) y.2 :=
  dleft_congr (H.rec_floor H.child_le_q hx hy hxy le_rfl)

lemma finBins_eq_of_child_record {x y : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : F (k + 1) x = F (k + 1) y) (κ : Bool) {i : ℕ} (hi : i ≤ J) :
    finBins J β q k N f₁ f₂ h x κ i = finBins J β q k N f₁ f₂ h y κ i :=
  H.rec_bin H.child_le_q hx hy hxy le_rfl hi κ

/-- The entire moving center of the target is determined by the final child
record and its final color. The final event itself need not be fixed. -/
lemma tcen_eq_of_child_record (a : (Fin n₁ × Fin n₂) × ℝ)
    {x y : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : F (k + 1) x = F (k + 1) y) (κ : Bool) (j : Fin m) (s : ℝ) :
    tcen J β q k m N f₁ f₂ h a x κ j s = tcen J β q k m N f₁ f₂ h a y κ j s := by
  let i₀ := m - 1 - (j : ℕ)
  have hi₀ : i₀ ≤ J := by have := j.isLt; have := H.hmJ; dsimp [i₀]; omega
  have hjet : binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ)) (finBins J β q k N f₁ f₂ h x κ)
        (dcenter h (k + 1) x.2) i₀ (dcenter h k a.2 + lamk h k * s) =
      binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ)) (finBins J β q k N f₁ f₂ h y κ)
        (dcenter h (k + 1) y.2) i₀ (dcenter h k a.2 + lamk h k * s) := by
    unfold binJet
    rw [H.child_center_eq hx hy hxy]
    apply Finset.sum_congr rfl
    intro i hi
    have hiJ : i₀ + i ≤ J := by have := Finset.mem_range.mp hi; omega
    rw [H.finBins_eq_of_child_record hx hy hxy κ hiJ]
  unfold tcen
  rw [hjet]

end Det

end Submission.Obl.k4_matching_switching_target_certificate
