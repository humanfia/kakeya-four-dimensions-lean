/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/RecoveredLists.lean.
   This file retains the source's own provenance comments below. -/
import Mathlib

/-!
The final code labels are recovered from the deeper ORIGINAL path list and a
short list of parameter/midpoint codes. Candidate identities never enter the
output list. An injective enumeration of used codes inherits this bound.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

noncomputable section

def recoveredCodeList {β P D Code : Type*} [Fintype β]
    (key : β → P × Code) (ancestor : D → P) (S : Finset D) (small : D → Finset Code) :
    Finset β := by
  classical
  exact Finset.univ.filter fun b => ∃ d ∈ S,
    (key b).1 = ancestor d ∧ (key b).2 ∈ small d

theorem mem_recoveredCodeList {β P D Code : Type*} [Fintype β]
    (key : β → P × Code) (ancestor : D → P) (S : Finset D) (small : D → Finset Code) (b : β) :
    b ∈ recoveredCodeList key ancestor S small ↔
      ∃ d ∈ S, (key b).1 = ancestor d ∧ (key b).2 ∈ small d := by
  classical
  simp [recoveredCodeList]

theorem card_recoveredCodeList_le_sum {β P D Code : Type*} [Fintype β]
    (key : β → P × Code) (hkey : Function.Injective key)
    (ancestor : D → P) (S : Finset D) (small : D → Finset Code) :
    (recoveredCodeList key ancestor S small).card ≤ ∑ d ∈ S, (small d).card := by
  classical
  let allKeys := S.biUnion fun d => (small d).image (fun c => (ancestor d, c))
  have hsub : (recoveredCodeList key ancestor S small).image key ⊆ allKeys := by
    intro k hk
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨d, hd, hparent, hcode⟩ := (mem_recoveredCodeList key ancestor S small b).mp hb
    exact Finset.mem_biUnion.mpr ⟨d, hd,
      Finset.mem_image.mpr ⟨(key b).2, hcode, Prod.ext hparent.symm rfl⟩⟩
  calc
    _ = ((recoveredCodeList key ancestor S small).image key).card :=
      (Finset.card_image_of_injective _ hkey).symm
    _ ≤ allKeys.card := Finset.card_le_card hsub
    _ ≤ ∑ d ∈ S, ((small d).image (fun c => (ancestor d, c))).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun d _ => Finset.card_image_le

/-- A deep known list of size `K` and at most `R` short codes per deeper
label yield at most `K R` final labels, independent of candidate multiplicity. -/
theorem card_recoveredCodeList_le {β P D Code : Type*} [Fintype β]
    (key : β → P × Code) (hkey : Function.Injective key)
    (ancestor : D → P) (S : Finset D) (small : D → Finset Code) {K R : ℝ}
    (hS : (S.card : ℝ) ≤ K) (hR : 0 ≤ R)
    (hsmall : ∀ d ∈ S, ((small d).card : ℝ) ≤ R) :
    ((recoveredCodeList key ancestor S small).card : ℝ) ≤ K * R := by
  calc
    _ ≤ ∑ d ∈ S, ((small d).card : ℝ) := by
      exact_mod_cast card_recoveredCodeList_le_sum key hkey ancestor S small
    _ ≤ ∑ _d ∈ S, R := Finset.sum_le_sum hsmall
    _ = (S.card : ℝ) * R := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hS hR

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
