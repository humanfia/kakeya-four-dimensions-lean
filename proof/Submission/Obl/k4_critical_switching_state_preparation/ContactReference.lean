/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/ContactReference.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/ContactReference.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.ContactPairs

namespace Submission.Obl.k4_critical_switching_state_preparation

open Inherited

noncomputable section

/-- A reference horizontal line through the exact midpoint of a true box. -/
def boxReference (c : Fin 5 → ℝ) (m : ℝ) : Fin 3 → ℝ :=
  ![c 0, c 2 + m * c 3 + c 4 * (c 0 + m * c 1) + m * c 0, c 1]

/-- Centering the reference line at the midpoint places the complete true
box in a contact rectangle with fourth-power volume. -/
theorem true_box_in_contact_box (c : Fin 5 → ℝ) (m H K : ℝ)
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hm : |m| ≤ 1)
    (hc : |c 1| ≤ K) (hcenter : |c 3 + c 0 + m * c 1| ≤ K * H)
    (htilt : |c 4 - m| ≤ K * H) :
    horizontalTrueBox c m H K ⊆
      contactOuterBox m (boxReference c m) H (8 * K * H) (32 * K ^ 2 * H ^ 2) := by
  let q₀ : Fin 3 → ℝ := ![m, c 0 + m * c 1,
    c 2 + m * c 3 + c 4 * (c 0 + m * c 1)]
  have hq₀ : q₀ ∈ horizontalTrueBox c m H K := by
    dsimp [q₀, horizontalTrueBox]
    constructor
    · simpa using (by positivity : (0 : ℝ) ≤ H / 2)
    constructor
    · have : c 0 + m * c 1 - c 0 - m * c 1 = 0 := by ring
      rw [this, abs_zero]
      positivity
    · have : c 2 + m * c 3 + c 4 * (c 0 + m * c 1) - c 2 - m * c 3 -
          c 4 * (c 0 + m * c 1) = 0 := by ring
      rw [this, abs_zero]
      positivity
  have hz : |q₀ 1 - referenceZ (boxReference c m) (q₀ 0)| ≤ K * 0 := by
    simp [q₀, boxReference, referenceZ]
  have hy : |q₀ 2 - referenceY (boxReference c m) (q₀ 0)| ≤ K * 0 := by
    simp [q₀, boxReference, referenceY]
  have hbound := horizontalTrueBox_common_contact c (boxReference c m) q₀ m H K 0
    hH hH1 hK (by positivity) hm hc hc hcenter htilt hq₀ hz hy
  intro q hq
  exact (mem_contactOuterBox_iff _ _ _ _ _ _).mpr ⟨hq.1, hbound q hq⟩

/-- The upper occupied-pair estimate on a complete true box. -/
theorem true_box_intercept_pair_count
    (F : Finset (ℤ × (Fin 3 → ℤ)))
    (point : ℤ × (Fin 3 → ℤ) → Fin 3 → ℝ)
    (value : ℤ × (Fin 3 → ℤ) → ℝ)
    (A : Fin 4 → ℝ) (c : Fin 5 → ℝ) (m H K δ a M : ℝ)
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hδ : 0 < δ)
    (hδH : δ ≤ H ^ 2) (ha : 0 < a) (hM : 0 ≤ M)
    (hm : |m| ≤ 1) (hv : |c 1| ≤ K) (hposition : |c 0 + m * c 1| ≤ K)
    (hcenter : |c 3 + c 0 + m * c 1| ≤ K * H)
    (htilt : |c 4 - m| ≤ K * H)
    (hA : ∀ i : Fin 3, |A i.succ| ≤ M) (hmesh : 3 * M * δ ≤ K * a)
    (hpoint : ∀ u ∈ F, point u ∈ contactGridCell δ u.2 ∧
      point u ∈ horizontalTrueBox c m H K)
    (hbin : ∀ u ∈ F, ⌊value u / a⌋ = u.1)
    (hfit : ∀ u ∈ F, |value u - affineBaseEval A (point u)| ≤ 2 * K * a) :
    (F.card : ℝ) * δ ^ 3 ≤ 4194304 * K ^ 4 * H ^ 4 := by
  exact contact_intercept_pair_count F point value A (boxReference c m) m H K δ a M
    hH hH1 hK hδ hδH ha hM hm hv hposition hA hmesh
    (fun u hu => ⟨(hpoint u hu).1,
      true_box_in_contact_box c m H K hH hH1 hK hm hv hcenter htilt (hpoint u hu).2⟩)
    hbin hfit

end

end Submission.Obl.k4_critical_switching_state_preparation
