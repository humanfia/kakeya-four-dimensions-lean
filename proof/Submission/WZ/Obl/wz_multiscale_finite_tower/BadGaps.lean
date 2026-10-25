-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.BadGaps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.UniformInsertion

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

noncomputable def badGaps (d g : ℝ) (J : ℕ) (r : ℕ → ℝ) : Finset ℕ :=
  (Finset.range J).filter fun j => r (j + 1) < d ^ g * r j

lemma mem_badGaps {d g : ℝ} {J j : ℕ} {r : ℕ → ℝ} :
    j ∈ badGaps d g J r ↔ j < J ∧ r (j + 1) < d ^ g * r j := by
  classical
  simp only [badGaps, Finset.mem_filter, Finset.mem_range]

lemma badGaps_card_le (d g : ℝ) (J : ℕ) (r : ℕ → ℝ) : (badGaps d g J r).card ≤ J :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range J)

lemma badGaps_empty {d g : ℝ} {J : ℕ} {r : ℕ → ℝ} (h : (badGaps d g J r).card = 0) :
    ∀ j, j < J → d ^ g * r j ≤ r (j + 1) := by
  intro j hj
  by_contra he
  have hh : j ∈ badGaps d g J r := mem_badGaps.mpr ⟨hj, lt_of_not_ge he⟩
  rw [Finset.card_eq_zero.mp h] at hh
  exact Finset.notMem_empty j hh

def insertRadii (k : ℕ) (s : ℝ) (r : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ k then r j else if j = k + 1 then s else r (j - 1)

lemma insertRadii_before {k j : ℕ} (s : ℝ) (r : ℕ → ℝ) (hj : j ≤ k) :
    insertRadii k s r j = r j := by simp only [insertRadii, ite_eq_left hj]

lemma insertRadii_middle (k : ℕ) (s : ℝ) (r : ℕ → ℝ) :
    insertRadii k s r (k + 1) = s := by simp [insertRadii]

lemma insertRadii_after {k j : ℕ} (s : ℝ) (r : ℕ → ℝ) (hj : k + 1 < j) :
    insertRadii k s r j = r (j - 1) := by
  simp only [insertRadii, ite_eq_right (by omega : ¬ j ≤ k), ite_eq_right (by omega : j ≠ k + 1)]

/-- A split whose two new edges meet the target mesh removes exactly one bad gap. -/
lemma badGaps_insert {d g s : ℝ} {J k : ℕ} {r : ℕ → ℝ} (hk : k < J)
    (hbad : r (k + 1) < d ^ g * r k)
    (hlo : d ^ g * r k ≤ s) (hhi : d ^ g * s ≤ r (k + 1)) :
    (badGaps d g (J + 1) (insertRadii k s r)).card + 1 = (badGaps d g J r).card := by
  classical
  let f : ℕ → ℕ := fun j => if j < k then j else j + 1
  have hf : Function.Injective f := by
    intro a b he
    dsimp only [f] at he
    split_ifs at he <;> omega
  have he : badGaps d g (J + 1) (insertRadii k s r) =
      ((badGaps d g J r).erase k).image f := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjJ, hjbad⟩ := mem_badGaps.mp hj
      by_cases hjk : j < k
      · have hjold : r (j + 1) < d ^ g * r j := by
          simpa only [insertRadii_before s r (by omega : j + 1 ≤ k), insertRadii_before s r hjk.le] using hjbad
        exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨by omega,
          mem_badGaps.mpr ⟨by omega, hjold⟩⟩, by simp only [f, ite_eq_left hjk]⟩
      · by_cases hejk : j = k
        · subst j
          rw [insertRadii_middle, insertRadii_before s r le_rfl] at hjbad
          exact False.elim (not_lt_of_ge hlo hjbad)
        · by_cases hejk' : j = k + 1
          · subst j
            rw [insertRadii_middle, insertRadii_after s r (by omega), show k + 1 + 1 - 1 = k + 1 by omega] at hjbad
            exact False.elim (not_lt_of_ge hhi hjbad)
          · have hjafter : k + 1 < j := by omega
            have hjold : r (j - 1 + 1) < d ^ g * r (j - 1) := by
              rw [insertRadii_after s r (by omega), insertRadii_after s r hjafter] at hjbad
              simpa only [show j + 1 - 1 = j - 1 + 1 by omega] using hjbad
            exact Finset.mem_image.mpr ⟨j - 1, Finset.mem_erase.mpr ⟨by omega,
              mem_badGaps.mpr ⟨by omega, hjold⟩⟩, by dsimp [f]; split_ifs <;> omega⟩
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hik, hi⟩ := Finset.mem_erase.mp hi
      obtain ⟨hiJ, hibad⟩ := mem_badGaps.mp hi
      by_cases hik' : i < k
      · simp only [f, ite_eq_left hik']
        exact mem_badGaps.mpr ⟨by omega, by
          simpa only [insertRadii_before s r (by omega : i + 1 ≤ k), insertRadii_before s r hik'.le] using hibad⟩
      · have hki : k < i := by omega
        simp only [f, ite_eq_right hik']
        refine mem_badGaps.mpr ⟨by omega, ?_⟩
        rw [insertRadii_after s r (by omega), insertRadii_after s r (by omega),
          show i + 1 + 1 - 1 = i + 1 by omega, show i + 1 - 1 = i by omega]
        exact hibad
  rw [he, Finset.card_image_of_injective _ hf]
  exact Finset.card_erase_add_one (mem_badGaps.mpr ⟨hk, hbad⟩)

noncomputable def HierarchyCertificate.improve_mesh {d θ g g' gap : ℝ} {J : ℕ}
    (C : HierarchyCertificate d θ g gap J)
    (h : (badGaps d g' J (fun j => (C.tree.layer j).radius)).card = 0) :
    HierarchyCertificate d θ g' gap J where
  tree := C.tree
  shading := C.shading
  root_axis := C.root_axis
  scalar := C.scalar
  control := { C.control with lower_gap := badGaps_empty h }
  alignment := C.alignment
  family := C.family

end WangZahlLot.Obl.wz_multiscale_finite_tower
