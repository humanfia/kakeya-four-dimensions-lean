/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarWindowCovers.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarWindowCovers.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridIndices
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Choose

/-! Fixed reading lists from the selected original starting-bin windows. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set
open scoped BigOperators

theorem scalar_interval_grid_list {R p : ℝ} (hR : 0 ≤ R) (hp : 0 < p) (center : ℝ) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ 2 * R / p + 3 ∧
      ∀ x : ℝ, |x - center| ≤ R → (⌊x / p⌋ : ℤ) ∈ J := by
  let J := Finset.Icc ⌊(center - R) / p⌋ ⌊(center + R) / p⌋
  have horder : ⌊(center - R) / p⌋ ≤ ⌊(center + R) / p⌋ :=
    Int.floor_mono ((div_le_div_iff_of_pos_right hp).mpr (by linarith))
  have hcountZ := Int.card_Icc_of_le
    (a := ⌊(center - R) / p⌋) (b := ⌊(center + R) / p⌋) (by omega)
  have hcountR : (J.card : ℝ) = (⌊(center + R) / p⌋ : ℝ) + 1 - ⌊(center - R) / p⌋ := by
    exact_mod_cast hcountZ
  refine ⟨J, ?_, ?_⟩
  · rw [hcountR]
    have hlo := Int.lt_floor_add_one ((center - R) / p)
    have hhi := Int.floor_le ((center + R) / p)
    have he : (center + R) / p - (center - R) / p = 2 * R / p := by ring
    linarith
  · intro x hx
    have hh := abs_le.mp hx
    exact Finset.mem_Icc.mpr
      ⟨Int.floor_mono ((div_le_div_iff_of_pos_right hp).mpr (by linarith [hh.1])),
        Int.floor_mono ((div_le_div_iff_of_pos_right hp).mpr (by linarith [hh.2]))⟩

theorem normalized_scalar_bin_near_start {H C x : ℝ} (hH : 0 < H) (bin : ℤ)
    (hbound : |(x - H * bin) / H| ≤ C) :
    |(⌊x / H⌋ : ℝ) - bin| ≤ C + 1 := by
  have hx : |x - H * bin| ≤ C * H := by
    rw [abs_div, abs_of_pos hH] at hbound
    exact (div_le_iff₀ hH).mp hbound
  have hh := mesh_index_close hH hx
  simpa only [mesh_lower_endpoint_index hH bin] using hh

theorem scalar_reading_cover_of_group_windows {Λ : Type*}
    (A : Set Λ) (group current : Λ → ℤ) (jet : Λ → ℝ) (center : ℤ → ℝ)
    {C K r : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hr : 0 < r)
    (hnear : ∀ l ∈ A, |(group l : ℝ) - current l| ≤ C)
    (hwindow : ∀ l ∈ A, |jet l - center (group l)| ≤ K * r) :
    ∃ J : ℤ → Finset ℤ, (∀ z, ((J z).card : ℝ) ≤ (2 * C + 3) * (2 * K + 3)) ∧
      ∀ l ∈ A, (⌊jet l / r⌋ : ℤ) ∈ J (current l) := by
  classical
  choose I hIcard hIcover using fun z : ℤ => scalar_interval_grid_list hC (by norm_num : (0 : ℝ) < 1) z
  choose Q hQcard hQcover using fun b : ℤ => scalar_interval_grid_list
    (mul_nonneg hK hr.le) hr (center b)
  let J : ℤ → Finset ℤ := fun z => (I z).biUnion Q
  have hQcard' b : ((Q b).card : ℝ) ≤ 2 * K + 3 := by
    have he : 2 * (K * r) / r + 3 = 2 * K + 3 := by field_simp
    simpa only [he] using hQcard b
  refine ⟨J, ?_, ?_⟩
  · intro z
    have hu : ((J z).card : ℝ) ≤ ∑ b ∈ I z, ((Q b).card : ℝ) := by
      change (((I z).biUnion Q).card : ℝ) ≤ _
      exact_mod_cast (Finset.card_biUnion_le : ((I z).biUnion Q).card ≤ ∑ b ∈ I z, (Q b).card)
    calc
      _ ≤ ∑ b ∈ I z, ((Q b).card : ℝ) := hu
      _ ≤ ∑ _b ∈ I z, (2 * K + 3) := Finset.sum_le_sum (fun b _ => hQcard' b)
      _ = ((I z).card : ℝ) * (2 * K + 3) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [div_one] using hIcard z) (by positivity)
  · intro l hl
    have hg : group l ∈ I (current l) := by
      simpa only [div_one, Int.floor_intCast] using hIcover (current l) (group l) (hnear l hl)
    exact Finset.mem_biUnion.mpr ⟨group l, hg, hQcover (group l) (jet l) (hwindow l hl)⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
