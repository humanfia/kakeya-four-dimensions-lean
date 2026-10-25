import Submission.Lib.K4ScalarCoreAssembly.Support

namespace Submission.Obl.k4_conditional_common_affine_field

open Set
open Submission.Lib.K4ScalarCoreAssembly

/-- At most five old bins meet a one-width neighborhood of a fixed center. -/
noncomputable def nearbyCharts (χ x : ℝ) : Finset ℤ :=
  Finset.Icc (⌊x / χ⌋ - 2) (⌊x / χ⌋ + 2)

theorem card_nearbyCharts (χ x : ℝ) : (nearbyCharts χ x).card = 5 := by
  simp only [nearbyCharts, Int.card_Icc]
  have h : ⌊x / χ⌋ + 2 + 1 - (⌊x / χ⌋ - 2) = 5 := by ring
  rw [h]
  rfl

theorem floor_mem_nearbyCharts {χ x y : ℝ} (hχ : 0 < χ) (hxy : |x - y| ≤ χ) :
    ⌊x / χ⌋ ∈ nearbyCharts χ y := by
  have h := bounded_floor_offset_mem (L := 1) hχ (by simpa using hxy)
  norm_num only [one_mul, show (⌈(1 : ℝ) + 1⌉ : ℤ) = 2 by norm_num,
    Finset.mem_Icc] at h
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- The original chart lists in a bounded chart neighborhood. -/
noncomputable def chartMenu {β : Type*} (L : ℤ × ℤ → Finset β)
    (χb χv b v : ℝ) : Finset β := by
  classical
  exact (nearbyCharts χb b).biUnion fun i =>
    (nearbyCharts χv v).biUnion fun j => L (i, j)

theorem card_chartMenu {β : Type*} (L : ℤ × ℤ → Finset β)
    (χb χv b v K : ℝ) (hL : ∀ q, ((L q).card : ℝ) ≤ K) :
    ((chartMenu L χb χv b v).card : ℝ) ≤ 25 * K := by
  classical
  have hinner (i : ℤ) :
      (((nearbyCharts χv v).biUnion fun j => L (i,j)).card : ℝ) ≤ 5 * K := by
    calc
      _ ≤ ∑ j ∈ nearbyCharts χv v, ((L (i,j)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ nearbyCharts χv v, K := Finset.sum_le_sum fun j _ => hL _
      _ = 5 * K := by simp [card_nearbyCharts]
  calc
    _ ≤ ∑ i ∈ nearbyCharts χb b,
        (((nearbyCharts χv v).biUnion fun j => L (i,j)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ nearbyCharts χb b, 5*K := Finset.sum_le_sum fun i _ => hinner i
    _ = 25*K := by simp [card_nearbyCharts]; ring

theorem mem_chartMenu {β : Type*} (L : ℤ × ℤ → Finset β)
    {χb χv b v b₀ v₀ : ℝ} (hχb : 0 < χb) (hχv : 0 < χv)
    (hb : |b - b₀| ≤ χb) (hv : |v - v₀| ≤ χv)
    {a : β} (ha : a ∈ L (⌊b / χb⌋, ⌊v / χv⌋)) :
    a ∈ chartMenu L χb χv b₀ v₀ := by
  classical
  exact Finset.mem_biUnion.mpr ⟨_, floor_mem_nearbyCharts hχb hb,
    Finset.mem_biUnion.mpr ⟨_, floor_mem_nearbyCharts hχv hv, ha⟩⟩

theorem chartMenu_property {β : Type*} (L : ℤ × ℤ → Finset β)
    (χb χv b v : ℝ) (P : β → Prop) (hL : ∀ q, ∀ a ∈ L q, P a) :
    ∀ a ∈ chartMenu L χb χv b v, P a := by
  classical
  intro a ha
  obtain ⟨i, hi, ha⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨j, hj, ha⟩ := Finset.mem_biUnion.mp ha
  exact hL (i,j) a ha

end Submission.Obl.k4_conditional_common_affine_field
