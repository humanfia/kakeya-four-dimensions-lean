import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Keys
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Prune
import Submission.Obl.k4_scalar_guarded_tangent_preparation.CodeVelocity

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set Finset
open Inherited.Native
open Submission.Obl.k4_scalar_guarded_tangent_preparation

noncomputable section

/-- All bin centers in a bounded physical interval. -/
def centerBins (δ L : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc ⌊-L / δ⌋ ⌈L / δ⌉).filter fun j => |(j : ℝ) * δ| ≤ L

theorem mem_centerBins {δ L : ℝ} (hδ : 0 < δ) (j : ℤ) :
    j ∈ centerBins δ L ↔ |(j : ℝ) * δ| ≤ L := by
  classical
  unfold centerBins
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hj
    have h := abs_le.mp hj
    have hlo : -L / δ ≤ (j : ℝ) := (div_le_iff₀ hδ).mpr h.1
    have hhi : (j : ℝ) ≤ L / δ := (le_div_iff₀ hδ).mpr h.2
    exact ⟨Finset.mem_Icc.mpr ⟨by simpa using Int.floor_mono hlo,
      by simpa using Int.ceil_mono hhi⟩, hj⟩

/-- A finite universal key box, bounded in the original physical units.
Its cardinality is never used in the reference budgets. -/
def boundedKeys (χ m L : ℝ) : Finset (Fin 3 → ℤ) :=
  keyBox (centerBins χ L) (fun _ => centerBins χ L) (fun _ _ => centerBins m L)

theorem boundedKeys_bound {χ m L : ℝ} {key : Fin 3 → ℤ}
    (hk : key ∈ boundedKeys χ m L) :
    |(key 0 : ℝ) * χ| ≤ L ∧ |(key 1 : ℝ) * χ| ≤ L ∧ |(key 2 : ℝ) * m| ≤ L := by
  classical
  obtain ⟨⟨v, z, y⟩, hmem, heq⟩ := Finset.mem_image.mp hk
  simp only [Finset.mem_sigma] at hmem
  subst key
  simp only [Matrix.cons_val]
  exact ⟨(Finset.mem_filter.mp hmem.1).2, (Finset.mem_filter.mp hmem.2.1).2,
    (Finset.mem_filter.mp hmem.2.2).2⟩

theorem mem_boundedKeys {χ m L : ℝ} (hχ : 0 < χ) (hm : 0 < m) (key : Fin 3 → ℤ)
    (h0 : |(key 0 : ℝ) * χ| ≤ L) (h1 : |(key 1 : ℝ) * χ| ≤ L)
    (h2 : |(key 2 : ℝ) * m| ≤ L) : key ∈ boundedKeys χ m L :=
  mem_keyBox ((mem_centerBins hχ _).mpr h0) ((mem_centerBins hχ _).mpr h1)
    ((mem_centerBins hm _).mpr h2)

/-- Bounded projected labels lie in the universal box in every native
unit-time slot, without selecting or counting velocity bins. -/
theorem slotKey_mem_boundedKeys {α : Type} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} {l : α} {χ m t₀ H L : ℝ}
    (hχ : 0 < χ) (hm : 0 < m) (hχ1 : χ ≤ 1) (hm1 : m ≤ 1)
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hb : ∀ e, |b l e| ≤ H) (hL : 2 * H + 1 ≤ L) :
    slotKey b χ m t₀ l ∈ boundedKeys χ m L := by
  have hH : 0 ≤ H := (abs_nonneg _).trans (hb 0)
  have ht : |t₀| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht₀.1, ht₀.2]
  have hcenter {x δ : ℝ} (hδ : 0 < δ) (hx : |x| ≤ H) (hδ1 : δ ≤ 1) :
      |(⌊x / δ⌋ : ℝ) * δ| ≤ L := by
    have he := floor_center_error hδ ⌊x / δ⌋ rfl
    have hh : |(⌊x / δ⌋ : ℝ) * δ| ≤ |x| + |x - (⌊x / δ⌋ : ℝ) * δ| := by
      have hh := abs_sub_abs_le_abs_sub ((⌊x / δ⌋ : ℝ) * δ) x
      rw [abs_sub_comm] at hh
      linarith
    exact hh.trans (by linarith)
  have hY : |b l 1 + t₀ * b l 4| ≤ 2 * H := by
    calc |b l 1 + t₀ * b l 4| ≤ |b l 1| + |t₀ * b l 4| := abs_add_le _ _
      _ ≤ H + 1 * H := by rw [abs_mul]; gcongr <;> exact hb _
      _ = 2 * H := by ring
  apply mem_boundedKeys hχ hm
  · exact hcenter hχ (hb 3) hχ1
  · exact hcenter hχ (hb 0) hχ1
  · have he := floor_center_error hm ⌊(b l 1 + t₀ * b l 4) / m⌋ rfl
    change |(⌊(b l 1 + t₀ * b l 4) / m⌋ : ℝ) * m| ≤ L
    have hh := abs_sub_abs_le_abs_sub ((⌊(b l 1 + t₀ * b l 4) / m⌋ : ℝ) * m)
      (b l 1 + t₀ * b l 4)
    rw [abs_sub_comm] at hh
    linarith

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
