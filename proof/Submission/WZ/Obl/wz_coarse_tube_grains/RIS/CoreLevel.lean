-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CoreLevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.ShadingCore
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Counting
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalMultiplicity

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set
open scoped Classical

theorem multiplicity_mono {n : ℕ} {Y Z : Fin n → Set Space}
    (hsub : ∀ i, Y i ⊆ Z i) (p : Space) : multiplicity Y p ≤ multiplicity Z p := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hp : p ∈ Y i
  · simp only [Set.indicator_of_mem hp, Set.indicator_of_mem (hsub i hp), le_refl]
  · simp only [Set.indicator_of_notMem hp]
    exact bot_le

theorem fiberMultiplicity_mono {n N : ℕ} (f : Fin n → Fin N) {Y Z : Fin n → Set Space}
    (hsub : ∀ i, Y i ⊆ Z i) (j : Fin N) (p : Space) :
    fiberMultiplicity f Y j p ≤ fiberMultiplicity f Z j p := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hp : p ∈ Y i
  · simp only [Set.indicator_of_mem hp, Set.indicator_of_mem (hsub i hp), le_refl]
  · simp only [Set.indicator_of_notMem hp]
    exact bot_le

/-- The simultaneous core retains half the mass of a uniform multiplicity level,
with only a quarter-mass budget for occupied-fiber density. -/
theorem dense_core_of_uniform_level {n N : ℕ} (Y : Fin n → Set Space)
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, volume (Y i) ≠ ⊤)
    (f : Fin n → Fin N) (cost : Fin N → ENNReal) {M : ℝ} (hM : 0 ≤ M)
    (hlevel : ∀ p ∈ ⋃ i, Y i, ENNReal.ofReal M ≤ multiplicity Y p)
    (hcost : (∑ k, cost k) ≤ (1 / 4 : ENNReal) * ∑ i, volume (Y i)) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ENNReal) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
      (∀ k, (∃ i, f i = k ∧ (Z i).Nonempty) →
        cost k ≤ ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Z i)) ∧
      (∀ p ∈ ⋃ i, Z i, ENNReal.ofReal (M / 4) ≤ multiplicity Z p) := by
  have hmass := multiplicity_mul_volume_le_mass hY hlevel
  have hquarter : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hquarters : (1 / 4 : ENNReal) + 1 / 4 = 1 / 2 := by
    rw [← hquarter, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have he : ENNReal.ofReal (M / 4) = (1 / 4 : ENNReal) * ENNReal.ofReal M := by
    rw [show M / 4 = (1 / 4 : ℝ) * M by ring, ENNReal.ofReal_mul (by norm_num), hquarter]
  have hbudget : (∑ k, cost k) + ENNReal.ofReal (M / 4) * volume (⋃ i, Y i) ≤
      (1 / 2 : ENNReal) * ∑ i, volume (Y i) := by
    calc
      _ ≤ (1 / 4 : ENNReal) * (∑ i, volume (Y i)) +
          (1 / 4 : ENNReal) * (∑ i, volume (Y i)) := by
        apply add_le_add hcost
        rw [he, mul_assoc]
        exact mul_le_mul_right hmass _
      _ = _ := by rw [← add_mul, hquarters]
  obtain ⟨Z, hZ, hretain, hdense, hpoint⟩ :=
    measurable_shading_core_half volume Y hY hfin f cost (ENNReal.ofReal (M / 4)) hbudget
  refine ⟨Z, hZ, hretain, ?_, ?_⟩
  · intro k hk
    convert hdense k hk using 1
    congr 1
    ext i
    simp
  · intro p hp
    have hh := hpoint p hp
    rw [multiplicity_eq_ncard]
    have heq : Set.ncard {i | p ∈ Z i} = (Finset.univ.filter fun i => p ∈ Z i).card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp
    simpa only [heq] using hh

/-- A global fine lower level, divided by the fine multiplicity upper bound in
one packet, gives a packet lower level on the same union. -/
theorem packet_lower_of_fine_level {n N : ℕ} (f : Fin n → Fin N)
    (Y : Fin n → Set Space) (Q : Fin N → Set Space)
    (hcover : ∀ i, Y i ⊆ Q (f i)) (hunion : (⋃ j, Q j) ⊆ ⋃ i, Y i)
    {M B : ℝ} (hB : 0 < B)
    (hlower : ∀ p ∈ ⋃ i, Y i, ENNReal.ofReal M ≤ multiplicity Y p)
    (hupper : ∀ p j, fiberMultiplicity f Y j p ≤ ENNReal.ofReal B) :
    ∀ p ∈ ⋃ j, Q j, ENNReal.ofReal (M / B) ≤ multiplicity Q p := by
  intro p hp
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hB).ne'
    ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal B * ENNReal.ofReal (M / B) = ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_mul hB.le]
      congr 1
      field_simp
    _ ≤ multiplicity Y p := hlower p (hunion hp)
    _ ≤ _ := multiplicity_le_mul_of_fiber_bound f hcover (hupper p)

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
