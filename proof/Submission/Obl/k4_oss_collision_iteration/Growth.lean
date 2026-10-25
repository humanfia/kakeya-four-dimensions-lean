import Submission.Obl.k4_oss_collision_cauchy_schwarz

open MeasureTheory Set
open scoped ENNReal

/-!
Adapted from this LOT tree's o026, session x0068, commit 919377f,
`Submission/Obl/k4_oss_unit_decay/CollisionGrowth.lean`.
The source used the accepted o023 cell and collision Cauchy--Schwarz APIs.
-/

namespace Submission.Obl.k4_oss_collision_iteration

open Submission.Obl.k4_oss_collision_cauchy_schwarz

lemma shifted_collision_le (α : Measure ℝ) [SFinite α] {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    (α.prod α) {p : ℝ × ℝ | |p.1 - p.2 - a| ≤ 4 * δ} ≤ 13 * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
  let c : ℤ := ⌊-a / δ⌋
  let J : Finset ℤ := Finset.Icc (c - 6) (c + 6)
  let E (j : ℤ) : Set (ℝ × ℝ) := {p | ⌊p.2 / δ⌋ = ⌊p.1 / δ⌋ + j}
  have hsub : {p : ℝ × ℝ | |p.1 - p.2 - a| ≤ 4 * δ} ⊆ ⋃ j ∈ J, E j := by
    intro p hp
    let j : ℤ := ⌊p.2 / δ⌋ - ⌊p.1 / δ⌋
    have hj : j ∈ J := by
      have hpd : |p.1 / δ - p.2 / δ - a / δ| ≤ 4 := by
        rw [← sub_div, ← sub_div, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
        exact hp
      have hx := Int.floor_le (p.1 / δ)
      have hx' := Int.lt_floor_add_one (p.1 / δ)
      have hy := Int.floor_le (p.2 / δ)
      have hy' := Int.lt_floor_add_one (p.2 / δ)
      have hc := Int.floor_le (-a / δ)
      have hc' := Int.lt_floor_add_one (-a / δ)
      rw [abs_le] at hpd
      simp only [J, Finset.mem_Icc]
      constructor
      · have hh : ((c - 6 : ℤ) : ℝ) ≤ (j : ℝ) := by
          dsimp [c, j]
          push_cast
          simp only [neg_div] at hc hc' ⊢
          linarith
        exact_mod_cast hh
      · have hh : (j : ℝ) ≤ ((c + 6 : ℤ) : ℝ) := by
          dsimp [c, j]
          push_cast
          simp only [neg_div] at hc hc' ⊢
          linarith
        exact_mod_cast hh
    refine mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, ?_⟩⟩
    dsimp [E, j]
    omega
  have hE (j : ℤ) : (α.prod α) (E j) ≤ (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
    rw [show (α.prod α) (E j) =
      ∑' k : ℤ, α (cell δ k) * α (cell δ (k + j)) from
      shift_event_measure α (fun x => ⌊x / δ⌋) (by fun_prop) j]
    exact (tsum_mul_shift_le (fun k => α (cell δ k)) j).trans
      (cell_energy_le_collision α hδ)
  have hcard : J.card = 13 := by
    simp [J, Int.card_Icc, show c + 6 + 1 - (c - 6) = 13 by ring]
  calc
    _ ≤ (α.prod α) (⋃ j ∈ J, E j) := measure_mono hsub
    _ ≤ ∑ j ∈ J, (α.prod α) (E j) := measure_biUnion_finset_le J E
    _ ≤ ∑ j ∈ J, (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := Finset.sum_le_sum fun j _ => hE j
    _ = 13 * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by simp [hcard, nsmul_eq_mul]

lemma projection_collision_le (α β : Measure ℝ) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] {δ : ℝ} (hδ : 0 < δ)
    (hβ : β (Icc (1 : ℝ) 2)ᶜ = 0) :
    MeasureTheory.lintegral (β.prod β) (fun p : ℝ × ℝ =>
      ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) |
        |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ}) ≤ 13 * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
  have hb : ∀ᵐ y ∂β, 1 ≤ y := by
    have hh : ∀ᵐ y ∂β, y ∈ Icc (1 : ℝ) 2 := hβ
    exact hh.mono fun _ hy => hy.1
  have hbb : ∀ᵐ p ∂β.prod β, 1 ≤ p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hb] with y hy
    exact Filter.Eventually.of_forall fun _ => hy
  calc
    _ ≤ ∫⁻ _p : ℝ × ℝ, 13 * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ∂β.prod β := by
      apply lintegral_mono_ae
      filter_upwards [hbb] with p hp
      rw [Measure.prod_apply_symm (by measurability)]
      calc
        _ ≤ ∫⁻ _q : ℝ × ℝ, 13 * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ∂α.prod α := by
          apply lintegral_mono
          intro q
          dsimp only
          calc
            _ ≤ (α.prod α) {z : ℝ × ℝ |
                |z.1 - z.2 - (p.2 * (q.1 - q.2)) / p.1| ≤ 4 * δ} := by
              apply measure_mono
              intro z hz
              simp only [mem_preimage, mem_ofPred_eq] at hz ⊢
              have hp0 : 0 < p.1 := by linarith
              have he : z.1 - z.2 - p.2 * (q.1 - q.2) / p.1 =
                  (p.1 * (z.1 - z.2) - p.2 * (q.1 - q.2)) / p.1 := by
                field_simp
              rw [he]
              rw [abs_div, abs_of_pos hp0, div_le_iff₀ hp0]
              rw [abs_le] at hz ⊢
              constructor <;> nlinarith
            _ ≤ _ := shifted_collision_le α hδ _
        _ = _ := by simp
    _ = _ := by simp

/-- A mixing step increases collisions by at most a fixed universal factor. -/
theorem collision_mix_le {r : ℝ} (hr : 0 < r) (α β : Measure ℝ)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hβ : β (Icc (1 : ℝ) 2)ᶜ = 0) (ω : Measure ℝ)
    (hω : ω = Measure.map (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (q.1.1 * q.1.2 - q.2.1 * q.2.2) / 4) ((α.prod β).prod (α.prod β))) :
    (ω.prod ω) {p : ℝ × ℝ | |p.1 - p.2| ≤ r} ≤
      39 * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ r} := by
  have hcs := Submission.k4_oss_collision_cauchy_schwarz r hr α β
    inferInstance inferInstance ω hω
  apply hcs.trans
  calc
    _ ≤ 3 * (13 * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ r}) := by
      gcongr
      exact projection_collision_le α β hr hβ
    _ = _ := by norm_num [← mul_assoc]

end Submission.Obl.k4_oss_collision_iteration
