import Submission.Obl.k4_horizontal_coefficient_count.Common

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- A finite cover by capped cells costs their number times the original
cell ceiling. No probability normalization or measurability of the
additional retained condition is required. -/
theorem measure_le_of_finite_cell_cover {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (code : Ω → Q) (condition : Ω → Prop)
    (F : Finset Q) {δ C V : ℝ} (hC : 0 ≤ C)
    (hcover : ∀ p ∈ E, code p ∈ F ∧ condition p)
    (hcount : (F.card : ℝ) * δ ^ 3 ≤ V)
    (hcap : ∀ q ∈ F, μ {p | code p = q ∧ condition p} ≤ ENNReal.ofReal (C * δ ^ 3)) :
    μ E ≤ ENNReal.ofReal (C * V) := by
  have hsub : E ⊆ ⋃ q ∈ F, {p | code p = q ∧ condition p} := by
    intro p hp
    exact mem_iUnion₂.mpr ⟨code p, (hcover p hp).1, rfl, (hcover p hp).2⟩
  calc
    μ E ≤ μ (⋃ q ∈ F, {p | code p = q ∧ condition p}) := measure_mono hsub
    _ ≤ ∑ q ∈ F, μ {p | code p = q ∧ condition p} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ F, ENNReal.ofReal (C * δ ^ 3) := Finset.sum_le_sum hcap
    _ = ENNReal.ofReal (C * ((F.card : ℝ) * δ ^ 3)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg F.card)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (C * V) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcount hC)

/-- Count complete, disjoint witness domains under one original-law mass
ceiling. The common fourth-power factor cancels before any restriction
to the parameter group. -/
theorem witness_count_of_fourth_power_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (E : ι → Set Ω) (U : Set Ω)
    {H θ C : ℝ} (hH : 0 < H) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hE : ∀ i ∈ S, MeasurableSet (E i))
    (hdisj : (S : Set ι).PairwiseDisjoint E)
    (hsub : ∀ i ∈ S, E i ⊆ U)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal (θ * H ^ 4) ≤ μ (E i))
    (hupper : μ U ≤ ENNReal.ofReal (C * H ^ 4)) :
    (S.card : ℝ) * θ ≤ C := by
  have hmass : ENNReal.ofReal ((S.card : ℝ) * (θ * H ^ 4)) ≤
      ENNReal.ofReal (C * H ^ 4) := by
    calc
      _ = ∑ _i ∈ S, ENNReal.ofReal (θ * H ^ 4) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg S.card),
          ENNReal.ofReal_natCast]
      _ ≤ ∑ i ∈ S, μ (E i) := Finset.sum_le_sum hfloor
      _ = μ (⋃ i ∈ S, E i) := (measure_biUnion_finset hdisj hE).symm
      _ ≤ μ U := measure_mono (iUnion₂_subset hsub)
      _ ≤ _ := hupper
  have hreal : (S.card : ℝ) * (θ * H ^ 4) ≤ C * H ^ 4 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (pow_nonneg hH.le _))).mp hmass
  apply (mul_le_mul_iff_left₀ (pow_pos hH 4)).mp
  simpa only [mul_assoc] using hreal

/-- Summing the finitely many unit scalar bins in the bounded residual
law gives the pure base cap needed for complete-box witness counts. -/
theorem pure_cell_cap_of_joint_cap {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → Q) (scalar : Ω → ℤ) (J : Finset ℤ)
    {δ C : ℝ} (hC : 0 ≤ C) (hsupport : μ {ω | scalar ω ∈ J}ᶜ = 0)
    (hcap : ∀ q : Q, ∀ j ∈ J,
      μ {ω | base ω = q ∧ scalar ω = j} ≤ ENNReal.ofReal (C * δ ^ 3)) :
    ∀ q : Q, μ {ω | base ω = q} ≤ ENNReal.ofReal ((J.card : ℝ) * C * δ ^ 3) := by
  intro q
  have heq : μ {ω | base ω = q} = μ {ω | base ω = q ∧ scalar ω ∈ J} := by
    exact (measure_inter_conull (s := {ω | base ω = q}) hsupport).symm
  rw [heq]
  convert measure_le_of_finite_cell_cover μ {ω | base ω = q ∧ scalar ω ∈ J}
    scalar (fun ω => base ω = q) J hC
    (fun ω hω => ⟨hω.2, hω.1⟩) le_rfl
    (fun j hj => by simpa only [and_comm] using hcap q j hj) using 1
  congr 1
  ring

end Submission.Obl.k4_horizontal_coefficient_count
