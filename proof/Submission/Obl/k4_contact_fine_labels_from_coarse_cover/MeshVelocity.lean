-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/MeshVelocity.lean
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps
import Submission.Lib.K4HorizontalCoercivity.VelocityWitnesses

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open MeasureTheory Set

/-- The frozen velocity-bin caps also bound arbitrary short intervals. A
window of radius one mesh width uses at most five original bins. -/
theorem interval_mass_of_mesh_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (v : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (b : ENNReal) (hcap : ∀ a : ℤ, μ {p | p ∈ E ∧ ⌊v p / δ⌋ = a} ≤ b)
    (w : ℝ) : μ (E ∩ {p | |v p - w| ≤ δ}) ≤ 5 * b := by
  let S : Finset ℤ := Finset.Icc (-2) 2
  have hsub : E ∩ {p | |v p - w| ≤ δ} ⊆
      ⋃ a ∈ S, {p | p ∈ E ∧ ⌊v p / δ⌋ = ⌊w / δ⌋ + a} := by
    intro p hp
    have hmem := Submission.Obl.k4_fixed_budget_quadratic_recovery.floor_offset_mem
      hδ (show |v p - w| ≤ 1 * δ by simpa using hp.2)
    have hmem' : ⌊v p / δ⌋ - ⌊w / δ⌋ ∈ S := by
      simpa only [S, show Int.ceil ((1 : ℝ) + 1) = 2 by norm_num] using hmem
    exact mem_iUnion.mpr ⟨⌊v p / δ⌋ - ⌊w / δ⌋,
      mem_iUnion.mpr ⟨hmem', hp.1, by omega⟩⟩
  calc
    _ ≤ μ (⋃ a ∈ S, {p | p ∈ E ∧ ⌊v p / δ⌋ = ⌊w / δ⌋ + a}) := measure_mono hsub
    _ ≤ ∑ a ∈ S, μ {p | p ∈ E ∧ ⌊v p / δ⌋ = ⌊w / δ⌋ + a} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ S, b := Finset.sum_le_sum (fun a _ => hcap _)
    _ = 5 * b := by norm_num [S, Int.card_Icc]

/-- Actual separated witnesses follow directly from bin caps, including a
prescribed original null exception. There is no continuous-palette assumption. -/
theorem three_velocity_witnesses_of_mesh {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E G : Set Ω) (v : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (b : ENNReal) (hcap : ∀ a : ℤ, μ {p | p ∈ E ∧ ⌊v p / δ⌋ = a} ≤ b)
    (hG : ∀ᵐ p ∂μ, p ∈ G) (hmass : 10 * b < μ E) :
    ∃ p₀ ∈ E ∩ G, ∃ p₁ ∈ E ∩ G, ∃ p₂ ∈ E ∩ G,
      δ < |v p₀ - v p₁| ∧ δ < |v p₀ - v p₂| ∧ δ < |v p₁ - v p₂| := by
  apply Submission.Lib.K4HorizontalCoercivity.exists_three_velocity_witnesses
    μ (E ∩ G) v δ (5 * b)
  · intro w
    have hsub : (E ∩ G) ∩ {p | |v p - w| ≤ δ} ⊆ E ∩ {p | |v p - w| ≤ δ} :=
      fun p hp => ⟨hp.1.1, hp.2⟩
    exact (measure_mono hsub).trans
      (interval_mass_of_mesh_cap μ E v hδ b hcap w)
  · rw [measure_inter_conull (ae_iff.mp hG)]
    convert hmass using 1
    ring

/-- The original joint palette numerator passes to the actual-witness
criterion without changing the state reference weight. -/
theorem three_velocity_witnesses_of_original_palette {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E G : Set Ω) (v : Ω → ℝ) (π : Measure ℝ)
    {δ : ℝ} (hδ : 0 < δ) (C w b : ENNReal)
    (hcap : ∀ a : ℤ, μ {p | p ∈ E ∧ ⌊v p / δ⌋ = a} ≤
      C * w * π {u : ℝ | ⌊u / δ⌋ = a})
    (hπ : ∀ a : ℤ, π {u : ℝ | ⌊u / δ⌋ = a} ≤ b)
    (hG : ∀ᵐ p ∂μ, p ∈ G) (hmass : 10 * (C * w * b) < μ E) :
    ∃ p₀ ∈ E ∩ G, ∃ p₁ ∈ E ∩ G, ∃ p₂ ∈ E ∩ G,
      δ < |v p₀ - v p₁| ∧ δ < |v p₀ - v p₂| ∧ δ < |v p₁ - v p₂| := by
  apply three_velocity_witnesses_of_mesh μ E G v hδ (C * w * b) ?_ hG hmass
  intro a
  exact (hcap a).trans (mul_le_mul le_rfl (hπ a) bot_le bot_le)

/-- Every full true assignment has its own floor and palette numerator. Thus
it supplies separated actual velocities before any additional conditioning. -/
theorem three_velocity_witnesses_of_assignment {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (ν : Measure α) [IsProbabilityMeasure ν]
    (π : Measure ℝ) (A B : Set α) (I : Set ℝ) (G : Set (α × ℝ)) (v : α → ℝ)
    {K q δ β : ℝ} (hK : 0 < K) (hq : 0 < q) (hδ : 0 < δ) (hβ : 0 ≤ β)
    (hA : ν A ≠ 0)
    (hfloor : ENNReal.ofReal (q / K) * ν A ≤ μ (B ×ˢ I))
    (hcap : ∀ a : ℤ, μ {p | p ∈ B ×ˢ I ∧ ⌊v p.1 / δ⌋ = a} ≤
      ENNReal.ofReal (K * q) * ν A * π {u : ℝ | ⌊u / δ⌋ = a})
    (hπ : ∀ a : ℤ, π {u : ℝ | ⌊u / δ⌋ = a} ≤ ENNReal.ofReal β)
    (hG : ∀ᵐ p ∂μ, p ∈ G) (hsmall : 10 * K ^ 2 * β < 1) :
    ∃ p₀ ∈ (B ×ˢ I) ∩ G, ∃ p₁ ∈ (B ×ˢ I) ∩ G, ∃ p₂ ∈ (B ×ˢ I) ∩ G,
      δ < |v p₀.1 - v p₁.1| ∧ δ < |v p₀.1 - v p₂.1| ∧
        δ < |v p₁.1 - v p₂.1| := by
  let w : ENNReal := ENNReal.ofReal (q / K) * ν A
  have hw0 : w ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' hA
  have hwtop : w ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hcoeff : ENNReal.ofReal (10 * K ^ 2 * β) < 1 := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hsmall
  have hlt : ENNReal.ofReal (10 * K ^ 2 * β) * w < w := by
    simpa only [one_mul] using ENNReal.mul_lt_mul_left hw0 hwtop hcoeff
  have heq : 10 * (ENNReal.ofReal (K * q) * ν A * ENNReal.ofReal β) =
      ENNReal.ofReal (10 * K ^ 2 * β) * w := by
    have hnum : (10 : ENNReal) * ENNReal.ofReal (K * q) * ENNReal.ofReal β =
        ENNReal.ofReal (10 * (K * q) * β) := by
      rw [show (10 : ENNReal) = ENNReal.ofReal (10 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 10 * (K * q))]
    have hden : ENNReal.ofReal (10 * K ^ 2 * β) * ENNReal.ofReal (q / K) =
        ENNReal.ofReal (10 * (K * q) * β) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 10 * K ^ 2 * β)]
      congr 1
      field_simp
    calc
      _ = ((10 : ENNReal) * ENNReal.ofReal (K * q) * ENNReal.ofReal β) * ν A := by ring
      _ = ENNReal.ofReal (10 * (K * q) * β) * ν A := by rw [hnum]
      _ = _ := by dsimp [w]; rw [← hden]; ring
  apply three_velocity_witnesses_of_original_palette μ (B ×ˢ I) G
    (fun p => v p.1) π hδ (ENNReal.ofReal (K * q)) (ν A) (ENNReal.ofReal β)
    hcap hπ hG
  rw [heq]
  exact hlt.trans_le hfloor

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
