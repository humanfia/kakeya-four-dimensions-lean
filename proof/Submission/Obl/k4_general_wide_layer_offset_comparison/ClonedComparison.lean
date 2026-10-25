-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ClonedComparison.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

/- Adapted within this LOT tree from o247/x0870, commit 5d56dd4b,
Submission/Obl/k4_wide_common_field_velocity_lists/ClonedComparison.lean.
Uniform-copy kernels are imported from the gate-accepted library. -/
import Submission.Lib.K4OriginalStatePreparation.Copies
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.DyadicMatching

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Metric
open Submission.Lib.K4OriginalStatePreparation
open k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

/-- A comparison law with the two original layer weights kept separate.
The only difference from the accepted discrepancy setup is the unequal
source and witness density ceilings. -/
structure TwoWeightComparison (ι₁ ι₂ Λ Ω : Type*) [MeasurableSpace Ω] where
  law : Measure Ω
  lab₁ : ι₁ → Λ
  lab₂ : ι₂ → Λ
  φ₁ : ι₁ → EuclideanSpace ℂ (Fin 3) → ℂ
  φ₂ : ι₂ → EuclideanSpace ℂ (Fin 3) → ℂ
  src : Ω → ι₁
  wit : Ω → ι₂
  point : Ω → EuclideanSpace ℝ (Fin 3)
  value : Ω → ℝ
  error : ℝ
  K : ℝ
  weight₁ : Λ → ℝ
  weight₂ : Λ → ℝ
  finite : IsFiniteMeasure law
  sheet₁ : ∀ i, IsMatchSheet (φ₁ i)
  sheet₂ : ∀ i, IsMatchSheet (φ₂ i)
  src_meas : ∀ i, MeasurableSet {p | src p = i}
  wit_meas : ∀ i, MeasurableSet {p | wit p = i}
  point_meas : Measurable point
  lab_eq : ∀ p, lab₁ (src p) = lab₂ (wit p)
  point_mem : ∀ p, ‖point p‖ ≤ 1 / 2
  error_pos : 0 < error
  near_src : ∀ p, ‖φ₁ (src p) (emb (point p)) - (value p : ℂ)‖ ≤ error
  near_wit : ∀ p, ‖φ₂ (wit p) (emb (point p)) - (value p : ℂ)‖ ≤ error
  K_nonneg : 0 ≤ K
  weight₁_nonneg : ∀ l, 0 ≤ weight₁ l
  weight₂_nonneg : ∀ l, 0 ≤ weight₂ l
  density_src : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    law {p | src p = i ∧ point p ∈ U} ≤
      ENNReal.ofReal (K * weight₁ (lab₁ i)) * volume U
  density_wit : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    law {p | wit p = i ∧ point p ∈ U} ≤
      ENNReal.ofReal (K * weight₂ (lab₂ i)) * volume U

namespace TwoWeightComparison

variable {ι₁ ι₂ Λ Ω : Type*} [MeasurableSpace Ω]
    (S : TwoWeightComparison ι₁ ι₂ Λ Ω)

/-- Uniformly splitting source indices brings both colors to the fine
original weight. The underlying physical law is unchanged after forgetting
the new independent finite index. -/
def cloned (r : ℕ) (hr : 0 < r)
    (hweights : ∀ l, S.weight₁ l ≤ (r : ℝ) * S.weight₂ l) :
    DiscSetup ((ι₁ × Fin r) ⊕ ι₂) Λ (Ω × Fin r) := by
  letI := S.finite
  refine
    { Pm := uniformCopies S.law r
      lab := Sum.elim (fun p => S.lab₁ p.1) S.lab₂
      φ := Sum.elim (fun p => S.φ₁ p.1) S.φ₂
      src := fun p => Sum.inl (S.src p.1, p.2)
      wit := fun p => Sum.inr (S.wit p.1)
      x := fun p => S.point p.1
      w := fun p => S.value p.1
      Δ := S.error
      ρ := fun l => S.K * S.weight₂ l
      finite := uniformCopies_finite S.law hr
      sheet := ?_
      src_meas := ?_
      wit_meas := ?_
      x_meas := S.point_meas.comp measurable_fst
      lab_eq := fun p => S.lab_eq p.1
      x_mem := fun p => S.point_mem p.1
      Δ_pos := S.error_pos
      near_src := fun p => S.near_src p.1
      near_wit := fun p => S.near_wit p.1
      ρ_nonneg := fun l => mul_nonneg S.K_nonneg (S.weight₂_nonneg l)
      dens_src := ?_
      dens_wit := ?_ }
  · intro i
    rcases i with ⟨i, j⟩ | i
    · exact S.sheet₁ i
    · exact S.sheet₂ i
  · intro i
    rcases i with ⟨i, j⟩ | i
    · have heq : {p : Ω × Fin r | Sum.inl (S.src p.1, p.2) =
          (Sum.inl (i, j) : (ι₁ × Fin r) ⊕ ι₂)} = {p | S.src p = i} ×ˢ {j} := by
        ext p
        simp
      rw [heq]
      exact (S.src_meas i).prod (measurableSet_singleton j)
    · have heq : {p : Ω × Fin r | Sum.inl (S.src p.1, p.2) =
          (Sum.inr i : (ι₁ × Fin r) ⊕ ι₂)} = ∅ := by ext p; simp
      rw [heq]
      exact MeasurableSet.empty
  · intro i
    rcases i with ⟨i, j⟩ | i
    · have heq : {p : Ω × Fin r | Sum.inr (S.wit p.1) =
          (Sum.inl (i, j) : (ι₁ × Fin r) ⊕ ι₂)} = ∅ := by ext p; simp
      rw [heq]
      exact MeasurableSet.empty
    · have heq : {p : Ω × Fin r | Sum.inr (S.wit p.1) =
          (Sum.inr i : (ι₁ × Fin r) ⊕ ι₂)} = Prod.fst ⁻¹' {p | S.wit p = i} := by
        ext p
        simp
      rw [heq]
      exact (S.wit_meas i).preimage measurable_fst
  · intro i U hU
    rcases i with ⟨i, j⟩ | i
    · have heq : {p : Ω × Fin r | Sum.inl (S.src p.1, p.2) =
            (Sum.inl (i, j) : (ι₁ × Fin r) ⊕ ι₂) ∧ S.point p.1 ∈ U} =
          {p | S.src p = i ∧ S.point p ∈ U} ×ˢ {j} := by
        ext p
        simp only [Sum.inl.injEq, Prod.mk.injEq, mem_ofPred_eq, mem_prod,
          mem_singleton_iff]
        tauto
      rw [heq]
      apply uniformCopies_cap S.law hr _ j (S.K * S.weight₂ (S.lab₁ i)) (volume U)
      refine (S.density_src i U hU).trans ?_
      apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have h := mul_le_mul_of_nonneg_left (hweights (S.lab₁ i)) S.K_nonneg
      nlinarith
    · have heq : {p : Ω × Fin r | Sum.inl (S.src p.1, p.2) =
            (Sum.inr i : (ι₁ × Fin r) ⊕ ι₂) ∧ S.point p.1 ∈ U} = ∅ := by
        ext p
        simp
      rw [heq, measure_empty]
      exact zero_le
  · intro i U hU
    rcases i with ⟨i, j⟩ | i
    · have heq : {p : Ω × Fin r | Sum.inr (S.wit p.1) =
            (Sum.inl (i, j) : (ι₁ × Fin r) ⊕ ι₂) ∧ S.point p.1 ∈ U} = ∅ := by
        ext p
        simp
      rw [heq, measure_empty]
      exact zero_le
    · have heq : {p : Ω × Fin r | Sum.inr (S.wit p.1) =
            (Sum.inr i : (ι₁ × Fin r) ⊕ ι₂) ∧ S.point p.1 ∈ U} =
          Prod.fst ⁻¹' {p | S.wit p = i ∧ S.point p ∈ U} := by
        ext p
        simp
      rw [heq, uniformCopies_preimage S.law hr]
      exact S.density_wit i U hU

/-- The accepted geometric discrepancy theorem applies to the copied
indices with their common fine density ceiling, and the conclusion returns
to the original pair law exactly. -/
theorem discrepancy_mass_le [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq Λ]
    (r : ℕ) (hr : 0 < r)
    (hweights : ∀ l, S.weight₁ l ≤ (r : ℝ) * S.weight₂ l)
    (J : JetData) (M₀ : ℝ) (θ G : Λ → ℝ)
    {d₀ ε₀ R₀ ε χ d : ℝ} (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hM₀ : 0 < M₀)
    (hχ : 0 < χ) (hχ1 : χ < 1) (hθ : ∀ l, 0 < θ l) (hG : ∀ l, 0 ≤ G l)
    (hR : R₀ * (2 * S.error) ≤ M₀)
    (hC : 3 * J.C₂ ≤ (M₀ / (2 * S.error)) ^ ε)
    (hρ : ∀ l, (S.K * S.weight₂ l) * (M₀ / (2 * S.error)) ^ (-ε) ≤ θ l / 2)
    (hρgrow : (2 : ℝ) ^ (-ε) ≤ χ)
    (hΓ : ∀ l, G l / θ l ≤ (M₀ / (2 * S.error)) ^ (d₀ + ε))
    (hΓgrow : (2 : ℝ) ^ d ≤ χ * (2 : ℝ) ^ (d₀ + ε))
    (hband : ∀ i : ι₁ ⊕ ι₂, ∀ k : ℕ,
      S.law {p | S.lab₁ (S.src p) = Sum.elim S.lab₁ S.lab₂ i ∧
        ‖Sum.elim S.φ₁ S.φ₂ i (emb (S.point p)) - (S.value p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)} ≤
        ENNReal.ofReal (G (Sum.elim S.lab₁ S.lab₂ i) * ((2 : ℝ) ^ d) ^ k)) :
    S.law {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M₀ ≤ ‖S.φ₁ (S.src p) (emb y) - S.φ₂ (S.wit p) (emb y)‖} ≤
      ENNReal.ofReal (4 *
        (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
        (1 - χ) * ((r : ℝ) * ∑ i, θ (S.lab₁ i) + ∑ j, θ (S.lab₂ j))) := by
  letI := S.finite
  let C := S.cloned r hr hweights
  have hb (i : (ι₁ × Fin r) ⊕ ι₂) (k : ℕ) :
      C.Pm {p | C.lab (C.src p) = C.lab i ∧
        ‖C.φ i (emb (C.x p)) - (C.w p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)} ≤
          ENNReal.ofReal (G (C.lab i) * ((2 : ℝ) ^ d) ^ k) := by
    rcases i with ⟨i, j⟩ | i
    · change uniformCopies S.law r (Prod.fst ⁻¹'
        {p : Ω | S.lab₁ (S.src p) = S.lab₁ i ∧
          ‖S.φ₁ i (emb (S.point p)) - (S.value p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)}) ≤ _
      rw [uniformCopies_preimage S.law hr]
      exact hband (Sum.inl i) k
    · change uniformCopies S.law r (Prod.fst ⁻¹'
        {p : Ω | S.lab₁ (S.src p) = S.lab₂ i ∧
          ‖S.φ₂ i (emb (S.point p)) - (S.value p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)}) ≤ _
      rw [uniformCopies_preimage S.law hr]
      exact hband (Sum.inr i) k
  have h := discrepancy_mass_le_from_base J C M₀ θ G hmb hR₀ hε hεε₀ hM₀ hχ hχ1
    hθ hG hR hC hρ hρgrow hΓ hΓgrow hb
  change uniformCopies S.law r (Prod.fst ⁻¹'
    {p : Ω | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M₀ ≤ ‖S.φ₁ (S.src p) (emb y) - S.φ₂ (S.wit p) (emb y)‖}) ≤ ENNReal.ofReal
    (4 * (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
      (1 - χ) * ∑ i : (ι₁ × Fin r) ⊕ ι₂,
        θ (Sum.elim (fun p => S.lab₁ p.1) S.lab₂ i)) at h
  rw [uniformCopies_preimage S.law hr, uniformCopies_reference_sum] at h
  exact h

end TwoWeightComparison

end

end Submission.Obl.k4_general_wide_layer_offset_comparison
