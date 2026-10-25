import Submission.Lib.K4WeightedCellEnergy
import Submission.Lib.K4HorizontalCoercivity.VelocityWitnesses

namespace Submission.Obl.k4_contact_time_rate_rigidity

open MeasureTheory Set
open scoped ENNReal

/-- An interval of one mesh radius meets at most three velocity bins. -/
theorem interval_mass_of_floor_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (v : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (β : ℝ≥0∞) (hcap : ∀ a : ℤ, μ {p | p ∈ E ∧ ⌊v p / δ⌋ = a} ≤ β)
    (w : ℝ) : μ (E ∩ {p | |v p - w| ≤ δ}) ≤ 3 * β := by
  let a := ⌊w / δ⌋
  have hsub : E ∩ {p | |v p - w| ≤ δ} ⊆
      {p | p ∈ E ∧ ⌊v p / δ⌋ = a - 1} ∪
      {p | p ∈ E ∧ ⌊v p / δ⌋ = a} ∪
      {p | p ∈ E ∧ ⌊v p / δ⌋ = a + 1} := by
    intro p hp
    have hh := Submission.Lib.K4WeightedCellEnergy.floor_neighbor_of_dist_le hδ hp.2
    change ⌊v p / δ⌋ ≤ a + 1 ∧ a ≤ ⌊v p / δ⌋ + 1 at hh
    have hi : ⌊v p / δ⌋ = a - 1 ∨ ⌊v p / δ⌋ = a ∨ ⌊v p / δ⌋ = a + 1 := by omega
    rcases hi with h | h | h
    · exact Or.inl (Or.inl ⟨hp.1, h⟩)
    · exact Or.inl (Or.inr ⟨hp.1, h⟩)
    · exact Or.inr ⟨hp.1, h⟩
  calc
    _ ≤ μ (_ ∪ _ ∪ _) := measure_mono hsub
    _ ≤ (μ _ + μ _) + μ _ := (measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (β + β) + β := add_le_add (add_le_add (hcap _) (hcap _)) (hcap _)
    _ = _ := by ring

/-- The original bin ceilings give actual separated witnesses outside a null set. -/
theorem separated_contact_witnesses {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E G : Set Ω) (v : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (β : ℝ≥0∞) (hcap : ∀ a : ℤ, μ {p | p ∈ E ∧ ⌊v p / δ⌋ = a} ≤ β)
    (hsmall : 6 * β < μ E) (hG : ∀ᵐ p ∂μ, p ∈ G) :
    ∃ p₀ p₁ : Ω, (p₀ ∈ E ∧ p₀ ∈ G) ∧ (p₁ ∈ E ∧ p₁ ∈ G) ∧
      δ < |v p₀ - v p₁| := by
  have hmass : 3 * β + 3 * β < μ (E ∩ G) := by
    rw [measure_inter_conull (ae_iff.mp hG)]
    convert hsmall using 1 <;> ring
  have hthin (w : ℝ) : μ ((E ∩ G) ∩ {p | |v p - w| ≤ δ}) ≤ 3 * β := by
    have hs : (E ∩ G) ∩ {p | |v p - w| ≤ δ} ⊆ E ∩ {p | |v p - w| ≤ δ} :=
      fun _ hp => ⟨hp.1.1, hp.2⟩
    exact (measure_mono hs).trans (interval_mass_of_floor_cap μ E v hδ β hcap w)
  obtain ⟨p₀, hp₀, p₁, hp₁, _, _, hsep, _, _⟩ :=
    Submission.Lib.K4HorizontalCoercivity.exists_three_velocity_witnesses
      μ (E ∩ G) v δ (3 * β) hthin hmass
  exact ⟨p₀, p₁, hp₀, hp₁, hsep⟩

/-- A label's lower mass and original palette numerator give separated witnesses. -/
theorem label_witnesses {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E G : Set Ω) (v : Ω → ℝ)
    {K q δ η : ℝ} (hK : 1 ≤ K) (hq : 0 < q) (hδ : 0 < δ) (hη : 0 ≤ η)
    (w : ℝ≥0∞) (hw₀ : w ≠ 0) (hwtop : w ≠ ⊤)
    (hmass : ENNReal.ofReal (q / K) * w ≤ μ E)
    (hcap : ∀ a : ℤ, μ {p | p ∈ E ∧ ⌊v p / δ⌋ = a} ≤
      ENNReal.ofReal (K * q) * w * ENNReal.ofReal (K * η))
    (hsmall : 6 * K ^ 3 * η < 1) (hG : ∀ᵐ p ∂μ, p ∈ G) :
    ∃ p₀ p₁ : Ω, (p₀ ∈ E ∧ p₀ ∈ G) ∧ (p₁ ∈ E ∧ p₁ ∈ G) ∧
      δ < |v p₀ - v p₁| := by
  have hK₀ : 0 < K := by linarith
  have hreal : 6 * (K * q) * (K * η) < q / K := by
    apply (lt_div_iff₀ hK₀).mpr
    calc
      _ = (6 * K ^ 3 * η) * q := by ring
      _ < 1 * q := mul_lt_mul_of_pos_right hsmall hq
      _ = q := one_mul _
  apply separated_contact_witnesses μ E G v hδ
    (ENNReal.ofReal (K * q) * w * ENNReal.ofReal (K * η)) hcap _ hG
  calc
    _ = ENNReal.ofReal (6 * (K * q) * (K * η)) * w := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 6 * (K * q)),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num
      ring
    _ < ENNReal.ofReal (q / K) * w :=
      ENNReal.mul_lt_mul_left hw₀ hwtop
        ((ENNReal.ofReal_lt_ofReal_iff (div_pos hq hK₀)).mpr hreal)
    _ ≤ μ E := hmass

end Submission.Obl.k4_contact_time_rate_rigidity
