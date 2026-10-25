-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/PaddedBinChoice.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.FiniteBinChoice

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory
open scoped ENNReal

/-- Empty lists at unused observations can be filled with a default.
For a list bound at least one, this has no additional mass cost. -/
theorem exists_original_bin_choice_allow_empty {Ω I B : Type*}
    [MeasurableSpace Ω] [Fintype I] [Nonempty B]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E)
    (obs : Ω → I) (hobs : ∀ i, MeasurableSet {x | obs x = i})
    (label : Ω → B) (hlabel : ∀ b, MeasurableSet {x | label x = b})
    (L : I → Finset B) (hknown : ∀ x ∈ E, label x ∈ L (obs x))
    (K : ℝ≥0∞) (hK : 1 ≤ K) (hcard : ∀ i, ((L i).card : ℝ≥0∞) ≤ K) :
    ∃ choice : I → B,
      (∀ i, (L i).Nonempty → choice i ∈ L i) ∧
      MeasurableSet {x | x ∈ E ∧ label x = choice (obs x)} ∧
      μ E ≤ K * μ {x | x ∈ E ∧ label x = choice (obs x)} := by
  classical
  let b₀ : B := Classical.choice inferInstance
  let pad : I → Finset B := fun i => if (L i).Nonempty then L i else {b₀}
  have hpad (i : I) : (pad i).Nonempty := by
    by_cases hi : (L i).Nonempty
    · simpa only [pad, ite_eq_left hi] using hi
    · simp only [pad, ite_eq_right hi, Finset.singleton_nonempty]
  have hpadcard (i : I) : ((pad i).card : ℝ≥0∞) ≤ K := by
    by_cases hi : (L i).Nonempty
    · simpa only [pad, ite_eq_left hi] using hcard i
    · simpa only [pad, ite_eq_right hi, Finset.card_singleton, Nat.cast_one] using hK
  have hpadknown (x : Ω) (hx : x ∈ E) : label x ∈ pad (obs x) := by
    have hmem := hknown x hx
    have hne : (L (obs x)).Nonempty := ⟨label x,hmem⟩
    simpa only [pad, ite_eq_left hne] using hmem
  obtain ⟨choice,hchoice,hm,hmass⟩ := exists_original_observation_bin_choice μ E hE obs hobs
    label hlabel pad hpad hpadknown K hpadcard
  refine ⟨choice,?_,hm,hmass⟩
  intro i hi
  simpa only [pad, ite_eq_left hi] using hchoice i

/-- Three heterogeneous lists (a cell value and two fiber polynomials,
for example) are fixed on the same original law with a cubic loss. -/
theorem exists_three_original_bin_choices {Ω I₀ I₁ I₂ B₀ B₁ B₂ : Type*}
    [MeasurableSpace Ω] [Fintype I₀] [Fintype I₁] [Fintype I₂]
    [Nonempty B₀] [Nonempty B₁] [Nonempty B₂]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E)
    (o₀ : Ω → I₀) (o₁ : Ω → I₁) (o₂ : Ω → I₂)
    (ho₀ : ∀ i, MeasurableSet {x | o₀ x=i})
    (ho₁ : ∀ i, MeasurableSet {x | o₁ x=i})
    (ho₂ : ∀ i, MeasurableSet {x | o₂ x=i})
    (b₀ : Ω → B₀) (b₁ : Ω → B₁) (b₂ : Ω → B₂)
    (hb₀ : ∀ b, MeasurableSet {x | b₀ x=b})
    (hb₁ : ∀ b, MeasurableSet {x | b₁ x=b})
    (hb₂ : ∀ b, MeasurableSet {x | b₂ x=b})
    (L₀ : I₀ → Finset B₀) (L₁ : I₁ → Finset B₁) (L₂ : I₂ → Finset B₂)
    (hk₀ : ∀ x ∈ E, b₀ x ∈ L₀ (o₀ x))
    (hk₁ : ∀ x ∈ E, b₁ x ∈ L₁ (o₁ x))
    (hk₂ : ∀ x ∈ E, b₂ x ∈ L₂ (o₂ x))
    (K : ℝ≥0∞) (hK : 1 ≤ K)
    (hc₀ : ∀ i, ((L₀ i).card : ℝ≥0∞) ≤ K)
    (hc₁ : ∀ i, ((L₁ i).card : ℝ≥0∞) ≤ K)
    (hc₂ : ∀ i, ((L₂ i).card : ℝ≥0∞) ≤ K) :
    ∃ (c₀ : I₀ → B₀) (c₁ : I₁ → B₁) (c₂ : I₂ → B₂) (S : Set Ω),
      MeasurableSet S ∧ S ⊆ E ∧ μ E ≤ K^3 * μ S ∧
      ∀ x ∈ S, b₀ x=c₀ (o₀ x) ∧ b₁ x=c₁ (o₁ x) ∧ b₂ x=c₂ (o₂ x) := by
  obtain ⟨c₀,_,hm₀,hμ₀⟩ := exists_original_bin_choice_allow_empty μ E hE o₀ ho₀ b₀ hb₀ L₀ hk₀ K hK hc₀
  let E₀ := {x | x ∈ E ∧ b₀ x=c₀ (o₀ x)}
  obtain ⟨c₁,_,hm₁,hμ₁⟩ := exists_original_bin_choice_allow_empty μ E₀ hm₀ o₁ ho₁ b₁ hb₁ L₁
    (fun x hx => hk₁ x hx.1) K hK hc₁
  let E₁ := {x | x ∈ E₀ ∧ b₁ x=c₁ (o₁ x)}
  obtain ⟨c₂,_,hm₂,hμ₂⟩ := exists_original_bin_choice_allow_empty μ E₁ hm₁ o₂ ho₂ b₂ hb₂ L₂
    (fun x hx => hk₂ x hx.1.1) K hK hc₂
  let S := {x | x ∈ E₁ ∧ b₂ x=c₂ (o₂ x)}
  refine ⟨c₀,c₁,c₂,S,hm₂,(fun x hx => hx.1.1.1),?_,?_⟩
  · calc
      μ E ≤ K*μ E₀ := hμ₀
      _ ≤ K*(K*μ E₁) := mul_le_mul' le_rfl hμ₁
      _ ≤ K*(K*(K*μ S)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hμ₂)
      _ = _ := by ring
  · intro x hx
    exact ⟨hx.1.1.2,hx.1.2,hx.2⟩

/-- Numerical loss accounting for original unnormalized source floors. -/
theorem original_floor_after_bin_choices {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E S : Set Ω) (K m : ℝ)
    (hK : 0 < K) (hm : 0 ≤ m)
    (hlower : ENNReal.ofReal m ≤ μ E)
    (hloss : μ E ≤ (ENNReal.ofReal K)^3 * μ S) :
    ENNReal.ofReal (m/K^3) ≤ μ S := by
  have h := hlower.trans hloss
  have hr := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_ofReal hm, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hK.le] at hr
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ S)).mpr
  apply (div_le_iff₀ (pow_pos hK 3)).mpr
  simpa only [mul_comm] using hr

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
