/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/GML3Law.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation, session x0764, Match3/GML3Law.lean, commit2b232aca. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.GML3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The three-dimensional matching lemma on an incidence law

`gml3_of_law` restates `gml3` for an arbitrary finite measure `λ` on an event space `Ω` (for
instance incidences `(line, time)`), with measurable label maps `f₁ : Ω → ι₁`, `f₂ : Ω → ι₂` and a
measurable normalized base point `x : Ω → E3`: the pair law is the pushforward of `λ` under
`ω ↦ ((f₁ ω, f₂ ω), x ω)`.  All hypotheses and the conclusion are then statements about `λ`
itself: cube ceilings per label, closeness of the two predictors at the base point, jet counts,
and the conclusion bounds the `λ`-mass of events whose two labels' predictors differ by `≥ M*`
in coefficient norm.
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open MeasureTheory

/-- **GML3 on an incidence law.** -/
theorem gml3_of_law (hM : Matching) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (lam : Measure Ω) [IsFiniteMeasure lam]
      (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (f₁ : Ω → ι₁) (f₂ : Ω → ι₂) (x : Ω → E3)
      (c₁ : ι₁ → Fin 10 → ℝ) (c₂ : ι₂ → Fin 10 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
      (δ Mst A B w : ℝ),
      Measurable f₁ → Measurable f₂ → Measurable x →
      0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
      0 < w → w ≤ 1 / 8 → 42 * B * w ≤ δ →
      (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
      (∀ i k, |c₁ i k| ≤ B) → (∀ j k, |c₂ j k| ≤ B) →
      (∀ i (y : E3), lam {ω | f₁ ω = i ∧ y - x ω ∈ cube w} ≤
        ENNReal.ofReal (A * T₁ i * w ^ 3)) →
      (∀ j (y : E3), lam {ω | f₂ ω = j ∧ y - x ω ∈ cube w} ≤
        ENNReal.ofReal (A * T₂ j * w ^ 3)) →
      (∀ (r : Fin 10 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun i => ∀ k, |c₁ i k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d) →
      (∀ (r : Fin 10 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun j => ∀ k, |c₂ j k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d) →
      (∀ᵐ ω ∂lam, ‖x ω‖ ≤ 1 / 4 ∧ |q3E (c₁ (f₁ ω)) (x ω) - q3E (c₂ (f₂ ω)) (x ω)| ≤ δ) →
      lam {ω | Mst ≤ cnorm3 (c₁ (f₁ ω) - c₂ (f₂ ω))} ≤
        ENNReal.ofReal (A * (Mst / δ) ^ (-η) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
  obtain ⟨η, hη, R₀, hR₀, H⟩ := gml3 hM hd0 hd1
  refine ⟨η, hη, R₀, hR₀, ?_⟩
  intro Ω _ lam _ ι₁ ι₂ _ _ _ _ _ _ f₁ f₂ x c₁ c₂ T₁ T₂ δ Mst A B w hf₁ hf₂ hx hδ hMst hA1 hA
    hw hw8 hwδ hT₁ hT₂ hB₁ hB₂ hi₁ hi₂ hc₁ hc₂ hae
  set Φ : Ω → (ι₁ × ι₂) × E3 := fun ω => ((f₁ ω, f₂ ω), x ω) with hΦ
  have hΦm : Measurable Φ := (hf₁.prodMk hf₂).prodMk hx
  set P : Measure ((ι₁ × ι₂) × E3) := lam.map Φ with hP
  have : IsFiniteMeasure P := Measure.isFiniteMeasure_map lam Φ
  have hPapp : ∀ S : Set ((ι₁ × ι₂) × E3), MeasurableSet S → P S = lam (Φ ⁻¹' S) :=
    fun S hS => Measure.map_apply hΦm hS
  have hmeasCube : ∀ (y : E3), MeasurableSet {z : E3 | y - z ∈ cube w} :=
    fun y => (measurable_const.sub measurable_id) (measurableSet_cube w)
  have hi₁' : ∀ i (y : E3), P {p | p.1.1 = i ∧ y - p.2 ∈ cube w} ≤
      ENNReal.ofReal (A * T₁ i * w ^ 3) := by
    intro i y
    have hS : MeasurableSet {p : (ι₁ × ι₂) × E3 | p.1.1 = i ∧ y - p.2 ∈ cube w} :=
      ((measurable_fst.comp measurable_fst) (measurableSet_singleton i)).inter
        (measurable_snd (hmeasCube y))
    rw [hPapp _ hS]
    exact hi₁ i y
  have hi₂' : ∀ j (y : E3), P {p | p.1.2 = j ∧ y - p.2 ∈ cube w} ≤
      ENNReal.ofReal (A * T₂ j * w ^ 3) := by
    intro j y
    have hS : MeasurableSet {p : (ι₁ × ι₂) × E3 | p.1.2 = j ∧ y - p.2 ∈ cube w} :=
      ((measurable_snd.comp measurable_fst) (measurableSet_singleton j)).inter
        (measurable_snd (hmeasCube y))
    rw [hPapp _ hS]
    exact hi₂ j y
  have hae' : ∀ᵐ p ∂P, ‖p.2‖ ≤ 1 / 4 ∧ |q3E (c₁ p.1.1) p.2 - q3E (c₂ p.1.2) p.2| ≤ δ := by
    have hmeasS : MeasurableSet {p : (ι₁ × ι₂) × E3 | ‖p.2‖ ≤ 1 / 4 ∧
        |q3E (c₁ p.1.1) p.2 - q3E (c₂ p.1.2) p.2| ≤ δ} := by
      have hf : Measurable (fun p : (ι₁ × ι₂) × E3 =>
          |q3E (c₁ p.1.1) p.2 - q3E (c₂ p.1.2) p.2|) := by
        apply measurable_from_prod_countable_right
        intro z
        simp only [q3E, q3]
        fun_prop
      exact (measurableSet_le measurable_snd.norm measurable_const).inter
        (measurableSet_le hf measurable_const)
    rw [hP, ae_map_iff hΦm.aemeasurable hmeasS]
    exact hae
  have hres := H ι₁ ι₂ c₁ c₂ T₁ T₂ P δ Mst A B w hδ hMst hA1 hA hw hw8 hwδ hT₁ hT₂ hB₁ hB₂
    hi₁' hi₂' hc₁ hc₂ hae'
  have hmeasF : MeasurableSet {p : (ι₁ × ι₂) × E3 | Mst ≤ cnorm3 (c₁ p.1.1 - c₂ p.1.2)} :=
    measurable_fst (t := {q : ι₁ × ι₂ | Mst ≤ cnorm3 (c₁ q.1 - c₂ q.2)})
      (Set.toFinite _).measurableSet
  rw [hPapp _ hmeasF] at hres
  exact hres

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
