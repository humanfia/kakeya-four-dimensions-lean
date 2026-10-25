-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Matching.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.Interface
import Submission.Obl.k4_algebraic_real_jet_comparison.RealGeometry

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Metric

abbrev Real3 := EuclideanSpace ℝ (Fin 3)
abbrev Complex3 := EuclideanSpace ℂ (Fin 3)

noncomputable abbrev emb : Real3 →ₗᵢ[ℝ] Complex3 :=
  Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3

/-- A bounded-degree family of real algebraic sheets, compared to one common graph. -/
def SheetFamily (D n : ℕ) (R M ε : ℝ) (f₀ : Real3 → ℂ)
    (f : Fin n → Complex3 → ℂ) (P : Fin n → MvPolynomial (Fin 4) ℂ) : Prop :=
  ∀ i, P i ≠ 0 ∧ (P i).totalDegree ≤ D ∧
    DifferentiableOn ℂ (f i) (ball 0 4) ∧
    (∀ z ∈ ball (0 : Complex3) 4,
      MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f i z)) (P i) = 0) ∧
    ∀ x : Real3, ‖x‖ ≤ 1 → (f i (emb x)).im = 0 ∧ ‖f i (emb x) - f₀ x‖ ≤ M * R ^ ε

/-- Pairs agreeing at their sampled base but separated somewhere in the comparison half-ball. -/
def badPairs {n₁ n₂ : ℕ} (f₁ : Fin n₁ → Complex3 → ℂ)
    (f₂ : Fin n₂ → Complex3 → ℂ) (R M ε : ℝ) :
    Set ((Fin n₁ × Fin n₂) × Real3) :=
  {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧
    ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ M * R ^ (-1 + ε) ∧
    ∃ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 ∧
      M * R ^ (-ε) ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖}

/-- The separated-pair event is measurable even though the sheet functions are only
assumed holomorphic on their comparison domain. -/
theorem measurableSet_badPairs {n₁ n₂ : ℕ}
    {f₁ : Fin n₁ → Complex3 → ℂ} {f₂ : Fin n₂ → Complex3 → ℂ}
    (hf₁ : ∀ i, DifferentiableOn ℂ (f₁ i) (ball 0 4))
    (hf₂ : ∀ i, DifferentiableOn ℂ (f₂ i) (ball 0 4)) (R M ε : ℝ) :
    MeasurableSet (badPairs f₁ f₂ R M ε) := by
  classical
  let B (i : Fin n₁) (j : Fin n₂) : Set Real3 :=
    {z | ‖z‖ ≤ (1 : ℝ) / 2 ∧
      ‖f₁ i (emb z) - f₂ j (emb z)‖ ≤ M * R ^ (-1 + ε) ∧
      ∃ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 ∧
        M * R ^ (-ε) ≤ ‖f₁ i (emb x) - f₂ j (emb x)‖}
  have hmaps : MapsTo emb (closedBall (0 : Real3) (1 / 2)) (ball 0 4) := by
    intro z hz
    rw [mem_ball_zero_iff, emb.norm_map]
    have hz' := mem_closedBall_zero_iff.mp hz
    linarith
  have hB (i : Fin n₁) (j : Fin n₂) : MeasurableSet (B i j) := by
    have hc₁ : ContinuousOn (fun z : Real3 => f₁ i (emb z)) (closedBall 0 (1 / 2)) :=
      (hf₁ i).continuousOn.comp emb.continuous.continuousOn hmaps
    have hc₂ : ContinuousOn (fun z : Real3 => f₂ j (emb z)) (closedBall 0 (1 / 2)) :=
      (hf₂ j).continuousOn.comp emb.continuous.continuousOn hmaps
    have hm : MeasurableSet {z : Real3 | ‖z‖ ≤ (1 : ℝ) / 2 ∧
        ‖f₁ i (emb z) - f₂ j (emb z)‖ ≤ M * R ^ (-1 + ε)} := by
      simpa only [mem_closedBall_zero_iff, Pi.sub_apply] using
        (isClosed_closedBall.isClosed_le (hc₁.sub hc₂).norm continuousOn_const).measurableSet
    by_cases hgap : ∃ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 ∧
      M * R ^ (-ε) ≤ ‖f₁ i (emb x) - f₂ j (emb x)‖
    · simpa only [B, hgap, and_true] using hm
    · simp only [B, hgap, and_false, ofPred_false, MeasurableSet.empty]
  have hU : MeasurableSet (⋃ i : Fin n₁, ⋃ j : Fin n₂,
      ({(i, j)} : Set (Fin n₁ × Fin n₂)) ×ˢ B i j) :=
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
      (measurableSet_singleton (i, j)).prod (hB i j)
  convert hU using 1
  ext p
  simp only [badPairs, mem_ofPred_eq, mem_iUnion, mem_prod, mem_singleton_iff]
  constructor
  · intro hp
    exact ⟨p.1.1, p.1.2, by simp, hp⟩
  · rintro ⟨i, j, hp, hB⟩
    simpa only [B, hp, mem_ofPred_eq] using hB

/-- Restricting to bad pairs turns the qualitative matching exclusion into a uniform
quantitative bound. Neither conditioning on a rare event nor renormalization is needed. -/
theorem graph_bad_mass (h : localGraph) (D : ℕ) (d₀ : ℝ)
    (hd₀ : 0 ≤ d₀) (hd₀1 : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ →
      ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → Complex3 → ℂ) (f₂ : Fin n₂ → Complex3 → ℂ)
        (P₁ : Fin n₁ → MvPolynomial (Fin 4) ℂ)
        (P₂ : Fin n₂ → MvPolynomial (Fin 4) ℂ) (f₀ : Real3 → ℂ)
        (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ)
        (μ : Measure ((Fin n₁ × Fin n₂) × Real3)),
      (n₁ : ℝ) ≤ R ^ (d₀ + ε) → (n₂ : ℝ) ≤ R ^ (d₀ + ε) →
      SheetFamily D n₁ R M ε f₀ f₁ P₁ → SheetFamily D n₂ R M ε f₀ f₂ P₂ →
      (∀ i, 0 ≤ π₁ i) → (∀ i, 0 ≤ π₂ i) → (∑ i, π₁ i) = 1 → (∑ i, π₂ i) = 1 →
      μ univ ≤ 1 →
      (∀ i (U : Set Real3), MeasurableSet U →
        μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₁ i) * volume U) →
      (∀ i (U : Set Real3), MeasurableSet U →
        μ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₂ i) * volume U) →
      μ (badPairs f₁ f₂ R M ε) < ENNReal.ofReal (R ^ (-ε)) := by
  obtain ⟨ε₀, hε₀, R₀, hR₀, hmatch⟩ := h D d₀ hd₀ hd₀1
  refine ⟨ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R M ε hR hM hε hεε₀ n₁ n₂ f₁ f₂ P₁ P₂ f₀ π₁ π₂ μ
    hn₁ hn₂ hf₁ hf₂ hπ₁ hπ₂ hπ₁sum hπ₂sum hμ hμ₁ hμ₂
  have hm := measurableSet_badPairs (fun i => (hf₁ i).2.2.1)
    (fun i => (hf₂ i).2.2.1) R M ε
  by_contra! hbad
  let ν := μ.restrict (badPairs f₁ f₂ R M ε)
  have hν : ν ≤ μ := Measure.restrict_le_self
  have hνmass : ENNReal.ofReal (R ^ (-ε)) ≤ ν univ := by
    simpa only [ν, Measure.restrict_apply_univ] using hbad
  have hν₁ i (U : Set Real3) (hU : MeasurableSet U) :=
    (Measure.le_iff'.mp hν _).trans (hμ₁ i U hU)
  have hν₂ i (U : Set Real3) (hU : MeasurableSet U) :=
    (Measure.le_iff'.mp hν _).trans (hμ₂ i U hU)
  have hex := hmatch R M ε hR hM hε hεε₀ n₁ n₂ f₁ f₂ P₁ P₂ f₀ π₁ π₂ ν
    hn₁ hn₂ hf₁ hf₂ hπ₁ hπ₂ hπ₁sum hπ₂sum hνmass
    ((Measure.le_iff'.mp hν _).trans hμ) hν₁ hν₂
  apply hex
  change (μ.restrict (badPairs f₁ f₂ R M ε)) (badPairs f₁ f₂ R M ε)ᶜ = 0
  rw [Measure.restrict_apply hm.compl, compl_inter_self, measure_empty]

end Submission.Obl.k4_clean_cover_graph_atlas
