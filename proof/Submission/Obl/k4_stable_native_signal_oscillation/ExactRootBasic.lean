import Mathlib
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials

/-!
# Exact-root signal partition: basic tools

The base map, the hidden-coordinate expansion of quadratics, base-density volume bounds,
polynomial control from the law (from the fixed-degree polynomial control statement),
the thin-slab mass bound, and the two-sign group packaging.
-/

namespace Submission.Obl.k4_stable_native_signal_oscillation

open MvPolynomial MeasureTheory Set Metric
open Submission.Obl.k4_quadratic_atlas_normalization

/-- The base point of a native point (first three coordinates). -/
noncomputable def erBase (p : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![p 0, p 1, p 2]

lemma measurable_erBase : Measurable erBase := by
  apply Continuous.measurable
  unfold erBase
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

lemma continuous_erBase : Continuous erBase := by
  unfold erBase
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

lemma er_snoc_base (p : EuclideanSpace ℝ (Fin 4)) :
    (Fin.snoc (fun j : Fin 3 => erBase p j) (p 3) : Fin 4 → ℝ) = fun i => p i := by
  funext i
  fin_cases i <;> rfl

/-- The hidden-coordinate expansion of a quadratic at a native point. -/
lemma er_eval_expand (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (p : EuclideanSpace ℝ (Fin 4)) :
    eval (fun i => p i) P = eval (fun j => erBase p j) (restrictBase P) +
      eval (fun j => erBase p j) (restrictBase (pderiv 3 P)) * p 3 +
      curvature P 3 * p 3 ^ 2 / 2 := by
  have h := eval_snoc_quadratic P hP (fun j => erBase p j) (p 3)
  rw [er_snoc_base] at h
  exact h

/-- The hidden derivative of a quadratic is affine in the hidden coordinate. -/
lemma er_deriv_expand (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (p : EuclideanSpace ℝ (Fin 4)) :
    eval (fun i => p i) (pderiv 3 P) =
      eval (fun j => erBase p j) (restrictBase (pderiv 3 P)) + curvature P 3 * p 3 := by
  have h := quadratic_coordinate_derivative P hP
    (Fin.snoc (fun j : Fin 3 => erBase p j) 0 : Fin 4 → ℝ) 3 (p 3)
  have h3 : (Fin.snoc (fun j : Fin 3 => erBase p j) 0 : Fin 4 → ℝ) 3 = 0 := rfl
  rw [h3, zero_add] at h
  have hu : Function.update (Fin.snoc (fun j : Fin 3 => erBase p j) 0 : Fin 4 → ℝ) 3 (p 3) =
      fun i => p i := by
    rw [← er_snoc_base p]
    exact update_snoc_hidden _ _ _
  rw [hu] at h
  rw [h, ← eval_restrictBase]

lemma er_totalDegree_restrict_deriv (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) :
    (restrictBase (pderiv 3 P)).totalDegree ≤ 1 :=
  (totalDegree_restrictBase _).trans
    ((Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le P 3).trans (by omega))

lemma er_totalDegree_restrict (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) :
    (restrictBase P).totalDegree ≤ 2 :=
  (totalDegree_restrictBase _).trans hP

/-- Base density: a measurable base set carrying almost every base point has volume at
least `K⁻¹`. -/
lemma er_witness_volume (μ : Measure (EuclideanSpace ℝ (Fin 4))) [IsProbabilityMeasure μ]
    {K : ℝ} (hK : 0 < K) (hd : Measure.map erBase μ ≤ ENNReal.ofReal K • volume)
    (T : Set (EuclideanSpace ℝ (Fin 3))) (hT : MeasurableSet T)
    (hfull : ∀ᵐ p ∂μ, erBase p ∈ T) :
    ENNReal.ofReal K⁻¹ ≤ volume T := by
  have hprob : (Measure.map erBase μ) T = 1 := by
    rw [Measure.map_apply measurable_erBase hT]
    exact (mem_ae_iff_prob_eq_one (hT.preimage measurable_erBase)).mp hfull
  rw [ENNReal.ofReal_inv_of_pos hK]
  apply (ENNReal.inv_le_iff_le_mul
    (fun _ => (ENNReal.ofReal_pos.mpr hK).ne') (fun h => (ENNReal.ofReal_ne_top h).elim)).mpr
  calc
    1 = (Measure.map erBase μ) T := hprob.symm
    _ ≤ (ENNReal.ofReal K • volume) T := hd T
    _ = ENNReal.ofReal K * volume T := Measure.smul_apply _ _ _

/-- Base density bounds the mass above a base set. -/
lemma er_preimage_mass (μ : Measure (EuclideanSpace ℝ (Fin 4)))
    {K : ℝ} (hd : Measure.map erBase μ ≤ ENNReal.ofReal K • volume)
    (T : Set (EuclideanSpace ℝ (Fin 3))) (hT : MeasurableSet T) :
    μ (erBase ⁻¹' T) ≤ ENNReal.ofReal K * volume T := by
  rw [← Measure.map_apply measurable_erBase hT]
  exact (hd T).trans_eq (Measure.smul_apply _ _ _)

/-- The fixed-degree polynomial control statement (proved on branch x0586 as
`exists_polynomial_control`). -/
def PolyControlStatement : Prop :=
  ∀ D m : ℕ, ∃ N : ℕ, 1 ≤ N ∧ ∀ K : ℝ, 2 ≤ K →
    ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
    ∀ (E : Set (EuclideanSpace ℝ (Fin 3))) (V : ℝ), 0 ≤ V →
    E ⊆ closedBall 0 K → ENNReal.ofReal ((K ^ m)⁻¹) ≤ volume E →
    (∀ x ∈ E, |eval (fun i => x i) P| ≤ V) →
    (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → |eval (fun i => x i) P| ≤ K ^ N * V) ∧
    ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → ‖y‖ ≤ 3 * K →
      |eval (fun i => x i) P - eval (fun i => y i) P| ≤ K ^ N * V * ‖x - y‖

lemma er_continuous_eval3 (f : MvPolynomial (Fin 3) ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin 3) => eval (fun i => x i) f) :=
  (MvPolynomial.continuous_eval f).comp (by fun_prop)

/-- Polynomial control from the law: a base polynomial bounded at the base of almost every
point is bounded and Lipschitz on the enlarged ball. -/
lemma er_control (hPC : PolyControlStatement) (D : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ K : ℝ, 2 ≤ K →
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 4))) [IsProbabilityMeasure μ],
      Measure.map erBase μ ≤ ENNReal.ofReal K • volume →
      ∀ (G : Set (EuclideanSpace ℝ (Fin 4))), (∀ᵐ p ∂μ, p ∈ G) →
      (∀ p ∈ G, ‖erBase p‖ ≤ K) →
      ∀ (f : MvPolynomial (Fin 3) ℝ), f.totalDegree ≤ D → ∀ V : ℝ, 0 ≤ V →
      (∀ p ∈ G, |eval (fun i => erBase p i) f| ≤ V) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → |eval (fun i => x i) f| ≤ K ^ N * V) ∧
      ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → ‖y‖ ≤ 3 * K →
        |eval (fun i => x i) f - eval (fun i => y i) f| ≤ K ^ N * V * ‖x - y‖ := by
  obtain ⟨N, hN, hctl⟩ := hPC D 1
  refine ⟨N, hN, ?_⟩
  intro K hK μ _ hd G hG hGball f hf V hV hfG
  have hK0 : 0 < K := by linarith
  let T : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | ‖x‖ ≤ K ∧ |eval (fun i => x i) f| ≤ V}
  have hTm : MeasurableSet T :=
    (measurableSet_le measurable_id.norm measurable_const).inter
      (measurableSet_le (er_continuous_eval3 f).abs.measurable measurable_const)
  have hfull : ∀ᵐ p ∂μ, erBase p ∈ T := by
    filter_upwards [hG] with p hp
    exact ⟨hGball p hp, hfG p hp⟩
  have hvol := er_witness_volume μ hK0 hd T hTm hfull
  have hsub : T ⊆ closedBall 0 K := fun x hx => by
    simpa [mem_closedBall, dist_zero_right] using hx.1
  exact hctl K hK f hf T V hV hsub (by simpa only [pow_one] using hvol) (fun x hx => hx.2)


/-- A thin slab of a base polynomial, measured relative to its maximum on the ball, carries
little mass. -/
lemma er_slab (hPC : PolyControlStatement) (D A : ℕ) :
    ∃ c : ℕ, ∀ K : ℝ, 2 ≤ K →
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 4))),
      Measure.map erBase μ ≤ ENNReal.ofReal K • volume →
      ∀ (B : MvPolynomial (Fin 3) ℝ), B.totalDegree ≤ D →
      ∀ (x₀ : EuclideanSpace ℝ (Fin 3)), ‖x₀‖ ≤ K →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ K →
        |eval (fun i => x i) B| ≤ |eval (fun i => x₀ i) B|) →
      0 < |eval (fun i => x₀ i) B| →
      μ (erBase ⁻¹' {x | ‖x‖ ≤ K ∧
          |eval (fun i => x i) B| ≤ |eval (fun i => x₀ i) B| / K ^ c}) ≤
        ENNReal.ofReal ((K ^ A)⁻¹) := by
  obtain ⟨N, hN, hctl⟩ := hPC D (A + 1)
  refine ⟨N + 1, ?_⟩
  intro K hK μ hd B hB x₀ hx₀ hmax hpos
  have hK0 : 0 < K := by linarith
  have hK1 : 1 < K := by linarith
  set L := |eval (fun i => x₀ i) B| with hL
  set Y : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | ‖x‖ ≤ K ∧ |eval (fun i => x i) B| ≤ L / K ^ (N + 1)} with hY
  have hYm : MeasurableSet Y :=
    (measurableSet_le measurable_id.norm measurable_const).inter
      (measurableSet_le (er_continuous_eval3 B).abs.measurable measurable_const)
  have hvol : volume Y < ENNReal.ofReal ((K ^ (A + 1))⁻¹) := by
    by_contra h0
    have h := le_of_not_gt h0
    have hsub : Y ⊆ closedBall 0 K := fun x hx => by
      simpa [mem_closedBall, dist_zero_right] using hx.1
    have hb := (hctl K hK B hB Y (L / K ^ (N + 1)) (by positivity) hsub h
      (fun x hx => hx.2)).1 x₀ (by linarith)
    have heq : K ^ N * (L / K ^ (N + 1)) = L / K := by
      rw [pow_succ]
      field_simp
    rw [heq] at hb
    have : L / K < L := div_lt_self hpos hK1
    linarith
  calc μ (erBase ⁻¹' Y) ≤ ENNReal.ofReal K * volume Y := er_preimage_mass μ hd Y hYm
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((K ^ (A + 1))⁻¹) := by gcongr
    _ = ENNReal.ofReal ((K ^ A)⁻¹) := by
      rw [← ENNReal.ofReal_mul hK0.le]
      congr 1
      rw [pow_succ]
      field_simp

/-- Two sign groups, trimmed by a threshold on an auxiliary observable. -/
lemma er_package (μ : Measure (EuclideanSpace ℝ (Fin 4)))
    (G : Set (EuclideanSpace ℝ (Fin 4))) (hGm : MeasurableSet G) (hG : ∀ᵐ p ∂μ, p ∈ G)
    (u : EuclideanSpace ℝ (Fin 4) → ℝ) (hu : Measurable u) (hu0 : ∀ p ∈ G, u p ≠ 0)
    (g : EuclideanSpace ℝ (Fin 4) → ℝ) (hg : Measurable g) (b : ℝ)
    (Φ : EuclideanSpace ℝ (Fin 4) → ℝ) (L : ℝ) (ε : ENNReal)
    (hmass : μ (G ∩ {p | |g p| ≤ b}) ≤ ε)
    (hlip : ∀ p ∈ G, ∀ q ∈ G, b < |g p| → b < |g q| → 0 < u p * u q →
      |Φ p - Φ q| ≤ L * ‖erBase p - erBase q‖) :
    ∃ E : Fin 2 → Set (EuclideanSpace ℝ (Fin 4)),
      (∀ i, MeasurableSet (E i)) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
      μ (⋃ i, E i)ᶜ ≤ ε ∧
      ∀ i p, p ∈ E i → ∀ q, q ∈ E i → |Φ p - Φ q| ≤ L * ‖erBase p - erBase q‖ := by
  let E : Fin 2 → Set (EuclideanSpace ℝ (Fin 4)) :=
    ![G ∩ {p | 0 < u p} ∩ {p | b < |g p|}, G ∩ {p | u p < 0} ∩ {p | b < |g p|}]
  have hgm : MeasurableSet {p | b < |g p|} := measurableSet_lt measurable_const hg.abs
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (hGm.inter (measurableSet_lt measurable_const hu)).inter hgm
    · exact (hGm.inter (measurableSet_lt hu measurable_const)).inter hgm
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Set.disjoint_left.mpr fun p hp hq => by
        have h1 : 0 < u p := hp.1.2
        have h2 : u p < 0 := hq.1.2
        linarith
    · exact Set.disjoint_left.mpr fun p hp hq => by
        have h1 : u p < 0 := hp.1.2
        have h2 : 0 < u p := hq.1.2
        linarith
    · exact absurd rfl hij
  · have hsub : (⋃ i, E i)ᶜ ⊆ Gᶜ ∪ (G ∩ {p | |g p| ≤ b}) := by
      intro p hp
      by_cases hpG : p ∈ G
      · right
        refine ⟨hpG, ?_⟩
        by_contra hgb0
        have hgb : b < |g p| := lt_of_not_ge hgb0
        apply hp
        rcases lt_or_gt_of_ne (hu0 p hpG) with hneg | hposu
        · exact Set.mem_iUnion.mpr ⟨1, ⟨⟨hpG, hneg⟩, hgb⟩⟩
        · exact Set.mem_iUnion.mpr ⟨0, ⟨⟨hpG, hposu⟩, hgb⟩⟩
      · left; exact hpG
    have hGc : μ Gᶜ = 0 := ae_iff.mp hG
    calc μ (⋃ i, E i)ᶜ ≤ μ (Gᶜ ∪ (G ∩ {p | |g p| ≤ b})) := measure_mono hsub
      _ ≤ μ Gᶜ + μ (G ∩ {p | |g p| ≤ b}) := measure_union_le _ _
      _ ≤ 0 + ε := by rw [hGc]; exact add_le_add le_rfl hmass
      _ = ε := zero_add _
  · intro i p hp q hq
    fin_cases i
    · exact hlip p hp.1.1 q hq.1.1 hp.2 hq.2 (mul_pos hp.1.2 hq.1.2)
    · exact hlip p hp.1.1 q hq.1.1 hp.2 hq.2 (mul_pos_of_neg_of_neg hp.1.2 hq.1.2)

end Submission.Obl.k4_stable_native_signal_oscillation
