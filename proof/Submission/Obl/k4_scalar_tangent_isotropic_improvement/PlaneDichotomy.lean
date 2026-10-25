import Mathlib

set_option linter.unusedVariables false

/-!
# The plane dichotomy for lifted directions in `ℝ³`

At a fine physical state of the paper's velocity graph (`a05:velocity-graph`, version 1, lifted
directions `(1, V, X')/‖·‖ ∈ ℝ³`), either no plane through the origin captures most directions,
and then three independent draws span with determinant `≥ ε²` with probability `≥ c²`
(`triple_det_lower`: this is the bad-cell hypothesis of `bad_mass_le`), or some plane captures
them; with two captured velocities `δ` apart the plane is a bounded graph
(`normal_hidden_lower`) and every captured lifted velocity lies within `ε / |n₂|` of
`X' = G₀ + G₁ V` (`graph_residual_of_normal`). Also: the cross product on `ℝ³` as a Euclidean space
(`cross3`, `inner_cross3`, `norm_cross3_sq`) and unit normals (`exists_unit_orth`).
-/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Cross product on `ℝ³` as a Euclidean space. -/
def cross3 (a b : E3) : E3 := WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))

lemma inner_eq_dot (a b : E3) : inner ℝ a b = WithLp.ofLp a ⬝ᵥ WithLp.ofLp b := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

lemma inner_cross3 (a b c : E3) :
    inner ℝ (cross3 a b) c = Matrix.det (Matrix.of fun i k : Fin 3 => (![a, b, c] i) k) := by
  rw [inner_eq_dot, cross3]
  simp only [WithLp.ofLp_toLp]
  rw [dotProduct_comm, triple_product_permutation, triple_product_eq_det]
  congr 1
  ext i k
  fin_cases i <;> rfl

lemma norm_cross3_sq (a b : E3) : ‖cross3 a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - (inner ℝ a b) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_eq_dot, inner_eq_dot, inner_eq_dot, inner_eq_dot, cross3]
  simp only [WithLp.ofLp_toLp]
  rw [cross_dot_cross, dotProduct_comm (WithLp.ofLp b) (WithLp.ofLp a)]
  ring

/-- A unit vector orthogonal to a given vector of `ℝ³`. -/
lemma exists_unit_orth (u : E3) : ∃ ν : E3, ‖ν‖ = 1 ∧ inner ℝ ν u = 0 := by
  by_cases hu : u = 0
  · refine ⟨EuclideanSpace.single 0 1, by simp, by simp [hu]⟩
  · haveI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
    have hdim : Module.finrank ℝ (ℝ ∙ u)ᗮ = 2 := Submodule.finrank_orthogonal_span_singleton hu
    have hne : (ℝ ∙ u)ᗮ ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hdim; norm_num at hdim
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨‖w‖⁻¹ • w, norm_smul_inv_norm hw0, ?_⟩
    rw [real_inner_smul_left, Submodule.mem_orthogonal_singleton_iff_inner_left.mp hw, mul_zero]

/-- For unit `u₁` and a unit `ν ⊥ u₁`, `|⟪ν, u₂⟫| ≤ ‖u₁ × u₂‖`. -/
lemma abs_inner_le_norm_cross3 {u₁ ν : E3} (hu₁ : ‖u₁‖ = 1) (hν : ‖ν‖ = 1)
    (horth : inner ℝ ν u₁ = 0) (u₂ : E3) : |inner ℝ ν u₂| ≤ ‖cross3 u₁ u₂‖ := by
  set w : E3 := u₂ - (inner ℝ u₁ u₂) • u₁ with hw
  have hνw : inner ℝ ν u₂ = inner ℝ ν w := by
    rw [hw, inner_sub_right, real_inner_smul_right, horth, mul_zero, sub_zero]
  have hw2 : ‖w‖ ^ 2 = ‖cross3 u₁ u₂‖ ^ 2 := by
    rw [norm_cross3_sq, hu₁, hw, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu₁,
      Real.norm_eq_abs, real_inner_comm u₁ u₂]
    simp only [mul_one, one_pow, sq_abs]
    ring
  have hwn : ‖w‖ = ‖cross3 u₁ u₂‖ := by
    rw [← Real.sqrt_sq (norm_nonneg w), hw2, Real.sqrt_sq (norm_nonneg _)]
  rw [hνw, ← hwn]
  calc |inner ℝ ν w| ≤ ‖ν‖ * ‖w‖ := abs_real_inner_le_norm ν w
    _ = ‖w‖ := by rw [hν, one_mul]

/-- Complement lower bound: if `P(Aᶜ) ≤ (1 - c) m` then `c m ≤ P(A)`. -/
lemma ofReal_mul_le_of_compl {β : Type*} [MeasurableSpace β] (P : Measure β) [IsFiniteMeasure P]
    {A : Set β} (hA : MeasurableSet A) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (h : P Aᶜ ≤ ENNReal.ofReal (1 - c) * P univ) : ENNReal.ofReal c * P univ ≤ P A := by
  have hsum : P A + P Aᶜ = P univ := measure_add_measure_compl hA
  have hsplit : ENNReal.ofReal c * P univ + ENNReal.ofReal (1 - c) * P univ = P univ := by
    rw [← add_mul, ← ENNReal.ofReal_add hc (by linarith), add_sub_cancel, ENNReal.ofReal_one,
      one_mul]
  have : ENNReal.ofReal c * P univ + ENNReal.ofReal (1 - c) * P univ ≤
      P A + ENNReal.ofReal (1 - c) * P univ := by
    rw [hsplit]; calc P univ = P A + P Aᶜ := hsum.symm
      _ ≤ P A + ENNReal.ofReal (1 - c) * P univ := add_le_add_right h _
  exact ENNReal.le_of_add_le_add_right
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) this

lemma measurable_det3 : Measurable fun x : E3 × E3 × E3 =>
    Matrix.det (Matrix.of fun i k : Fin 3 => (![x.1, x.2.1, x.2.2] i) k) := by
  apply Continuous.measurable
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i k
  fin_cases i
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous).comp continuous_fst
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous).comp (continuous_fst.comp continuous_snd)
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous).comp (continuous_snd.comp continuous_snd)

/-- **Sampling a spanning triple.** If a finite law of unit vectors of `ℝ³` puts mass at most
`(1 - c)` of the total in every open `ε`-slab about a plane through the origin, then three
independent draws have determinant at least `ε²` with probability at least `c²`. -/
theorem triple_det_lower (P : Measure E3) [IsFiniteMeasure P] (hunit : P {u | ‖u‖ ≠ 1} = 0)
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcap : ∀ ν : E3, ‖ν‖ = 1 → P {u | |inner ℝ ν u| < ε} ≤ ENNReal.ofReal (1 - c) * P univ) :
    ENNReal.ofReal (c ^ 2) * P univ ^ 3 ≤ (P.prod (P.prod P))
      {x | ε ^ 2 ≤ |Matrix.det (Matrix.of fun i k : Fin 3 => (![x.1, x.2.1, x.2.2] i) k)|} := by
  classical
  set m := P univ with hm
  set S : Set (E3 × E3 × E3) :=
    {x | ε ^ 2 ≤ |Matrix.det (Matrix.of fun i k : Fin 3 => (![x.1, x.2.1, x.2.2] i) k)|} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const measurable_det3.abs
  have hslab : ∀ ν : E3, MeasurableSet {u : E3 | |inner ℝ ν u| < ε} := fun ν =>
    measurableSet_lt (by fun_prop) measurable_const
  -- the inner bound for a fixed unit first vector
  have hinner : ∀ u₁ : E3, ‖u₁‖ = 1 →
      ENNReal.ofReal c * m * (ENNReal.ofReal c * m) ≤ (P.prod P) (Prod.mk u₁ ⁻¹' S) := by
    intro u₁ hu₁
    obtain ⟨ν, hν, horth⟩ := exists_unit_orth u₁
    set A : Set E3 := {u₂ | ε ≤ ‖cross3 u₁ u₂‖} with hA
    have hAm : MeasurableSet A := measurableSet_le measurable_const (by
      unfold cross3; fun_prop)
    have hAc : P Aᶜ ≤ ENNReal.ofReal (1 - c) * m := by
      refine le_trans (measure_mono ?_) (hcap ν hν)
      intro u₂ hu₂
      simp only [hA, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hu₂
      exact lt_of_le_of_lt (abs_inner_le_norm_cross3 hu₁ hν horth u₂) hu₂
    have hPA : ENNReal.ofReal c * m ≤ P A := ofReal_mul_le_of_compl P hAm hc hc1 hAc
    have hsecond : ∀ u₂ ∈ A, ENNReal.ofReal c * m ≤ P (Prod.mk u₂ ⁻¹' (Prod.mk u₁ ⁻¹' S)) := by
      intro u₂ hu₂
      have hpos : 0 < ‖cross3 u₁ u₂‖ := lt_of_lt_of_le hε hu₂
      set ν' : E3 := ‖cross3 u₁ u₂‖⁻¹ • cross3 u₁ u₂ with hν'
      have hν'1 : ‖ν'‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hpos)
      set B : Set E3 := {u₃ | ε ≤ |inner ℝ ν' u₃|} with hB
      have hBm : MeasurableSet B := measurableSet_le measurable_const (by fun_prop)
      have hBc : P Bᶜ ≤ ENNReal.ofReal (1 - c) * m := by
        refine le_trans (measure_mono ?_) (hcap ν' hν'1)
        intro u₃ hu₃
        simp only [hB, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hu₃
        exact hu₃
      refine (ofReal_mul_le_of_compl P hBm hc hc1 hBc).trans (measure_mono ?_)
      intro u₃ hu₃
      simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq]
      rw [← inner_cross3]
      have h1 : inner ℝ (cross3 u₁ u₂) u₃ = ‖cross3 u₁ u₂‖ * inner ℝ ν' u₃ := by
        rw [hν', real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
      rw [h1, abs_mul, abs_of_pos hpos, sq]
      exact mul_le_mul hu₂ hu₃ hε.le hpos.le
    calc ENNReal.ofReal c * m * (ENNReal.ofReal c * m)
        ≤ ENNReal.ofReal c * m * P A := by gcongr
      _ = ∫⁻ u₂, A.indicator (fun _ => ENNReal.ofReal c * m) u₂ ∂P := by
          rw [lintegral_indicator_const hAm, mul_comm]
      _ ≤ ∫⁻ u₂, P (Prod.mk u₂ ⁻¹' (Prod.mk u₁ ⁻¹' S)) ∂P := by
          apply lintegral_mono
          intro u₂
          by_cases hu₂ : u₂ ∈ A
          · rw [Set.indicator_of_mem hu₂]; exact hsecond u₂ hu₂
          · rw [Set.indicator_of_notMem hu₂]; exact zero_le
      _ = (P.prod P) (Prod.mk u₁ ⁻¹' S) :=
          (Measure.prod_apply (measurable_prodMk_left hSm)).symm
  have hU : MeasurableSet {u : E3 | ‖u‖ = 1} := measurableSet_eq_fun measurable_norm measurable_const
  calc ENNReal.ofReal (c ^ 2) * m ^ 3
      = (ENNReal.ofReal c * m * (ENNReal.ofReal c * m)) * m := by
        rw [sq, ENNReal.ofReal_mul hc]; ring
    _ = (ENNReal.ofReal c * m * (ENNReal.ofReal c * m)) * P {u : E3 | ‖u‖ = 1} := by
        congr 1
        have : P {u : E3 | ‖u‖ = 1}ᶜ = 0 := by
          have hc' : {u : E3 | ‖u‖ = 1}ᶜ = {u | ‖u‖ ≠ 1} := by ext u; simp
          rw [hc', hunit]
        rw [hm, ← measure_add_measure_compl hU, this, add_zero]
    _ = ∫⁻ u₁, {u : E3 | ‖u‖ = 1}.indicator
          (fun _ => ENNReal.ofReal c * m * (ENNReal.ofReal c * m)) u₁ ∂P := by
        rw [lintegral_indicator_const hU, mul_comm]
    _ ≤ ∫⁻ u₁, (P.prod P) (Prod.mk u₁ ⁻¹' S) ∂P := by
        apply lintegral_mono
        intro u₁
        by_cases hu₁ : u₁ ∈ {u : E3 | ‖u‖ = 1}
        · rw [Set.indicator_of_mem hu₁]; exact hinner u₁ hu₁
        · rw [Set.indicator_of_notMem hu₁]; exact zero_le
    _ = (P.prod (P.prod P)) S := (Measure.prod_apply hSm).symm

/-- **A plane through two velocity-separated lifted directions is a bounded graph.** If the unit
normal `(n₀, n₁, n₂)` of a plane is `ε`-orthogonal to two lifted velocities `(1, V₁, X₁)` and
`(1, V₂, X₂)` with `|Vᵢ|, |Xᵢ| ≤ K` and `|V₁ - V₂| ≥ δ`, and `ε` is small, then the hidden
component of the normal is bounded below. -/
lemma normal_hidden_lower {n₀ n₁ n₂ K δ ε V₁ X₁ V₂ X₂ : ℝ} (hn : n₀ ^ 2 + n₁ ^ 2 + n₂ ^ 2 = 1)
    (hK : 0 ≤ K) (hδ : 0 < δ) (hV₁ : |V₁| ≤ K) (hX₁ : |X₁| ≤ K) (hX₂ : |X₂| ≤ K)
    (hsep : δ ≤ |V₁ - V₂|) (h₁ : |n₀ + n₁ * V₁ + n₂ * X₁| ≤ ε) (h₂ : |n₀ + n₁ * V₂ + n₂ * X₂| ≤ ε)
    (hsmall : ε * (1 + 2 * (K + 1) / δ) ≤ 1 / 2) :
    1 / (2 * ((K + 1) * (2 * K / δ + 1))) ≤ |n₂| := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) h₁
  -- |n₁| δ ≤ 2ε + 2K |n₂|
  have hdiff : |n₁ * (V₁ - V₂) + n₂ * (X₁ - X₂)| ≤ 2 * ε := by
    have : n₁ * (V₁ - V₂) + n₂ * (X₁ - X₂) =
        (n₀ + n₁ * V₁ + n₂ * X₁) - (n₀ + n₁ * V₂ + n₂ * X₂) := by ring
    rw [this]
    calc |(n₀ + n₁ * V₁ + n₂ * X₁) - (n₀ + n₁ * V₂ + n₂ * X₂)|
        ≤ |n₀ + n₁ * V₁ + n₂ * X₁| + |n₀ + n₁ * V₂ + n₂ * X₂| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hX12 : |X₁ - X₂| ≤ 2 * K := by
    calc |X₁ - X₂| ≤ |X₁| + |X₂| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  have hn1 : |n₁| * δ ≤ 2 * ε + 2 * K * |n₂| := by
    calc |n₁| * δ ≤ |n₁| * |V₁ - V₂| := mul_le_mul_of_nonneg_left hsep (abs_nonneg _)
      _ = |n₁ * (V₁ - V₂)| := (abs_mul _ _).symm
      _ = |(n₁ * (V₁ - V₂) + n₂ * (X₁ - X₂)) - n₂ * (X₁ - X₂)| := by ring_nf
      _ ≤ |n₁ * (V₁ - V₂) + n₂ * (X₁ - X₂)| + |n₂ * (X₁ - X₂)| := abs_sub _ _
      _ ≤ 2 * ε + |n₂| * (2 * K) := by
          rw [abs_mul]; gcongr
      _ = 2 * ε + 2 * K * |n₂| := by ring
  have hn0 : |n₀| ≤ ε + K * |n₁| + K * |n₂| := by
    calc |n₀| = |(n₀ + n₁ * V₁ + n₂ * X₁) - n₁ * V₁ - n₂ * X₁| := by ring_nf
      _ ≤ |n₀ + n₁ * V₁ + n₂ * X₁| + |n₁ * V₁| + |n₂ * X₁| := by
          have := abs_sub (n₀ + n₁ * V₁ + n₂ * X₁ - n₁ * V₁) (n₂ * X₁)
          have := abs_sub (n₀ + n₁ * V₁ + n₂ * X₁) (n₁ * V₁)
          linarith
      _ ≤ ε + K * |n₁| + K * |n₂| := by
          rw [abs_mul, abs_mul]
          have := mul_le_mul_of_nonneg_left hV₁ (abs_nonneg n₁)
          have := mul_le_mul_of_nonneg_left hX₁ (abs_nonneg n₂)
          nlinarith
  have hsum : 1 ≤ |n₀| + |n₁| + |n₂| := by
    have h1 : (1 : ℝ) = n₀ ^ 2 + n₁ ^ 2 + n₂ ^ 2 := hn.symm
    have h2 : n₀ ^ 2 + n₁ ^ 2 + n₂ ^ 2 ≤ (|n₀| + |n₁| + |n₂|) ^ 2 := by
      have := abs_nonneg n₀; have := abs_nonneg n₁; have := abs_nonneg n₂
      nlinarith [sq_abs n₀, sq_abs n₁, sq_abs n₂, mul_nonneg (abs_nonneg n₀) (abs_nonneg n₁),
        mul_nonneg (abs_nonneg n₀) (abs_nonneg n₂), mul_nonneg (abs_nonneg n₁) (abs_nonneg n₂)]
    have h3 : 0 ≤ |n₀| + |n₁| + |n₂| := by positivity
    nlinarith
  have hn1' : |n₁| ≤ (2 * ε + 2 * K * |n₂|) / δ := by rw [le_div_iff₀ hδ]; exact hn1
  have key : 1 ≤ ε * (1 + 2 * (K + 1) / δ) + |n₂| * ((K + 1) * (2 * K / δ + 1)) := by
    have e1 : (K + 1) * |n₁| ≤ (K + 1) * ((2 * ε + 2 * K * |n₂|) / δ) :=
      mul_le_mul_of_nonneg_left hn1' (by linarith)
    have e2 : ε * (1 + 2 * (K + 1) / δ) + |n₂| * ((K + 1) * (2 * K / δ + 1)) =
        ε + (K + 1) * ((2 * ε + 2 * K * |n₂|) / δ) + (K + 1) * |n₂| := by
      field_simp; ring
    rw [e2]
    linarith
  have hpos : 0 < (K + 1) * (2 * K / δ + 1) := by positivity
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- With the hidden normal component bounded below, every lifted velocity `ε`-orthogonal to the
normal lies within `ε / |n₂|` of the graph `X = G₀ + G₁ V`, `G₀ = -n₀/n₂`, `G₁ = -n₁/n₂`. -/
lemma graph_residual_of_normal {n₀ n₁ n₂ ε V X : ℝ} (hn₂ : n₂ ≠ 0)
    (h : |n₀ + n₁ * V + n₂ * X| ≤ ε) : |X - (-n₀ / n₂) - (-n₁ / n₂) * V| ≤ ε / |n₂| := by
  have : X - (-n₀ / n₂) - (-n₁ / n₂) * V = (n₀ + n₁ * V + n₂ * X) / n₂ := by
    field_simp; ring
  rw [this, abs_div]
  exact div_le_div_of_nonneg_right h (abs_nonneg _)

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
