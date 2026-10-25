/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/SheetGroupMatching.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Lib.K4QuadSheetMatching.Matching
import Submission.Obl.k4_local_algebraic_graph_matching
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetJets

/-!
# Local matching for one group of sheets, with reference weights

The accepted local algebraic graph matching (o112) excludes a pair law that is supported on
pairs of sheets agreeing at their events while differing on the comparison ball, provided each
colour's index-base marginals are bounded by its probability weights. Here the weights are
reference weights `T` with arbitrary totals: a pair law whose index-base marginals are at most
`CT * T i` times Lebesgue measure, supported on such bad pairs inside one group, has mass at most
`CT * R ^ (-ε₀)` times the reference total of the group. No floor on individual index masses is
used (paper, proof of Lemma 8.3: the separate colour priors `p_i = T_i / W_c`).

Coordinates: sheets are holomorphic on the ball of radius `4` and real on the real unit ball
(`IsSheet`); events and discrepancy witnesses lie in the real ball of radius `1/4`, closeness to
the reference holds on the real ball of radius `1/2`. The proof rescales by `2` and applies o112.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise

noncomputable section

/-- Sets cut out by a bound on a function continuous on a closed ball are measurable. -/
theorem measurableSet_norm_le_of_continuousOn {g : EuclideanSpace ℝ (Fin 3) → ℂ} {r c : ℝ}
    (hg : ContinuousOn g (closedBall 0 r)) :
    MeasurableSet {z : EuclideanSpace ℝ (Fin 3) | ‖z‖ ≤ r ∧ ‖g z‖ ≤ c} := by
  have h := hg.preimage_isClosed_of_isClosed isClosed_closedBall
    (isClosed_closedBall : IsClosed (closedBall (0 : ℂ) c))
  have : {z : EuclideanSpace ℝ (Fin 3) | ‖z‖ ≤ r ∧ ‖g z‖ ≤ c} =
      closedBall 0 r ∩ g ⁻¹' closedBall 0 c := by
    ext z
    simp [mem_closedBall, dist_zero_right]
  rw [this]
  exact h.measurableSet

theorem continuous_emb : Continuous emb := by
  unfold emb
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => Complex.continuous_ofReal.comp ((continuous_apply i).comp
      (PiLp.continuous_ofLp 2 _)))

/-- The difference of two sheets is continuous on the real closed ball of radius `r < 4`. -/
theorem continuousOn_sheet_sub {D : ℕ} {f g : EuclideanSpace ℂ (Fin 3) → ℂ}
    (hf : IsSheet D f) (hg : IsSheet D g) {r : ℝ} (hr : r < 4) :
    ContinuousOn (fun z : EuclideanSpace ℝ (Fin 3) => f (emb z) - g (emb z)) (closedBall 0 r) := by
  obtain ⟨_, _, _, hfh, _, _⟩ := hf
  obtain ⟨_, _, _, hgh, _, _⟩ := hg
  have hmaps : MapsTo emb (closedBall (0 : EuclideanSpace ℝ (Fin 3)) r) (ball 0 4) := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff, norm_emb]
    linarith
  exact (hfh.continuousOn.comp continuous_emb.continuousOn hmaps).sub
    (hgh.continuousOn.comp continuous_emb.continuousOn hmaps)

/-- **Local matching for one group**, with reference weights, from the accepted o112. -/
theorem group_matching (hTC : Submission.Lib.K4QuadSheetMatching.TwoColorStatement)
    (D : ℕ) (hD : 1 ≤ D) (d₀ : ℝ) (hd0 : 0 ≤ d₀) (hd1 : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ (R M CT : ℝ), R₀ ≤ R → 0 < M → 0 < CT →
    ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
      (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ)
      (f₀ : EuclideanSpace ℝ (Fin 3) → ℂ) (T₁ : Fin n₁ → ℝ) (T₂ : Fin n₂ → ℝ)
      (G₁ : Finset (Fin n₁)) (G₂ : Finset (Fin n₂))
      (μ : Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))),
    IsFiniteMeasure μ →
    (G₁.card : ℝ) ≤ R ^ (d₀ + ε₀) → (G₂.card : ℝ) ≤ R ^ (d₀ + ε₀) →
    (∀ i ∈ G₁, IsSheet D (f₁ i)) → (∀ j ∈ G₂, IsSheet D (f₂ j)) →
    (∀ i ∈ G₁, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 → ‖f₁ i (emb x) - f₀ x‖ ≤ M * R ^ ε₀) →
    (∀ j ∈ G₂, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 → ‖f₂ j (emb x) - f₀ x‖ ≤ M * R ^ ε₀) →
    (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
    (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
      μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (CT * T₁ i) * volume U) →
    (∀ (j : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
      μ {p | p.1.2 = j ∧ p.2 ∈ U} ≤ ENNReal.ofReal (CT * T₂ j) * volume U) →
    (∀ᵐ p ∂μ, p.1.1 ∈ G₁ ∧ p.1.2 ∈ G₂ ∧ ‖p.2‖ ≤ 1 / 4 ∧
      ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ M * R ^ (-1 + ε₀) ∧
      ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 ∧
        M * R ^ (-ε₀) ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖) →
    μ Set.univ ≤ ENNReal.ofReal (CT * R ^ (-ε₀) * (∑ i ∈ G₁, T₁ i + ∑ j ∈ G₂, T₂ j)) := by
  classical
  obtain ⟨ε₀, hε₀, R₀, hR₀, H⟩ := Submission.k4_local_algebraic_graph_matching hTC D d₀ hd0 hd1
  refine ⟨ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R M CT hR hM hCT n₁ n₂ f₁ f₂ f₀ T₁ T₂ G₁ G₂ μ hfin hn₁ hn₂ hs₁ hs₂ hcl₁ hcl₂ hT₁ hT₂
    hmar₁ hmar₂ hae
  set W₁ := ∑ i ∈ G₁, T₁ i with hW₁def
  set W₂ := ∑ j ∈ G₂, T₂ j with hW₂def
  by_contra hcon
  rw [not_le] at hcon
  have hRpos : 0 < R := by linarith
  have hμpos : 0 < μ univ := lt_of_le_of_lt zero_le hcon
  have hμfin : μ univ ≠ ⊤ := measure_ne_top μ univ
  set B := (μ univ).toReal with hBdef
  have hBpos : 0 < B := ENNReal.toReal_pos hμpos.ne' hμfin
  have hBeq : ENNReal.ofReal B = μ univ := ENNReal.ofReal_toReal hμfin
  have hW₁ : 0 ≤ W₁ := Finset.sum_nonneg fun i _ => hT₁ i
  have hW₂ : 0 ≤ W₂ := Finset.sum_nonneg fun j _ => hT₂ j
  have hBW : CT * R ^ (-ε₀) * (W₁ + W₂) < B := by
    rwa [← hBeq, ENNReal.ofReal_lt_ofReal_iff hBpos] at hcon
  have hRe : 0 < R ^ (-ε₀) := Real.rpow_pos_of_pos hRpos _
  -- the good events
  have hae' := ae_iff.mp hae
  have hgood1 : μ {p | p.1.1 ∉ G₁} = 0 := by
    refine measure_mono_null ?_ hae'
    intro p hp hg
    exact hp hg.1
  have hgood2 : μ {p | p.1.2 ∉ G₂} = 0 := by
    refine measure_mono_null ?_ hae'
    intro p hp hg
    exact hp hg.2.1
  -- both reference totals are positive
  have hW₁pos : 0 < W₁ := by
    by_contra h
    have hzero : ∀ i ∈ G₁, T₁ i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hT₁ i)).mp (le_antisymm (not_lt.mp h) hW₁)
    have hle : μ univ ≤ ∑ i ∈ G₁, μ {p | p.1.1 = i ∧ p.2 ∈ univ} + μ {p | p.1.1 ∉ G₁} := by
      calc μ univ ≤ μ ((⋃ i ∈ G₁, {p : (Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3) |
              p.1.1 = i ∧ p.2 ∈ univ}) ∪ {p | p.1.1 ∉ G₁}) := by
            apply measure_mono
            intro p _
            by_cases hp : p.1.1 ∈ G₁
            · exact Or.inl (Set.mem_biUnion hp ⟨rfl, trivial⟩)
            · exact Or.inr hp
        _ ≤ μ (⋃ i ∈ G₁, {p : (Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3) |
              p.1.1 = i ∧ p.2 ∈ univ}) + μ {p | p.1.1 ∉ G₁} := measure_union_le _ _
        _ ≤ _ := by gcongr; exact measure_biUnion_finset_le _ _
    have : μ univ = 0 := by
      refine le_antisymm (hle.trans ?_) zero_le
      rw [hgood1, add_zero]
      refine (Finset.sum_le_sum fun i hi => hmar₁ i univ MeasurableSet.univ).trans ?_
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro i hi
      simp [hzero i hi]
    exact hμpos.ne' this
  have hW₂pos : 0 < W₂ := by
    by_contra h
    have hzero : ∀ j ∈ G₂, T₂ j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hT₂ j)).mp (le_antisymm (not_lt.mp h) hW₂)
    have hle : μ univ ≤ ∑ j ∈ G₂, μ {p | p.1.2 = j ∧ p.2 ∈ univ} + μ {p | p.1.2 ∉ G₂} := by
      calc μ univ ≤ μ ((⋃ j ∈ G₂, {p : (Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3) |
              p.1.2 = j ∧ p.2 ∈ univ}) ∪ {p | p.1.2 ∉ G₂}) := by
            apply measure_mono
            intro p _
            by_cases hp : p.1.2 ∈ G₂
            · exact Or.inl (Set.mem_biUnion hp ⟨rfl, trivial⟩)
            · exact Or.inr hp
        _ ≤ μ (⋃ j ∈ G₂, {p : (Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3) |
              p.1.2 = j ∧ p.2 ∈ univ}) + μ {p | p.1.2 ∉ G₂} := measure_union_le _ _
        _ ≤ _ := by gcongr; exact measure_biUnion_finset_le _ _
    have : μ univ = 0 := by
      refine le_antisymm (hle.trans ?_) zero_le
      rw [hgood2, add_zero]
      refine (Finset.sum_le_sum fun j hj => hmar₂ j univ MeasurableSet.univ).trans ?_
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro j hj
      simp [hzero j hj]
    exact hμpos.ne' this
  -- nonempty groups
  have hG₁ : G₁.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    simp [hW₁def, h] at hW₁pos
  have hG₂ : G₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    simp [hW₂def, h] at hW₂pos
  obtain ⟨i₀, hi₀⟩ := hG₁
  obtain ⟨j₀, hj₀⟩ := hG₂
  -- reindexing and rescaling
  set e₁ := G₁.equivFin with he₁
  set e₂ := G₂.equivFin with he₂
  let g₁ : Fin G₁.card → EuclideanSpace ℂ (Fin 3) → ℂ :=
    fun i z => f₁ (e₁.symm i) (((1 / 2 : ℝ) : ℂ) • z)
  let g₂ : Fin G₂.card → EuclideanSpace ℂ (Fin 3) → ℂ :=
    fun j z => f₂ (e₂.symm j) (((1 / 2 : ℝ) : ℂ) • z)
  have hg₁ : ∀ i, IsSheet D (g₁ i) := fun i =>
    (hs₁ _ (e₁.symm i).2).comp_smul (by norm_num) (by norm_num)
  have hg₂ : ∀ j, IsSheet D (g₂ j) := fun j =>
    (hs₂ _ (e₂.symm j).2).comp_smul (by norm_num) (by norm_num)
  choose P₁ hP₁ using hg₁
  choose P₂ hP₂ using hg₂
  have hg₁emb : ∀ i (x : EuclideanSpace ℝ (Fin 3)),
      g₁ i (emb x) = f₁ (e₁.symm i) (emb ((1 / 2 : ℝ) • x)) := by
    intro i x
    simp only [g₁, emb_smul]
  have hg₂emb : ∀ j (x : EuclideanSpace ℝ (Fin 3)),
      g₂ j (emb x) = f₂ (e₂.symm j) (emb ((1 / 2 : ℝ) • x)) := by
    intro j x
    simp only [g₂, emb_smul]
  let f₀' : EuclideanSpace ℝ (Fin 3) → ℂ := fun x => f₀ ((1 / 2 : ℝ) • x)
  -- the map to the group's coordinates
  let ψ : Fin n₁ × Fin n₂ → Fin G₁.card × Fin G₂.card := fun ij =>
    if h : ij.1 ∈ G₁ ∧ ij.2 ∈ G₂ then (e₁ ⟨ij.1, h.1⟩, e₂ ⟨ij.2, h.2⟩)
    else (e₁ ⟨i₀, hi₀⟩, e₂ ⟨j₀, hj₀⟩)
  let φ : (Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3) →
      (Fin G₁.card × Fin G₂.card) × EuclideanSpace ℝ (Fin 3) :=
    Prod.map ψ (fun z => (2 : ℝ) • z)
  have hφ : Measurable φ := (Measurable.of_discrete).prodMap (measurable_const_smul (2 : ℝ))
  let μ' : Measure ((Fin G₁.card × Fin G₂.card) × EuclideanSpace ℝ (Fin 3)) :=
    (μ univ)⁻¹ • μ.map φ
  have hμ'univ : μ' univ = 1 := by
    simp only [μ', Measure.smul_apply, smul_eq_mul, Measure.map_apply hφ MeasurableSet.univ,
      preimage_univ]
    exact ENNReal.inv_mul_cancel hμpos.ne' hμfin
  -- probability weights
  let π₁ : Fin G₁.card → ℝ := fun i => T₁ (e₁.symm i) / W₁
  let π₂ : Fin G₂.card → ℝ := fun j => T₂ (e₂.symm j) / W₂
  have hπ₁sum : ∑ i, π₁ i = 1 := by
    have : ∑ i, T₁ (e₁.symm i : Fin n₁) = W₁ := by
      rw [e₁.symm.sum_comp (fun x : G₁ => T₁ (x : Fin n₁)), Finset.sum_coe_sort G₁ T₁]
    simp only [π₁, ← Finset.sum_div, this, div_self hW₁pos.ne']
  have hπ₂sum : ∑ j, π₂ j = 1 := by
    have : ∑ j, T₂ (e₂.symm j : Fin n₂) = W₂ := by
      rw [e₂.symm.sum_comp (fun x : G₂ => T₂ (x : Fin n₂)), Finset.sum_coe_sort G₂ T₂]
    simp only [π₂, ← Finset.sum_div, this, div_self hW₂pos.ne']
  have hπ₁nn : ∀ i, 0 ≤ π₁ i := fun i => div_nonneg (hT₁ _) hW₁
  have hπ₂nn : ∀ j, 0 ≤ π₂ j := fun j => div_nonneg (hT₂ _) hW₂
  -- volume of a halved set
  have hvol : ∀ U : Set (EuclideanSpace ℝ (Fin 3)),
      volume ((2 : ℝ)⁻¹ • U) = ENNReal.ofReal (1 / 8) * volume U := by
    intro U
    rw [Measure.addHaar_smul, finrank_euclideanSpace_fin]
    congr 2
    norm_num
  -- the ratio needed for the marginal ceilings
  have hratio : ∀ (W T : ℝ), 0 < W → 0 ≤ T → W ≤ W₁ + W₂ →
      B⁻¹ * (CT * T) * (1 / 8) ≤ R ^ ε₀ * (T / W) := by
    intro W T hW hT hWle
    have h1 : CT * W * R ^ (-ε₀) ≤ B := by
      have := mul_le_mul_of_nonneg_left hWle (by positivity : (0 : ℝ) ≤ CT * R ^ (-ε₀))
      nlinarith [hBW]
    have h2 : CT * W ≤ B * R ^ ε₀ := by
      have hRR : R ^ (-ε₀) * R ^ ε₀ = 1 := by
        rw [← Real.rpow_add hRpos]; simp
      calc CT * W = CT * W * R ^ (-ε₀) * R ^ ε₀ := by rw [mul_assoc, hRR, mul_one]
        _ ≤ B * R ^ ε₀ := by gcongr
    have key : B⁻¹ * CT * (1 / 8) ≤ R ^ ε₀ * W⁻¹ := by
      rw [show B⁻¹ * CT * (1 / 8) = CT / (8 * B) by field_simp,
        show R ^ ε₀ * W⁻¹ = R ^ ε₀ / W by ring, div_le_div_iff₀ (by positivity) hW]
      nlinarith [h2, Real.rpow_pos_of_pos hRpos ε₀]
    calc B⁻¹ * (CT * T) * (1 / 8) = (B⁻¹ * CT * (1 / 8)) * T := by ring
      _ ≤ (R ^ ε₀ * W⁻¹) * T := mul_le_mul_of_nonneg_right key hT
      _ = R ^ ε₀ * (T / W) := by ring
  have hinvB : (μ univ)⁻¹ = ENNReal.ofReal B⁻¹ := by
    rw [← hBeq, ENNReal.ofReal_inv_of_pos hBpos]
  -- preimages of marginal events
  have hpre₁ : ∀ (i : Fin G₁.card) (U : Set (EuclideanSpace ℝ (Fin 3))),
      φ ⁻¹' {q | q.1.1 = i ∧ q.2 ∈ U} ⊆
        ({p | p.1.1 = (e₁.symm i : Fin n₁) ∧ p.2 ∈ (2 : ℝ)⁻¹ • U} ∪ {p | p.1.1 ∉ G₁}) ∪
          {p | p.1.2 ∉ G₂} := by
    intro i U p hp
    simp only [mem_preimage, mem_setOf_eq, φ, Prod.map] at hp
    by_cases h : p.1.1 ∈ G₁ ∧ p.1.2 ∈ G₂
    · left; left
      simp only [ψ, dif_pos h] at hp
      refine ⟨?_, ?_⟩
      · have := congrArg e₁.symm hp.1
        rw [Equiv.symm_apply_apply] at this
        rw [← this]
      · exact (Set.mem_inv_smul_set_iff₀ two_ne_zero _ _).mpr hp.2
    · by_cases h1 : p.1.1 ∈ G₁
      · right; exact fun h2 => h ⟨h1, h2⟩
      · left; right; exact h1
  have hpre₂ : ∀ (j : Fin G₂.card) (U : Set (EuclideanSpace ℝ (Fin 3))),
      φ ⁻¹' {q | q.1.2 = j ∧ q.2 ∈ U} ⊆
        ({p | p.1.2 = (e₂.symm j : Fin n₂) ∧ p.2 ∈ (2 : ℝ)⁻¹ • U} ∪ {p | p.1.1 ∉ G₁}) ∪
          {p | p.1.2 ∉ G₂} := by
    intro j U p hp
    simp only [mem_preimage, mem_setOf_eq, φ, Prod.map] at hp
    by_cases h : p.1.1 ∈ G₁ ∧ p.1.2 ∈ G₂
    · left; left
      simp only [ψ, dif_pos h] at hp
      refine ⟨?_, ?_⟩
      · have := congrArg e₂.symm hp.1
        rw [Equiv.symm_apply_apply] at this
        rw [← this]
      · exact (Set.mem_inv_smul_set_iff₀ two_ne_zero _ _).mpr hp.2
    · by_cases h1 : p.1.1 ∈ G₁
      · right; exact fun h2 => h ⟨h1, h2⟩
      · left; right; exact h1
  have hmar₁' : ∀ (i : Fin G₁.card) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
      μ' {q | q.1.1 = i ∧ q.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε₀ * π₁ i) * volume U := by
    intro i U hU
    have hmeas : MeasurableSet {q : (Fin G₁.card × Fin G₂.card) × EuclideanSpace ℝ (Fin 3) |
        q.1.1 = i ∧ q.2 ∈ U} :=
      ((measurableSet_singleton i).preimage measurable_fst.fst).inter (hU.preimage measurable_snd)
    simp only [μ', Measure.smul_apply, smul_eq_mul, Measure.map_apply hφ hmeas]
    have hle : μ (φ ⁻¹' {q | q.1.1 = i ∧ q.2 ∈ U}) ≤
        ENNReal.ofReal (CT * T₁ (e₁.symm i)) * (ENNReal.ofReal (1 / 8) * volume U) := by
      calc μ (φ ⁻¹' {q | q.1.1 = i ∧ q.2 ∈ U})
          ≤ μ (({p | p.1.1 = (e₁.symm i : Fin n₁) ∧ p.2 ∈ (2 : ℝ)⁻¹ • U} ∪ {p | p.1.1 ∉ G₁}) ∪
              {p | p.1.2 ∉ G₂}) := measure_mono (hpre₁ i U)
        _ ≤ μ {p | p.1.1 = (e₁.symm i : Fin n₁) ∧ p.2 ∈ (2 : ℝ)⁻¹ • U} + μ {p | p.1.1 ∉ G₁} +
              μ {p | p.1.2 ∉ G₂} :=
            (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
        _ = μ {p | p.1.1 = (e₁.symm i : Fin n₁) ∧ p.2 ∈ (2 : ℝ)⁻¹ • U} := by
            rw [hgood1, hgood2, add_zero, add_zero]
        _ ≤ ENNReal.ofReal (CT * T₁ (e₁.symm i)) * volume ((2 : ℝ)⁻¹ • U) :=
            hmar₁ _ _ (hU.const_smul₀ _)
        _ = _ := by rw [hvol]
    calc (μ univ)⁻¹ * μ (φ ⁻¹' {q | q.1.1 = i ∧ q.2 ∈ U})
        ≤ ENNReal.ofReal B⁻¹ * (ENNReal.ofReal (CT * T₁ (e₁.symm i)) *
            (ENNReal.ofReal (1 / 8) * volume U)) := by rw [hinvB]; gcongr
      _ = ENNReal.ofReal (B⁻¹ * (CT * T₁ (e₁.symm i)) * (1 / 8)) * volume U := by
          rw [ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hBpos.le)
              (mul_nonneg hCT.le (hT₁ _))), ENNReal.ofReal_mul (inv_nonneg.mpr hBpos.le)]
          ring
      _ ≤ ENNReal.ofReal (R ^ ε₀ * π₁ i) * volume U :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal
            (hratio W₁ (T₁ (e₁.symm i)) hW₁pos (hT₁ _) (by linarith))) _
  have hmar₂' : ∀ (j : Fin G₂.card) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
      μ' {q | q.1.2 = j ∧ q.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε₀ * π₂ j) * volume U := by
    intro j U hU
    have hmeas : MeasurableSet {q : (Fin G₁.card × Fin G₂.card) × EuclideanSpace ℝ (Fin 3) |
        q.1.2 = j ∧ q.2 ∈ U} :=
      ((measurableSet_singleton j).preimage measurable_fst.snd).inter (hU.preimage measurable_snd)
    simp only [μ', Measure.smul_apply, smul_eq_mul, Measure.map_apply hφ hmeas]
    have hle : μ (φ ⁻¹' {q | q.1.2 = j ∧ q.2 ∈ U}) ≤
        ENNReal.ofReal (CT * T₂ (e₂.symm j)) * (ENNReal.ofReal (1 / 8) * volume U) := by
      calc μ (φ ⁻¹' {q | q.1.2 = j ∧ q.2 ∈ U})
          ≤ μ (({p | p.1.2 = (e₂.symm j : Fin n₂) ∧ p.2 ∈ (2 : ℝ)⁻¹ • U} ∪ {p | p.1.1 ∉ G₁}) ∪
              {p | p.1.2 ∉ G₂}) := measure_mono (hpre₂ j U)
        _ ≤ μ {p | p.1.2 = (e₂.symm j : Fin n₂) ∧ p.2 ∈ (2 : ℝ)⁻¹ • U} + μ {p | p.1.1 ∉ G₁} +
              μ {p | p.1.2 ∉ G₂} :=
            (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
        _ = μ {p | p.1.2 = (e₂.symm j : Fin n₂) ∧ p.2 ∈ (2 : ℝ)⁻¹ • U} := by
            rw [hgood1, hgood2, add_zero, add_zero]
        _ ≤ ENNReal.ofReal (CT * T₂ (e₂.symm j)) * volume ((2 : ℝ)⁻¹ • U) :=
            hmar₂ _ _ (hU.const_smul₀ _)
        _ = _ := by rw [hvol]
    calc (μ univ)⁻¹ * μ (φ ⁻¹' {q | q.1.2 = j ∧ q.2 ∈ U})
        ≤ ENNReal.ofReal B⁻¹ * (ENNReal.ofReal (CT * T₂ (e₂.symm j)) *
            (ENNReal.ofReal (1 / 8) * volume U)) := by rw [hinvB]; gcongr
      _ = ENNReal.ofReal (B⁻¹ * (CT * T₂ (e₂.symm j)) * (1 / 8)) * volume U := by
          rw [ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hBpos.le)
              (mul_nonneg hCT.le (hT₂ _))), ENNReal.ofReal_mul (inv_nonneg.mpr hBpos.le)]
          ring
      _ ≤ ENNReal.ofReal (R ^ ε₀ * π₂ j) * volume U :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal
            (hratio W₂ (T₂ (e₂.symm j)) hW₂pos (hT₂ _) (by linarith))) _
  -- the bad events in the group's coordinates
  let bad : Set ((Fin G₁.card × Fin G₂.card) × EuclideanSpace ℝ (Fin 3)) :=
    {q | ‖q.2‖ ≤ 1 / 2 ∧ ‖g₁ q.1.1 (emb q.2) - g₂ q.1.2 (emb q.2)‖ ≤ M * R ^ (-1 + ε₀) ∧
      ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 ∧
        M * R ^ (-ε₀) ≤ ‖g₁ q.1.1 (emb x) - g₂ q.1.2 (emb x)‖}
  have hbad_meas : MeasurableSet bad := by
    have hrepr : bad = ⋃ ij : Fin G₁.card × Fin G₂.card, ({ij} ×ˢ
        ({z : EuclideanSpace ℝ (Fin 3) | ‖z‖ ≤ 1 / 2 ∧
            ‖g₁ ij.1 (emb z) - g₂ ij.2 (emb z)‖ ≤ M * R ^ (-1 + ε₀)} ∩
          {_z | ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 ∧
            M * R ^ (-ε₀) ≤ ‖g₁ ij.1 (emb x) - g₂ ij.2 (emb x)‖})) := by
      ext q
      simp only [bad, mem_setOf_eq, mem_iUnion, mem_prod, mem_singleton_iff, mem_inter_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨q.1, rfl, ⟨h1, h2⟩, h3⟩
      · rintro ⟨ij, rfl, ⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [hrepr]
    refine MeasurableSet.iUnion fun ij => (measurableSet_singleton ij).prod ?_
    exact (measurableSet_norm_le_of_continuousOn
      (continuousOn_sheet_sub ⟨P₁ ij.1, hP₁ ij.1⟩ ⟨P₂ ij.2, hP₂ ij.2⟩ (by norm_num))).inter
      (MeasurableSet.const _)
  have hbad : μ' badᶜ = 0 := by
    simp only [μ', Measure.smul_apply, smul_eq_mul, Measure.map_apply hφ hbad_meas.compl]
    have hnull : μ (φ ⁻¹' badᶜ) = 0 := by
      refine measure_mono_null ?_ hae'
      intro p hp hgood
      apply hp
      obtain ⟨h1, h2, h3, h4, x, hx, h5⟩ := hgood
      have hψ : ψ p.1 = (e₁ ⟨p.1.1, h1⟩, e₂ ⟨p.1.2, h2⟩) := by
        simp only [ψ, dif_pos (And.intro h1 h2)]
      have hev₁ : ∀ z : EuclideanSpace ℝ (Fin 3),
          g₁ (e₁ ⟨p.1.1, h1⟩) (emb ((2 : ℝ) • z)) = f₁ p.1.1 (emb z) := by
        intro z
        rw [hg₁emb, Equiv.symm_apply_apply, smul_smul]
        norm_num
      have hev₂ : ∀ z : EuclideanSpace ℝ (Fin 3),
          g₂ (e₂ ⟨p.1.2, h2⟩) (emb ((2 : ℝ) • z)) = f₂ p.1.2 (emb z) := by
        intro z
        rw [hg₂emb, Equiv.symm_apply_apply, smul_smul]
        norm_num
      show φ p ∈ bad
      simp only [φ, Prod.map, hψ, bad, mem_setOf_eq]
      refine ⟨?_, ?_, (2 : ℝ) • x, ?_, ?_⟩
      · rw [norm_smul, Real.norm_two]; linarith
      · rw [hev₁, hev₂]; exact h4
      · rw [norm_smul, Real.norm_two]; linarith
      · rw [hev₁, hev₂]; exact h5
    rw [hnull, mul_zero]
  -- apply the accepted local matching
  have hR1 : ENNReal.ofReal (R ^ (-ε₀)) ≤ μ' univ := by
    rw [hμ'univ, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith))
  exact H R M ε₀ hR hM hε₀ le_rfl G₁.card G₂.card g₁ g₂ P₁ P₂ f₀' π₁ π₂ μ' hn₁ hn₂
    (fun i => ⟨(hP₁ i).1, (hP₁ i).2.1, (hP₁ i).2.2.1, (hP₁ i).2.2.2.1, fun x hx =>
      ⟨(hP₁ i).2.2.2.2 x hx, by
        show ‖g₁ i (emb x) - f₀ ((1 / 2 : ℝ) • x)‖ ≤ M * R ^ ε₀
        rw [hg₁emb]
        exact hcl₁ _ (e₁.symm i).2 _ (by rw [norm_smul]; norm_num; linarith)⟩⟩)
    (fun j => ⟨(hP₂ j).1, (hP₂ j).2.1, (hP₂ j).2.2.1, (hP₂ j).2.2.2.1, fun x hx =>
      ⟨(hP₂ j).2.2.2.2 x hx, by
        show ‖g₂ j (emb x) - f₀ ((1 / 2 : ℝ) • x)‖ ≤ M * R ^ ε₀
        rw [hg₂emb]
        exact hcl₂ _ (e₂.symm j).2 _ (by rw [norm_smul]; norm_num; linarith)⟩⟩)
    hπ₁nn hπ₂nn hπ₁sum hπ₂sum hR1 hμ'univ.le hmar₁' hmar₂' hbad

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
