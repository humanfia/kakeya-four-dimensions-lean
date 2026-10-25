-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.QuadGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalFlatAssembly
-- Copied from session x0338 (o070 branch, commit ec01e52, file QuadGeometry.lean), namespace renamed.

/-!
# Geometry for the quadratic prism count

* `Cyl m w r h`: the closed cylinder of radius `r` and half-length `h` about the line through `m`
  with direction `w`; convex and compact.
* `end_thirds`: a compact convex set `V` has at least `1/27` of its volume in each of its two end
  thirds along any direction (homothety of ratio `1/3` at an extreme point).
* `sum_mul_volume_le_of_disjoint`: if the products `E₁ i × E₂ i` of measurable subsets of `Ω` are
  pairwise disjoint, then `∑ |E₁ i| |E₂ i| ≤ |Ω|²`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory Metric
open scoped RealInnerProductSpace

/-- The closed cylinder of radius `r` and half-length `h` about the line through `m` with
direction `w`. -/
def Cyl (m w : Space) (r h : ℝ) : Set Space :=
  {y | ‖(y - m) - ⟪w, y - m⟫ • w‖ ≤ r ∧ |⟪w, y - m⟫| ≤ h}

lemma cyl_convex (m w : Space) (r h : ℝ) : Convex ℝ (Cyl m w r h) := by
  intro y₁ hy₁ y₂ hy₂ s t hs ht hst
  obtain ⟨h1, h1'⟩ := hy₁
  obtain ⟨h2, h2'⟩ := hy₂
  have key : s • y₁ + t • y₂ - m = s • (y₁ - m) + t • (y₂ - m) := by
    have : m = (s + t) • m := by rw [hst, one_smul]
    conv_lhs => rw [this]
    module
  have hin : ⟪w, s • y₁ + t • y₂ - m⟫ = s * ⟪w, y₁ - m⟫ + t * ⟪w, y₂ - m⟫ := by
    rw [key, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  refine ⟨?_, ?_⟩
  · have hv : (s • y₁ + t • y₂ - m) - ⟪w, s • y₁ + t • y₂ - m⟫ • w =
        s • ((y₁ - m) - ⟪w, y₁ - m⟫ • w) + t • ((y₂ - m) - ⟪w, y₂ - m⟫ • w) := by
      rw [hin, key]
      module
    rw [hv]
    calc ‖s • ((y₁ - m) - ⟪w, y₁ - m⟫ • w) + t • ((y₂ - m) - ⟪w, y₂ - m⟫ • w)‖
        ≤ s * ‖(y₁ - m) - ⟪w, y₁ - m⟫ • w‖ + t * ‖(y₂ - m) - ⟪w, y₂ - m⟫ • w‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
      _ ≤ s * r + t * r := by gcongr
      _ = r := by rw [← add_mul, hst, one_mul]
  · rw [hin]
    calc |s * ⟪w, y₁ - m⟫ + t * ⟪w, y₂ - m⟫| ≤ s * |⟪w, y₁ - m⟫| + t * |⟪w, y₂ - m⟫| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * h + t * h := by gcongr
      _ = h := by rw [← add_mul, hst, one_mul]

lemma cyl_isClosed (m w : Space) (r h : ℝ) : IsClosed (Cyl m w r h) := by
  have hc1 : Continuous fun y : Space => ‖(y - m) - ⟪w, y - m⟫ • w‖ := by fun_prop
  have hc2 : Continuous fun y : Space => |⟪w, y - m⟫| := by fun_prop
  exact (isClosed_le hc1 continuous_const).inter (isClosed_le hc2 continuous_const)

lemma norm_sub_le_of_mem_cyl {m w y : Space} {r h : ℝ} (hw : ‖w‖ = 1)
    (hy : y ∈ Cyl m w r h) : ‖y - m‖ ≤ r + h := by
  obtain ⟨h1, h2⟩ := hy
  have e : y - m = ((y - m) - ⟪w, y - m⟫ • w) + ⟪w, y - m⟫ • w := by abel
  calc ‖y - m‖ = ‖((y - m) - ⟪w, y - m⟫ • w) + ⟪w, y - m⟫ • w‖ := by rw [← e]
    _ ≤ ‖(y - m) - ⟪w, y - m⟫ • w‖ + ‖⟪w, y - m⟫ • w‖ := norm_add_le _ _
    _ ≤ r + h := by
        rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
        exact add_le_add h1 h2

lemma cyl_isCompact {m w : Space} (hw : ‖w‖ = 1) (r h : ℝ) : IsCompact (Cyl m w r h) := by
  apply Metric.isCompact_of_isClosed_isBounded (cyl_isClosed m w r h)
  rw [Metric.isBounded_iff_subset_closedBall m]
  exact ⟨r + h, fun y hy => by
    rw [mem_closedBall, dist_eq_norm]
    exact norm_sub_le_of_mem_cyl hw hy⟩

/-! ### End thirds -/

lemma finrank_space : Module.finrank ℝ Space = 3 := by
  simp [Space]

/-- **End thirds.**  A nonempty compact convex set has at least `1/27` of its volume in each end
third along a direction `w`. -/
theorem end_thirds {V : Set Space} (hV : Convex ℝ V) (hVc : IsCompact V) (hne : V.Nonempty)
    (w : Space) :
    ∃ t₀ t₁ : ℝ, (∀ y ∈ V, t₀ ≤ ⟪w, y⟫ ∧ ⟪w, y⟫ ≤ t₁) ∧ (∃ y ∈ V, ⟪w, y⟫ = t₀) ∧
      (∃ y ∈ V, ⟪w, y⟫ = t₁) ∧
      volume V ≤ 27 * volume (V ∩ {y | ⟪w, y⟫ ≤ t₀ + (t₁ - t₀) / 3}) ∧
      volume V ≤ 27 * volume (V ∩ {y | t₁ - (t₁ - t₀) / 3 ≤ ⟪w, y⟫}) := by
  have hcont : Continuous fun y : Space => ⟪w, y⟫ := by fun_prop
  obtain ⟨y₀, hy₀, hmin⟩ := hVc.exists_isMinOn hne hcont.continuousOn
  obtain ⟨y₁, hy₁, hmax⟩ := hVc.exists_isMaxOn hne hcont.continuousOn
  set t₀ := ⟪w, y₀⟫ with ht₀
  set t₁ := ⟪w, y₁⟫ with ht₁
  have hbounds : ∀ y ∈ V, t₀ ≤ ⟪w, y⟫ ∧ ⟪w, y⟫ ≤ t₁ := fun y hy =>
    ⟨isMinOn_iff.mp hmin y hy, isMaxOn_iff.mp hmax y hy⟩
  refine ⟨t₀, t₁, hbounds, ⟨y₀, hy₀, rfl⟩, ⟨y₁, hy₁, rfl⟩, ?_, ?_⟩
  · have hsub : AffineMap.homothety y₀ (1 / 3 : ℝ) '' V ⊆
        V ∩ {y | ⟪w, y⟫ ≤ t₀ + (t₁ - t₀) / 3} := by
      rintro _ ⟨y, hy, rfl⟩
      have hform : AffineMap.homothety y₀ (1 / 3 : ℝ) y = (2 / 3 : ℝ) • y₀ + (1 / 3 : ℝ) • y := by
        rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
        module
      rw [hform]
      refine ⟨hV hy₀ hy (by norm_num) (by norm_num) (by norm_num), ?_⟩
      simp only [mem_ofPred_eq, inner_add_right, real_inner_smul_right]
      have := (hbounds y hy).2
      linarith
    have hvol := MeasureTheory.Measure.addHaar_image_homothety (volume : Measure Space) y₀
      (1 / 3 : ℝ) V
    rw [finrank_space] at hvol
    have h27 : ENNReal.ofReal (|(1 / 3 : ℝ) ^ 3|) = (27 : ENNReal)⁻¹ := by
      rw [abs_of_pos (by norm_num), show ((1 / 3 : ℝ) ^ 3) = (27 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [h27] at hvol
    calc volume V = 27 * ((27 : ENNReal)⁻¹ * volume V) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ = 27 * volume (AffineMap.homothety y₀ (1 / 3 : ℝ) '' V) := by rw [hvol]
      _ ≤ 27 * volume (V ∩ {y | ⟪w, y⟫ ≤ t₀ + (t₁ - t₀) / 3}) := by
          gcongr
  · have hsub : AffineMap.homothety y₁ (1 / 3 : ℝ) '' V ⊆
        V ∩ {y | t₁ - (t₁ - t₀) / 3 ≤ ⟪w, y⟫} := by
      rintro _ ⟨y, hy, rfl⟩
      have hform : AffineMap.homothety y₁ (1 / 3 : ℝ) y = (2 / 3 : ℝ) • y₁ + (1 / 3 : ℝ) • y := by
        rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
        module
      rw [hform]
      refine ⟨hV hy₁ hy (by norm_num) (by norm_num) (by norm_num), ?_⟩
      simp only [mem_ofPred_eq, inner_add_right, real_inner_smul_right]
      have := (hbounds y hy).1
      linarith
    have hvol := MeasureTheory.Measure.addHaar_image_homothety (volume : Measure Space) y₁
      (1 / 3 : ℝ) V
    rw [finrank_space] at hvol
    have h27 : ENNReal.ofReal (|(1 / 3 : ℝ) ^ 3|) = (27 : ENNReal)⁻¹ := by
      rw [abs_of_pos (by norm_num), show ((1 / 3 : ℝ) ^ 3) = (27 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [h27] at hvol
    calc volume V = 27 * ((27 : ENNReal)⁻¹ * volume V) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ = 27 * volume (AffineMap.homothety y₁ (1 / 3 : ℝ) '' V) := by rw [hvol]
      _ ≤ 27 * volume (V ∩ {y | t₁ - (t₁ - t₀) / 3 ≤ ⟪w, y⟫}) := by
          gcongr

/-- **End pieces.**  A compact convex set of extent at least `e₀` along `w` has two measurable
end pieces, each carrying `1/27` of its volume, with `⟪w, q - p⟫ ≥ e₀/3` for `p` in the first
and `q` in the second. -/
theorem end_pieces {V : Set Space} (hV : Convex ℝ V) (hVc : IsCompact V) (w : Space) {e₀ : ℝ}
    (hext : ∃ y ∈ V, ∃ y' ∈ V, e₀ ≤ ⟪w, y' - y⟫) :
    ∃ E₁ E₂ : Set Space, MeasurableSet E₁ ∧ MeasurableSet E₂ ∧ E₁ ⊆ V ∧ E₂ ⊆ V ∧
      volume V ≤ 27 * volume E₁ ∧ volume V ≤ 27 * volume E₂ ∧
      ∀ p ∈ E₁, ∀ q ∈ E₂, e₀ / 3 ≤ ⟪w, q - p⟫ := by
  obtain ⟨y, hy, y', hy', hyy⟩ := hext
  obtain ⟨t₀, t₁, hb, -, -, h1, h2⟩ := end_thirds hV hVc ⟨y, hy⟩ w
  have hext' : e₀ ≤ t₁ - t₀ := by
    rw [inner_sub_right] at hyy
    linarith [(hb y hy).1, (hb y' hy').2]
  have hcont : Continuous fun y : Space => ⟪w, y⟫ := by fun_prop
  refine ⟨V ∩ {y | ⟪w, y⟫ ≤ t₀ + (t₁ - t₀) / 3}, V ∩ {y | t₁ - (t₁ - t₀) / 3 ≤ ⟪w, y⟫},
    hVc.isClosed.measurableSet.inter (isClosed_le hcont continuous_const).measurableSet,
    hVc.isClosed.measurableSet.inter (isClosed_le continuous_const hcont).measurableSet,
    inter_subset_left, inter_subset_left, h1, h2, ?_⟩
  rintro p ⟨-, hp⟩ q ⟨-, hq⟩
  simp only [mem_ofPred_eq] at hp hq
  rw [inner_sub_right]
  linarith

/-! ### Bounded multiplicity of endpoint products -/

open Classical in
/-- If every pair `(x, y)` lies in at most `M` of the products `E₁ i × E₂ i` (`i ∈ s`) of
measurable subsets of `Ω`, then `∑ |E₁ i| |E₂ i| ≤ M |Ω|²`. -/
theorem sum_mul_volume_le_of_mult {ι : Type*} (s : Finset ι) (E₁ E₂ : ι → Set Space)
    (Ω : Set Space) (M : ℕ) (hm₁ : ∀ i ∈ s, MeasurableSet (E₁ i))
    (hm₂ : ∀ i ∈ s, MeasurableSet (E₂ i)) (hΩ : MeasurableSet Ω)
    (hsub₁ : ∀ i ∈ s, E₁ i ⊆ Ω) (hsub₂ : ∀ i ∈ s, E₂ i ⊆ Ω)
    (hmult : ∀ x y : Space, (s.filter (fun i => x ∈ E₁ i ∧ y ∈ E₂ i)).card ≤ M) :
    ∑ i ∈ s, volume (E₁ i) * volume (E₂ i) ≤ (M : ENNReal) * (volume Ω * volume Ω) := by
  classical
  set μ : Measure (Space × Space) := (volume : Measure Space).prod volume with hμ
  have hmeas : ∀ i ∈ s, MeasurableSet (E₁ i ×ˢ E₂ i) := fun i hi => (hm₁ i hi).prod (hm₂ i hi)
  have h1 : ∀ i ∈ s, volume (E₁ i) * volume (E₂ i) =
      ∫⁻ z, (E₁ i ×ˢ E₂ i).indicator 1 z ∂μ := by
    intro i hi
    rw [lintegral_indicator_one (hmeas i hi), hμ, Measure.prod_prod]
  rw [Finset.sum_congr rfl h1, ← lintegral_finsetSum _
    (fun i hi => measurable_one.indicator (hmeas i hi))]
  calc ∫⁻ z, ∑ i ∈ s, (E₁ i ×ˢ E₂ i).indicator 1 z ∂μ
      ≤ ∫⁻ z, (Ω ×ˢ Ω).indicator (fun _ => (M : ENNReal)) z ∂μ := by
        apply lintegral_mono
        intro z
        dsimp only
        by_cases hz : z ∈ Ω ×ˢ Ω
        · rw [Set.indicator_of_mem hz]
          have he : ∑ i ∈ s, (E₁ i ×ˢ E₂ i).indicator (1 : Space × Space → ENNReal) z =
              ∑ i ∈ s, if z.1 ∈ E₁ i ∧ z.2 ∈ E₂ i then (1 : ENNReal) else 0 := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp only [Set.indicator_apply, Set.mem_prod, Pi.one_apply]
          rw [he, Finset.sum_boole]
          exact_mod_cast hmult z.1 z.2
        · rw [Set.indicator_of_notMem hz]
          apply le_of_eq
          refine Finset.sum_eq_zero (fun i hi => Set.indicator_of_notMem ?_ _)
          intro h
          exact hz ⟨hsub₁ i hi h.1, hsub₂ i hi h.2⟩
    _ = (M : ENNReal) * μ (Ω ×ˢ Ω) := lintegral_indicator_const (hΩ.prod hΩ) _
    _ = (M : ENNReal) * (volume Ω * volume Ω) := by rw [hμ, Measure.prod_prod]

/-! ### Packing -/

/-- Points pairwise `2r` apart within distance `R` of `p`: `#t · r³ ≤ (R + r)³`. -/
theorem card_mul_pow_le_of_packing {ι : Type*} (t : Finset ι) (y : ι → Space) (p : Space)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hsep : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → 2 * r ≤ dist (y i) (y j))
    (hnear : ∀ i ∈ t, dist (y i) p ≤ R) :
    (t.card : ℝ) * r ^ 3 ≤ (R + r) ^ 3 := by
  classical
  have hdisj : (t : Set ι).PairwiseDisjoint (fun i => ball (y i) r) := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hz1 hz2
    have h0 := hsep i hi j hj hij
    have h1 := mem_ball.mp hz1
    have h2 := mem_ball.mp hz2
    have h3 := dist_triangle_left (y i) (y j) z
    linarith
  have hsub : (⋃ i ∈ t, ball (y i) r) ⊆ ball p (R + r) := by
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨i, hi, hz⟩ := hz
    rw [mem_ball] at hz ⊢
    have h1 := dist_triangle z (y i) p
    have h2 := hnear i hi
    linarith
  have hvol := measure_mono (μ := (volume : Measure Space)) hsub
  rw [measure_biUnion_finset hdisj (fun i _ => isOpen_ball.measurableSet)] at hvol
  have hball : ∀ x : Space, ∀ s : ℝ, 0 ≤ s →
      volume (ball x s) = ENNReal.ofReal (s ^ 3) * volume (ball (0 : Space) 1) := by
    intro x s hs
    rw [Measure.addHaar_ball _ _ hs, finrank_space]
  rw [Finset.sum_congr rfl (fun i _ => hball (y i) r hr.le), Finset.sum_const, nsmul_eq_mul,
    hball p (R + r) (by linarith), ← mul_assoc] at hvol
  have hB0 : volume (ball (0 : Space) 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hBtop : volume (ball (0 : Space) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h := (ENNReal.mul_le_mul_iff_left hB0 hBtop).mp hvol
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
