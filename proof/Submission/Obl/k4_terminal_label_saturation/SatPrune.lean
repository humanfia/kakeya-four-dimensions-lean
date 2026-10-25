-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/SatPrune.lean
import Submission.Obl.k4_terminal_label_saturation.SaturationBridge
import Submission.Obl.k4_terminal_label_saturation.ChartMonotonicity

/-!
# Saturation with pruning, for one sample

After saturation, a chart whose retained selection fell below the (weakened)
true floor `N^-fL |det Q| / (2^T κ')` is discarded and the survivors are
reindexed.  Since every old selection had the floor at slack `κ₀`, the
discarded retained mass is at most `κ₀ / κ'` times the old weighted mass, which
is at most `2` (each incidence lies in at most two selections of its world).
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MeasureTheory Set MvPolynomial
open scoped ENNReal

/-- Restricting the selection of a chart to a measurable subset in format keeps
every chart condition. -/
theorem chart_restrict {Nk κ j r Bv : ℝ} {M D T : ℕ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F F' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (h : chart Nk M D κ T j r Bv Ev c u Q R A F ex) (hsub : F' ⊆ F) (hm : MeasurableSet F')
    (hfmt : ∀ i : ℕ, fmt 7 (Nk ^ M) D
      {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F'})
    (hex : ex') :
    chart Nk M D κ T j r Bv Ev c u Q R A F' ex' := by
  rcases h with ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, hA, _, hformat, hwhole, hselected, _⟩
  exact ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, hA, hm, fun i => ⟨(hformat i).1, hfmt i⟩,
    hwhole, fun p hp => hselected p (hsub hp), hex⟩

/-- The old weighted selection mass is at most two. -/
theorem weighted_selection_le_two {W C' T : ℕ} (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) [∀ γ₁, IsProbabilityMeasure (ν γ₁)]
    (hω : ∀ γ₁, 0 ≤ ω γ₁) (hω1 : ∑ γ₁, ω γ₁ = 1)
    (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T)) (A : Fin C' → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hFm : ∀ b, MeasurableSet (F b))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hF : ∀ b, ∀ p ∈ F b, p.1 ∈ A b ∧
      p.2 ∈ Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)) :
    ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b) ≤ 2 := by
  classical
  have hY : MeasurableSet (univ ×ˢ Icc (0 : ℝ) 1 : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hFY : ∀ b, F b ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    intro b p hp
    obtain ⟨_, ht⟩ := hF b p hp
    have hpos : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
    refine ⟨mem_univ _, ?_, ?_⟩
    · have := ht.1
      have h0 : 0 ≤ ((j b : ℕ) : ℝ) / (2 : ℝ) ^ T := by positivity
      linarith
    · have := ht.2
      have hj : ((j b : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
        have := (j b).isLt
        exact_mod_cast this
      have h1 : ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ≤ 1 := by
        rw [div_le_one hpos]; exact hj
      linarith
  have hfib : ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b) =
      ∑ γ₁, ∑ b : {b : Fin C' // γ b = γ₁}, ENNReal.ofReal (ω γ₁) * ((ν γ₁).prod volume) (F b) := by
    rw [← Fintype.sum_fiberwise γ (fun b => ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b))]
    apply Finset.sum_congr rfl
    intro γ₁ _
    apply Finset.sum_congr rfl
    intro b _
    rw [b.2]
  rw [hfib]
  calc ∑ γ₁, ∑ b : {b : Fin C' // γ b = γ₁}, ENNReal.ofReal (ω γ₁) * ((ν γ₁).prod volume) (F b)
      = ∑ γ₁, ENNReal.ofReal (ω γ₁) *
          ∑ b : {b : Fin C' // γ b = γ₁}, ((ν γ₁).prod volume) (F b ∩ (univ ×ˢ Icc (0 : ℝ) 1)) := by
        apply Finset.sum_congr rfl
        intro γ₁ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [inter_eq_left.mpr (hFY b)]
    _ ≤ ∑ γ₁, ENNReal.ofReal (ω γ₁) * (2 * ((ν γ₁).prod volume) (univ ×ˢ Icc (0 : ℝ) 1)) := by
        apply Finset.sum_le_sum
        intro γ₁ _
        apply mul_le_mul' le_rfl
        exact sum_measure_inter_le_two ((ν γ₁).prod volume) (fun b : {b : Fin C' // γ b = γ₁} => F b)
          (fun b => hFm b) (selection_multiplicity_le_two γ j A F hdisj hF γ₁) _ hY
    _ = ∑ γ₁, ENNReal.ofReal (ω γ₁) * 2 := by
        apply Finset.sum_congr rfl
        intro γ₁ _
        rw [Measure.prod_prod, measure_univ, Real.volume_Icc, one_mul]
        norm_num
    _ = 2 := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun γ₁ _ => hω γ₁), hω1,
          ENNReal.ofReal_one, one_mul]

/-- **Saturation with pruning for one sample.**  From one sample of a true
system at slack `κ₀` (charts with true floors, disjoint assignments, coverage
`1/κ₀`), the density map and typical cap at the terminal depth, and a numerical
budget, we obtain a reindexed subfamily of charts at slack `κ'` whose selections
are the saturated ones, with the true floor at slack `κ'`, knowledge through
lists of size at most `H ≤ κ'`, coverage `1/κ'`, and fixed-format list
membership. -/
theorem saturate_prune_sample {W C' T M D M' D' : ℕ} (Nk L : ℝ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) [∀ γ₁, IsProbabilityMeasure (ν γ₁)]
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (B : Fin W → ℝ) (g : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ≥0∞) {κ₀ κ' n₀ cap H : ℝ}
    (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (A : Fin C' → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hNk : 1 ≤ Nk) (hω : ∀ γ₁, 0 ≤ ω γ₁) (hω1 : ∑ γ₁, ω γ₁ = 1)
    (hB : ∀ γ₁, 0 < B γ₁) (hκ₀ : 1 ≤ κ₀) (hκ' : κ₀ ≤ κ') (hn₀ : 0 < n₀) (hcap : 0 ≤ cap)
    (hH : 0 < H) (hHκ : H ≤ κ') (hgm : ∀ γ₁, Measurable (g γ₁))
    (hmap : ∀ γ₁, Measure.map (obs (B γ₁) (δ Nk L)) (((ν γ₁).prod volume).restrict (E γ₁)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity (g γ₁))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hchart : ∀ b, chart Nk M D κ₀ T ((j b : ℕ) : ℝ) L (B (γ b)) (E (γ b)) (c b) (u b) (Q b)
      (R b) (A b) (F b)
      (ENNReal.ofReal (n₀ * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ₀)) ≤
        ((ν (γ b)).prod volume) (F b)))
    (hcov : ENNReal.ofReal κ₀⁻¹ ≤ ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b))
    (θ : ℝ≥0∞) (hθ : θ ≠ ⊤)
    (htyp : ∑ γ₁, ENNReal.ofReal (ω γ₁) * (((ν γ₁).prod volume).restrict (E γ₁))
      {p | ENNReal.ofReal cap < g γ₁ (obs (B γ₁) (δ Nk L) p)} ≤ θ)
    (hM' : M ≤ M') (hD' : max D 4 ≤ D')
    (hbudget : ∀ γ₀ : Fin W, Nk ^ M + (2 + ((binCount (2 * Nk ^ M) (B γ₀) (δ Nk L) + 1) +
      binCount (2 * Nk ^ M) (B γ₀) (δ Nk L) * (C' * 6))) ≤ Nk ^ M')
    (hnum : ENNReal.ofReal κ'⁻¹ +
      (2 * θ + 2 * ENNReal.ofReal (cap * (Real.pi * κ₀ ^ 3 * (14 + 48 * κ₀ ^ 2)) / (n₀ * H)) * 2 +
        ENNReal.ofReal (κ₀ / κ') * 2) ≤ ENNReal.ofReal κ₀⁻¹) :
    ∃ (C'' : ℕ) (e : Fin C'' → Fin C') (lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) →
        Finset (Fin C'')),
      C'' ≤ C' ∧ Function.Injective e ∧
      (∀ i, chart Nk M' D' κ' T ((j (e i) : ℕ) : ℝ) L (B (γ (e i))) (E (γ (e i))) (c (e i))
        (u (e i)) (Q (e i)) (R (e i)) (A (e i))
        (satSel γ j κ₀ (δ Nk L) B c u Q R H F (e i)) True) ∧
      (∀ i, ENNReal.ofReal (n₀ * |Matrix.det (Q (e i))| / ((2 : ℝ) ^ T * κ')) ≤
        ((ν (γ (e i))).prod volume) (satSel γ j κ₀ (δ Nk L) B c u Q R H F (e i))) ∧
      (∀ i, ∀ p ∈ satSel γ j κ₀ (δ Nk L) B c u Q R H F (e i),
        i ∈ lst (γ (e i)) (obs (B (γ (e i))) (δ Nk L) p)) ∧
      ENNReal.ofReal κ'⁻¹ ≤ ∑ i, ENNReal.ofReal (ω (γ (e i))) *
        ((ν (γ (e i))).prod volume) (satSel γ j κ₀ (δ Nk L) B c u Q R H F (e i)) ∧
      (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ') ∧
      (∀ γ₀ i, MeasurableSet {p | i ∈ lst γ₀ (obs (B γ₀) (δ Nk L) p)} ∧
        ∀ i' : ℕ, fmt 7 ((binCount (2 * Nk ^ M) (B γ₀) (δ Nk L) + 1) +
          binCount (2 * Nk ^ M) (B γ₀) (δ Nk L) * (C' * 6)) 4
          {r : Fin 7 → ℝ | i ∈ lst γ₀ (obs (B γ₀) (δ Nk L)
            ((i', fun z : Fin 6 => r z.castSucc), r 6))}) ∧
      (∀ i (i' : ℕ), fmt 7 (Nk ^ M + (2 + ((binCount (2 * Nk ^ M) (B (γ (e i))) (δ Nk L) + 1) +
          binCount (2 * Nk ^ M) (B (γ (e i))) (δ Nk L) * (C' * 6)))) (max D 4)
        {z : Fin 7 → ℝ | ((i', fun e' : Fin 6 => z e'.castSucc), z 6) ∈
          satSel γ j κ₀ (δ Nk L) B c u Q R H F (e i)}) := by
  classical
  have hκ₀pos : 0 < κ₀ := lt_of_lt_of_le one_pos hκ₀
  have hκ'pos : 0 < κ' := lt_of_lt_of_le hκ₀pos hκ'
  obtain ⟨hknow, hcard, hsub, hmeas, hmass, hfmtS, hfmtL, hmeasL⟩ :=
    saturation_of_charts Nk L ω ν E B g γ j c u Q R A F hNk hB hκ₀ hn₀ hcap hH hgm hmap hdisj
      hchart θ htyp
  set S := satSel γ j κ₀ (δ Nk L) B c u Q R H F with hS
  set m : Fin C' → ℝ≥0∞ := fun b => ((ν (γ b)).prod volume) (F b) with hmdef
  set m' : Fin C' → ℝ≥0∞ := fun b => ((ν (γ b)).prod volume) (S b) with hm'def
  set fl : Fin C' → ℝ≥0∞ := fun b =>
    ENNReal.ofReal (n₀ * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ')) with hfl
  -- kept charts
  set keep : Fin C' → Prop := fun b => fl b ≤ m' b with hkeep
  set C'' := Fintype.card {b : Fin C' // keep b} with hC''
  let eq : Fin C'' ≃ {b : Fin C' // keep b} := (Fintype.equivFin _).symm
  let e : Fin C'' → Fin C' := fun i => (eq i : Fin C')
  have he : Function.Injective e := fun i i' h => eq.injective (Subtype.ext h)
  have hkept : ∀ i, keep (e i) := fun i => (eq i).2
  refine ⟨C'', e, fun γ₀ o => Finset.univ.filter (fun i => e i ∈ satListR γ j κ₀ (δ Nk L) B c u
    Q R H (2 * Nk ^ M) γ₀ o), ?_, he, ?_, fun i => hkept i, ?_, ?_, ?_, ?_, ?_⟩
  · -- card
    simpa [hC''] using Fintype.card_subtype_le keep
  · -- charts
    intro i
    have hc := hchart (e i)
    have hc' := chart_mono hNk hM' ((le_max_left D 4).trans hD') hκ₀pos hκ' (hB _).le hc
      (ex' := True) (fun _ => trivial)
    exact chart_restrict hc' (hsub (e i)) (hmeas (e i))
      (fun i' => Submission.Lib.K4RepresentativeAssembly.fmt_mono (hfmtS (e i) i') (hbudget _) hD') trivial
  · -- knowledge
    intro i p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hknow (e i) p hp
  · -- coverage
    set K' : ℝ≥0∞ := ENNReal.ofReal (cap * (Real.pi * κ₀ ^ 3 * (14 + 48 * κ₀ ^ 2)) / (n₀ * H))
      with hK'
    set X := ∑ b, ENNReal.ofReal (ω (γ b)) * m b with hX
    have hX2 : X ≤ 2 := by
      have hF : ∀ b, ∀ p ∈ F b, p.1 ∈ A b ∧
          p.2 ∈ Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) :=
        fun b p hp => ⟨((hchart b).2.2.2.2.2.2.2.2.2.2.1 p hp).2.1,
          ((hchart b).2.2.2.2.2.2.2.2.2.2.1 p hp).2.2.1⟩
      exact weighted_selection_le_two ω ν hω hω1 γ j A F (fun b => (hchart b).2.2.2.2.2.2.2.1)
        hdisj hF
    -- the discarded charts
    have hdisc : ∀ b, ¬ keep b → m' b ≤ ENNReal.ofReal (κ₀ / κ') * m b := by
      intro b hb
      simp only [hkeep, not_le] at hb
      refine hb.le.trans ?_
      have hfloor := (hchart b).2.2.2.2.2.2.2.2.2.2.2
      calc fl b = ENNReal.ofReal (κ₀ / κ') *
            ENNReal.ofReal (n₀ * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ₀)) := by
            rw [hfl, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp
        _ ≤ ENNReal.ofReal (κ₀ / κ') * m b := mul_le_mul' le_rfl hfloor
    have hsplit : ∑ b, ENNReal.ofReal (ω (γ b)) * m' b =
        ∑ i, ENNReal.ofReal (ω (γ (e i))) * m' (e i) +
          ∑ b ∈ Finset.univ.filter (fun b => ¬ keep b), ENNReal.ofReal (ω (γ b)) * m' b := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ keep]
      congr 1
      rw [Finset.sum_subtype (Finset.univ.filter keep) (p := keep) (by simp)]
      exact (Equiv.sum_comp eq (fun b : {b : Fin C' // keep b} =>
        ENNReal.ofReal (ω (γ b)) * m' b)).symm
    have hdsum : ∑ b ∈ Finset.univ.filter (fun b => ¬ keep b), ENNReal.ofReal (ω (γ b)) * m' b ≤
        ENNReal.ofReal (κ₀ / κ') * 2 := by
      calc ∑ b ∈ Finset.univ.filter (fun b => ¬ keep b), ENNReal.ofReal (ω (γ b)) * m' b
          ≤ ∑ b ∈ Finset.univ.filter (fun b => ¬ keep b),
              ENNReal.ofReal (ω (γ b)) * (ENNReal.ofReal (κ₀ / κ') * m b) := by
            apply Finset.sum_le_sum
            intro b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
            exact mul_le_mul' le_rfl (hdisc b hb)
        _ ≤ ∑ b, ENNReal.ofReal (ω (γ b)) * (ENNReal.ofReal (κ₀ / κ') * m b) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = ENNReal.ofReal (κ₀ / κ') * X := by
            rw [hX, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
        _ ≤ ENNReal.ofReal (κ₀ / κ') * 2 := mul_le_mul' le_rfl hX2
    set kept := ∑ i, ENNReal.ofReal (ω (γ (e i))) * m' (e i) with hkeptdef
    set rest := 2 * θ + 2 * K' * 2 + ENNReal.ofReal (κ₀ / κ') * 2 with hrest
    have hrest_ne : rest ≠ ⊤ := by
      simp only [hrest]
      refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩
      · exact ENNReal.mul_ne_top (by norm_num) hθ
      · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
          (by norm_num)
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
    have hchain : ENNReal.ofReal κ'⁻¹ + rest ≤ kept + rest := by
      calc ENNReal.ofReal κ'⁻¹ + rest ≤ ENNReal.ofReal κ₀⁻¹ := hnum
        _ ≤ X := hcov
        _ ≤ ∑ b, ENNReal.ofReal (ω (γ b)) * m' b + 2 * θ + 2 * K' * X := hmass
        _ ≤ (kept + ENNReal.ofReal (κ₀ / κ') * 2) + 2 * θ + 2 * K' * 2 := by
            rw [hsplit]
            gcongr
        _ = kept + rest := by rw [hrest]; ring
    exact (ENNReal.add_le_add_iff_right hrest_ne).mp hchain
  · -- list size
    intro γ₀ o
    calc ((Finset.univ.filter (fun i => e i ∈ satListR γ j κ₀ (δ Nk L) B c u Q R H
          (2 * Nk ^ M) γ₀ o)).card : ℝ)
        ≤ ((satListR γ j κ₀ (δ Nk L) B c u Q R H (2 * Nk ^ M) γ₀ o).card : ℝ) := by
          have : (Finset.univ.filter (fun i => e i ∈ satListR γ j κ₀ (δ Nk L) B c u Q R H
              (2 * Nk ^ M) γ₀ o)).card ≤ (satListR γ j κ₀ (δ Nk L) B c u Q R H
              (2 * Nk ^ M) γ₀ o).card := by
            refine Finset.card_le_card_of_injOn e ?_ (he.injOn)
            intro i hi
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hi
            exact hi
          exact_mod_cast this
      _ ≤ H := hcard γ₀ o
      _ ≤ κ' := hHκ
  · -- list membership
    intro γ₀ i
    refine ⟨?_, fun i' => ?_⟩
    · have := hmeasL γ₀ (e i)
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using this
    · have := hfmtL γ₀ (e i) i'
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using this
  · intro i i'
    exact hfmtS (e i) i'

end Submission.Obl.k4_terminal_label_saturation
