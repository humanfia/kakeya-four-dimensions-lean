/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, CoefficientSample.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupInputs
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupClustering
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.CoefficientSubbinLists
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.CountingLosses

/-! The horizontal coefficient count at one sample: typical groups, scalar
clustering in each, and subbin lists, with explicit deletion costs. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_coefficient_clustering

theorem abs_sub_lt_of_floor_div_eq {x y δ : ℝ} (hδ : 0 < δ) (h : ⌊x / δ⌋ = ⌊y / δ⌋) :
    |x - y| < δ := by
  have hh := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at hh
  exact hh

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

theorem coefficient_lists_at_sample (k : ℕ) {s ε' ε₁ ηc θ₂ : ℝ}
    (hb : Measurable (cfg.b k)) (hBm : ∀ i, MeasurableSet (cfg.B k s i))
    [IsProbabilityMeasure (cfg.ν k)] [IsProbabilityMeasure (cfg.π k)]
    [IsFiniteMeasure (cfg.ρ k)]
    (hρμ : cfg.ρ k ≤ cfg.μ k)
    (hdom : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod volume))
    (hK : 1 ≤ cfg.K k) (hN : 1 < cfg.N k) (hs : 0 < s) (hd : 0 ≤ cfg.d) (hd1 : cfg.d < 1)
    (hθ₂ : 0 ≤ θ₂) (hε' : 0 ≤ ε')
    (hB : cfg.BandCapAt k s ε₁) (hS : cfg.SupportAt k s ε₁)
    (hcl : ∀ (ν' : Measure α) (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
        (a : α → EuclideanSpace ℝ (Fin 3)) (D : Set (α × ℝ)) (F : Finset (ℤ × ℤ)),
        Measurable a → MeasurableSet D → D ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → μ Dᶜ = 0 →
        μ ≤ ENNReal.ofReal (cfg.N k ^ ηc) • (ν'.prod volume) →
        (∀ l, ‖a l‖ ≤ cfg.N k ^ ηc) → ν' Set.univ ≤ ENNReal.ofReal (cfg.N k ^ ηc) →
        (F.card : ℝ) ≤ cfg.N k ^ ηc * (cfg.N k ^ (-s)) ^ (-1 - cfg.d) →
        (∀ l t, (l, t) ∈ D →
          (⌊t / (cfg.N k ^ (-s))⌋, ⌊quadratic (a l) t / (cfg.N k ^ (-s))⌋) ∈ F) →
        (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), cfg.N k ^ (-s) ≤ r →
          (∃ l, a l ∈ Metric.ball b r) →
          μ {p | |quadratic (a p.1) p.2 - quadratic b p.2| ≤ 3 * r} ≤
            ENNReal.ofReal (cfg.N k ^ ηc * r ^ cfg.d)) →
        ∃ G : Finset (Fin 3 → ℤ),
          (∀ q ∈ G, ENNReal.ofReal (cfg.N k ^ (-s * cfg.d - ε')) ≤
            μ {p | coefficientCode (cfg.N k ^ (-s)) (a p.1) = q}) ∧
          (G.card : ℝ) ≤ μ.real Set.univ / cfg.N k ^ (-s * cfg.d - ε') ∧
          μ {p | coefficientCode (cfg.N k ^ (-s)) (a p.1) ∉ G} <
            ENNReal.ofReal (cfg.N k ^ (-ηc)))
    (ha411 : cfg.N k ^ (-s) ≤ 4 / 11)
    (hηt : 9 * cfg.K k * cfg.N k ^ (-(2 * s)) ≤ cfg.N k ^ (-s))
    (hm4 : cfg.N k ^ (-(4 * s)) ≤ cfg.N k ^ (-(2 * s)))
    (hnorm : 3 * cfg.K k ≤ cfg.N k ^ ηc)
    (hc1 : 12 * cfg.K k * cfg.N k ^ ε₁ ≤ cfg.N k ^ ηc)
    (hc2 : 8 * cfg.N k ^ ε₁ ≤ cfg.N k ^ ηc)
    (hρtot : cfg.ρ k (cfg.goodSet k s) ≤ ENNReal.ofReal (cfg.K k)) :
    ∃ (G : Set (α × ℝ)) (CL : ℤ × ℤ × ℤ → ℤ → ℤ → Finset (Fin 3 → ℤ)),
      MeasurableSet G ∧ G ⊆ cfg.goodSet k s ∧
      cfg.ρ k (cfg.goodSet k s \ G) ≤ ENNReal.ofReal
        (12 * cfg.K k * cfg.N k ^ ε₁ / cfg.N k ^ ηc +
          25 * cfg.K k ^ 2 * cfg.N k ^ (-ηc) + 2 * cfg.K k * cfg.N k ^ (-θ₂)) ∧
      (∀ g τ j, ((CL g τ j).card : ℝ) ≤ 22 * cfg.N k ^ (ε₁ + ε' + θ₂)) ∧
      ∀ p ∈ G, coefficientCode (cfg.N k ^ (-s)) (cfg.hiddenCoeff k p.1) ∈
        CL (cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1)
          ⌊p.2 / cfg.N k ^ (-(2 * s))⌋ ⌊cfg.hidden k p / cfg.N k ^ (-s)⌋ := by
  classical
  -- abbreviations
  have hNpos : 0 < cfg.N k := by linarith
  set a := cfg.N k ^ (-s) with hadef
  set δ := cfg.N k ^ (-(2 * s)) with hδdef
  have ha : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hδ : 0 < δ := Real.rpow_pos_of_pos hNpos _
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hm4' : cfg.N k ^ (-(4 * s)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)
  set grp := cfg.groupCode k a δ with hgrpdef
  set W := cfg.groupWeight k a δ with hWdef
  set Γ := groupBox (cfg.K k) a δ with hΓdef
  have hWnn : ∀ g, 0 ≤ W g := fun g => cfg.groupWeight_nonneg k a δ g
  let X : ℤ × ℤ × ℤ → Set α := fun g => {l | grp l = g}
  have hXm : ∀ g, MeasurableSet (X g) := fun g =>
    (cfg.measurable_groupCode k hb a δ) (measurableSet_singleton g)
  let D : ℤ × ℤ × ℤ → Set (α × ℝ) := cfg.groupSet k s
  have hDm : ∀ g, MeasurableSet (D g) := cfg.measurableSet_groupSet k s hb hBm
  let cc : α × ℝ → Fin 3 → ℤ := fun p => coefficientCode a (cfg.hiddenCoeff k p.1)
  have hccm : Measurable cc :=
    ((measurable_coefficientCode a).comp (cfg.measurable_hiddenCoeff k hb)).comp measurable_fst
  let sub : α × ℝ → ℤ := fun p => ⌊p.2 / δ⌋
  have hsubm : Measurable sub := Int.measurable_floor.comp (measurable_snd.div_const δ)
  have hgrpm : Measurable (fun p : α × ℝ => grp p.1) :=
    (cfg.measurable_groupCode k hb a δ).comp measurable_fst
  have hclamp_eq : ∀ p ∈ cfg.goodSet k s,
      coefficientCode a (cfg.clampedCoeff k p.1) = cc p := by
    intro p hp
    simp only [cc, cfg.clampedCoeff_of_good hp]
  -- typical groups
  let Typ : Finset (ℤ × ℤ × ℤ) :=
    Γ.filter (fun g => 0 < W g ∧ (cfg.ν k).real (X g) ≤ cfg.N k ^ ηc * W g)
  have hHC : ∀ g ∈ Typ, ∃ HC : Finset (Fin 3 → ℤ),
      (∀ q ∈ HC, ENNReal.ofReal (W g * cfg.N k ^ (-s * cfg.d - ε')) ≤
        cfg.ρ k (D g ∩ {p | coefficientCode a (cfg.clampedCoeff k p.1) = q})) ∧
      (HC.card : ℝ) ≤ (cfg.ρ k).real (D g) / (W g * cfg.N k ^ (-s * cfg.d - ε')) ∧
      cfg.ρ k (D g ∩ {p | coefficientCode a (cfg.clampedCoeff k p.1) ∉ HC}) ≤
        ENNReal.ofReal (W g * cfg.N k ^ (-ηc)) := by
    intro g hg
    obtain ⟨_, hWg, hνg⟩ := Finset.mem_filter.mp hg
    obtain ⟨F, hF, hFsupp⟩ := cfg.group_support_finset k hN hs hS g
    have hdomg := cfg.group_domination k s hb hBm hρμ hdom g
    apply group_heavy_cover_original (cfg.ν k) (cfg.ρ k) cfg.d s ε' (cfg.N k) ηc (W g) hWg hNpos
      hcl (X g) (hXm g) (D g) (hDm g) (cfg.groupSet_unit k s g) (cfg.clampedCoeff k)
      (cfg.measurable_clampedCoeff k hb)
      (fun l => (cfg.norm_clampedCoeff_le k hK0 l).trans hnorm)
    · refine hdomg.trans ?_
      intro U
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr
      exact hnorm.trans' (by linarith)
    · rw [← ENNReal.ofReal_toReal (measure_ne_top (cfg.ν k) (X g))]
      exact ENNReal.ofReal_le_ofReal hνg
    · exact hF.trans (by gcongr; linarith [hc2, Real.rpow_nonneg hNpos.le ε₁])
    · exact hFsupp
    · intro b r hr hex
      exact cfg.group_clustering_band k hs hρμ hK hN hd hd1 hB hm4' hc1 hc2 g b r hr hex
  choose! HC hHCfloor hHCcard hHCexcl using hHC
  -- subbin floors
  let φ : ℤ × ℤ × ℤ → ℝ := fun g => δ * (W g * a ^ cfg.d * cfg.N k ^ (-ε' - θ₂))
  have hφnn : ∀ g, 0 ≤ φ g := fun g => by
    have := hWnn g
    positivity
  let cell : ℤ × ℤ × ℤ → (Fin 3 → ℤ) → ℤ → Set (α × ℝ) := fun g q θ =>
    D g ∩ {p | cc p = q} ∩ {p | sub p = θ}
  have hcellm : ∀ g q θ, MeasurableSet (cell g q θ) := fun g q θ =>
    ((hDm g).inter (hccm (measurableSet_singleton q))).inter (hsubm (measurableSet_singleton θ))
  let kept : ℤ × ℤ × ℤ → (Fin 3 → ℤ) → ℤ → Prop := fun g q θ =>
    ENNReal.ofReal (φ g) ≤ cfg.ρ k (cell g q θ)
  let G : Set (α × ℝ) := {p | p ∈ cfg.goodSet k s ∧ grp p.1 ∈ Typ ∧ cc p ∈ HC (grp p.1) ∧
    kept (grp p.1) (cc p) (sub p)}
  let CL : ℤ × ℤ × ℤ → ℤ → ℤ → Finset (Fin 3 → ℤ) := fun g θ j =>
    if g ∈ Typ then (HC g).filter (fun q => kept g q θ ∧
      ∃ p ∈ D g, cc p = q ∧ sub p = θ ∧ ⌊cfg.hidden k p / a⌋ = j) else ∅
  refine ⟨G, CL, ?_, fun p hp => hp.1, ?_, ?_, ?_⟩
  · -- measurability
    let Z : Set ((ℤ × ℤ × ℤ) × (Fin 3 → ℤ) × ℤ) :=
      {z | z.1 ∈ Typ ∧ z.2.1 ∈ HC z.1 ∧ kept z.1 z.2.1 z.2.2}
    have hZ : MeasurableSet Z := (Set.to_countable Z).measurableSet
    have hf : Measurable (fun p : α × ℝ => (grp p.1, cc p, sub p)) :=
      hgrpm.prodMk (hccm.prodMk hsubm)
    have : G = cfg.goodSet k s ∩ (fun p : α × ℝ => (grp p.1, cc p, sub p)) ⁻¹' Z := by
      ext p; simp only [G, Z, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    rw [this]
    exact (cfg.measurableSet_goodSet k hb s hBm).inter (hf hZ)
  · -- deletion cost
    let Θ : Finset ℤ := Finset.Icc 0 ⌊1 / δ⌋
    let A1 : Set (α × ℝ) := ⋃ g ∈ Γ.filter (fun g => g ∉ Typ), D g
    let A2 : Set (α × ℝ) := ⋃ g ∈ Typ,
      (D g ∩ {p | coefficientCode a (cfg.clampedCoeff k p.1) ∉ HC g})
    let A3 : Set (α × ℝ) := ⋃ g ∈ Typ, ⋃ q ∈ HC g,
      ⋃ θ ∈ Θ.filter (fun θ => cfg.ρ k (cell g q θ) < ENNReal.ofReal (φ g)), cell g q θ
    have hcover : cfg.goodSet k s \ G ⊆ A1 ∪ A2 ∪ A3 := by
      rintro p ⟨hgood, hnG⟩
      have hΓ : grp p.1 ∈ Γ := cfg.groupCode_mem_groupBox ha hδ hgood
      have hpD : p ∈ D (grp p.1) := ⟨hgood, rfl⟩
      by_cases hT : grp p.1 ∈ Typ
      swap
      · exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨grp p.1, Finset.mem_filter.mpr ⟨hΓ, hT⟩, hpD⟩))
      by_cases hH : cc p ∈ HC (grp p.1)
      swap
      · refine Or.inl (Or.inr (mem_iUnion₂.mpr ⟨grp p.1, hT, hpD, ?_⟩))
        change coefficientCode a (cfg.clampedCoeff k p.1) ∉ HC (grp p.1)
        rw [hclamp_eq p hgood]
        exact hH
      · have hnk : ¬ kept (grp p.1) (cc p) (sub p) := fun hk => hnG ⟨hgood, hT, hH, hk⟩
        have hθΘ : sub p ∈ Θ := by
          have ht := hgood.1
          exact Finset.mem_Icc.mpr ⟨Int.floor_nonneg.mpr (div_nonneg ht.1 hδ.le),
            Int.floor_mono (div_le_div_of_nonneg_right ht.2 hδ.le)⟩
        refine Or.inr (mem_iUnion₂.mpr ⟨grp p.1, hT, mem_iUnion₂.mpr ⟨cc p, hH,
          mem_iUnion₂.mpr ⟨sub p, Finset.mem_filter.mpr ⟨hθΘ, lt_of_not_ge hnk⟩, ?_⟩⟩⟩)
        exact ⟨⟨hpD, rfl⟩, rfl⟩
    have hA1 : cfg.ρ k A1 ≤ ENNReal.ofReal (12 * cfg.K k * cfg.N k ^ ε₁ / cfg.N k ^ ηc) := by
      apply atypical_group_loss (cfg.ν k) (cfg.ρ k) (Γ.filter (fun g => g ∉ Typ)) X D W
        (12 * cfg.K k * cfg.N k ^ ε₁) (cfg.N k ^ ηc) (fun g _ => hXm g)
      · intro g _ g' _ hgg'
        exact Set.disjoint_left.mpr (fun l hl hl' => hgg' (hl.symm.trans hl'))
      · have : 0 ≤ cfg.N k ^ ε₁ := Real.rpow_nonneg hNpos.le _
        positivity
      · exact Real.rpow_pos_of_pos hNpos _
      · exact hWnn
      · intro g _
        exact cfg.group_total_mass k hs hρμ hK hN hB hm4' g
      · intro g hg
        have hnT := (Finset.mem_filter.mp hg).2
        by_cases hW0 : W g ≤ 0
        · exact Or.inl (le_antisymm hW0 (hWnn g))
        · right
          by_contra hle
          exact hnT (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1, lt_of_not_ge hW0,
            le_of_not_gt hle⟩)
    have hA2 : cfg.ρ k A2 ≤ ENNReal.ofReal (25 * cfg.K k ^ 2 * cfg.N k ^ (-ηc)) := by
      calc
        cfg.ρ k A2 ≤ ∑ g ∈ Typ, cfg.ρ k
            (D g ∩ {p | coefficientCode a (cfg.clampedCoeff k p.1) ∉ HC g}) :=
          measure_biUnion_finset_le _ _
        _ ≤ ∑ g ∈ Typ, ENNReal.ofReal (W g * cfg.N k ^ (-ηc)) :=
          Finset.sum_le_sum (fun g hg => hHCexcl g hg)
        _ = ENNReal.ofReal ((∑ g ∈ Typ, W g) * cfg.N k ^ (-ηc)) := by
          rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun g _ => by
            have := hWnn g; have := Real.rpow_nonneg hNpos.le (-ηc); positivity)]
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNpos.le _)
          calc
            ∑ g ∈ Typ, W g ≤ ∑ g ∈ Γ, W g :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun g _ _ => hWnn g)
            _ ≤ 25 * cfg.K k ^ 2 :=
              cfg.groupBox_weight_sum k ha (by linarith) hδ hK
    have hA3 : cfg.ρ k A3 ≤ ENNReal.ofReal (2 * cfg.K k * cfg.N k ^ (-θ₂)) := by
      refine (light_entry_loss (cfg.ρ k) Typ HC Θ cell φ hφnn).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hΘ : (Θ.card : ℝ) ≤ 2 / δ := by
        have hfl : (0 : ℤ) ≤ ⌊1 / δ⌋ := Int.floor_nonneg.mpr (by positivity)
        have hc : (Θ.card : ℝ) = (⌊1 / δ⌋ : ℝ) + 1 := by
          simp only [Θ, Int.card_Icc, sub_zero]
          have hnat : (((⌊1 / δ⌋ + 1).toNat : ℕ) : ℤ) = ⌊1 / δ⌋ + 1 := by
            rw [Int.toNat_of_nonneg (by omega)]
          exact_mod_cast hnat
        rw [hc]
        have := Int.floor_le (1 / δ)
        have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)
        have h1δ : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
        have h2δ : 2 / δ = 1 / δ + 1 / δ := by ring
        linarith
      have had : 0 < a ^ cfg.d := Real.rpow_pos_of_pos ha _
      have hpow : cfg.N k ^ (-s * cfg.d - ε') = a ^ cfg.d * cfg.N k ^ (-ε') := by
        rw [hadef, ← Real.rpow_mul hNpos.le, sub_eq_add_neg, Real.rpow_add hNpos]
      have hterm : ∀ g ∈ Typ, ((HC g).card : ℝ) * (Θ.card : ℝ) * φ g ≤
          2 * cfg.N k ^ (-θ₂) * (cfg.ρ k).real (D g) := by
        intro g hg
        have hWg := (Finset.mem_filter.mp hg).2.1
        have hc := hHCcard g hg
        rw [hpow] at hc
        have hN' : 0 < cfg.N k ^ (-ε') := Real.rpow_pos_of_pos hNpos _
        have hden : 0 < W g * (a ^ cfg.d * cfg.N k ^ (-ε')) := by positivity
        calc
          ((HC g).card : ℝ) * (Θ.card : ℝ) * φ g ≤
              ((cfg.ρ k).real (D g) / (W g * (a ^ cfg.d * cfg.N k ^ (-ε')))) * (2 / δ) * φ g := by
            gcongr
          _ = 2 * ((cfg.N k ^ (-ε' - θ₂)) / cfg.N k ^ (-ε')) * (cfg.ρ k).real (D g) := by
            simp only [φ]
            field_simp
          _ = 2 * cfg.N k ^ (-θ₂) * (cfg.ρ k).real (D g) := by
            rw [sub_eq_add_neg, Real.rpow_add hNpos]
            field_simp
      have hdisj : (↑Typ : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint D := by
        intro g _ g' _ hgg'
        exact Set.disjoint_left.mpr (fun p hp hp' => hgg' (hp.2.symm.trans hp'.2))
      have hsumD : ∑ g ∈ Typ, (cfg.ρ k).real (D g) ≤ cfg.K k := by
        rw [← measureReal_biUnion_finset hdisj (fun g _ => hDm g)]
        have hsub : (⋃ g ∈ Typ, D g) ⊆ cfg.goodSet k s :=
          iUnion₂_subset (fun g _ => cfg.groupSet_subset_good k s g)
        refine (measureReal_mono hsub).trans ?_
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hρtot
        rwa [ENNReal.toReal_ofReal hK0] at this
      calc
        ∑ g ∈ Typ, ((HC g).card : ℝ) * (Θ.card : ℝ) * φ g ≤
            ∑ g ∈ Typ, 2 * cfg.N k ^ (-θ₂) * (cfg.ρ k).real (D g) := Finset.sum_le_sum hterm
        _ = 2 * cfg.N k ^ (-θ₂) * ∑ g ∈ Typ, (cfg.ρ k).real (D g) := by rw [Finset.mul_sum]
        _ ≤ 2 * cfg.N k ^ (-θ₂) * cfg.K k := by
          gcongr
        _ = 2 * cfg.K k * cfg.N k ^ (-θ₂) := by ring
    calc
      cfg.ρ k (cfg.goodSet k s \ G) ≤ cfg.ρ k (A1 ∪ A2 ∪ A3) := measure_mono hcover
      _ ≤ cfg.ρ k A1 + cfg.ρ k A2 + cfg.ρ k A3 :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (12 * cfg.K k * cfg.N k ^ ε₁ / cfg.N k ^ ηc) +
          ENNReal.ofReal (25 * cfg.K k ^ 2 * cfg.N k ^ (-ηc)) +
          ENNReal.ofReal (2 * cfg.K k * cfg.N k ^ (-θ₂)) := add_le_add (add_le_add hA1 hA2) hA3
      _ = _ := by
        have h1 : 0 ≤ 12 * cfg.K k * cfg.N k ^ ε₁ / cfg.N k ^ ηc := by
          have := Real.rpow_nonneg hNpos.le ε₁; have := Real.rpow_nonneg hNpos.le ηc; positivity
        have h2 : 0 ≤ 25 * cfg.K k ^ 2 * cfg.N k ^ (-ηc) := by
          have := Real.rpow_nonneg hNpos.le (-ηc); positivity
        have h3 : 0 ≤ 2 * cfg.K k * cfg.N k ^ (-θ₂) := by
          have := Real.rpow_nonneg hNpos.le (-θ₂); positivity
        rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) h3]
  · -- list sizes
    intro g θ j
    by_cases hg : g ∈ Typ
    swap
    · simp only [CL, hg, ite_eq_right_iff, not_false_eq_true, if_neg, Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨_, hWg, _⟩ := Finset.mem_filter.mp hg
    simp only [CL, hg, ite_true]
    set S := (HC g).filter (fun q => kept g q θ ∧
      ∃ p ∈ D g, cc p = q ∧ sub p = θ ∧ ⌊cfg.hidden k p / a⌋ = j) with hSdef
    have hDθ : MeasurableSet (D g ∩ {p | sub p = θ}) :=
      (hDm g).inter (hsubm (measurableSet_singleton θ))
    have hφpos : 0 < φ g := by
      simp only [φ]
      have : 0 < a ^ cfg.d := Real.rpow_pos_of_pos ha _
      have : 0 < cfg.N k ^ (-ε' - θ₂) := Real.rpow_pos_of_pos hNpos _
      positivity
    have hcellsub : ∀ q, cell g q θ ⊆ D g ∩ {p | sub p = θ} := fun q p hp => ⟨hp.1.1, hp.2⟩
    have hcard := coefficient_subbin_list_card ((cfg.ρ k).restrict (D g ∩ {p | sub p = θ})) S
      (fun q => cell g q θ) (fun e : α × ℝ => cfg.hiddenCoeff k e.1) Prod.snd a (3 * cfg.K k) δ
      (φ g) (22 * cfg.N k ^ ε₁ * δ * W g * a ^ cfg.d) j ha hφpos
      (fun q _ => hcellm g q θ)
      (fun q _ e he => he.1.2)
      (fun q _ e he => by
        have hgood := he.1.1.1
        rw [← cfg.clampedCoeff_of_good hgood]
        exact cfg.norm_clampedCoeff_le k hK0 e.1)
      (fun q _ e he => he.1.1.1.1)
      (fun q _ e he e' he' => (abs_sub_lt_of_floor_div_eq hδ (he.2.trans he'.2.symm)).le)
      (fun q hq => by
        have hk := (Finset.mem_filter.mp hq).2.1
        have hfin : cfg.ρ k (cell g q θ) ≠ ∞ := measure_ne_top _ _
        rw [measureReal_restrict_apply' hDθ, Set.inter_eq_left.mpr (hcellsub q)]
        exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hk)
      (fun q hq => by
        obtain ⟨p, hpD, hpq, hpθ, hpj⟩ := (Finset.mem_filter.mp hq).2.2
        refine ⟨p, ⟨⟨hpD, hpq⟩, hpθ⟩, ?_⟩
        rw [cfg.quadratic_hiddenCoeff k p]
        exact hpj)
      (by
        rw [measureReal_def, Measure.restrict_apply' hDθ]
        have hsub2 : {e : α × ℝ | |quadratic (cfg.hiddenCoeff k e.1) e.2 - a * (j : ℝ)| ≤
            10 * a + 3 * (3 * cfg.K k) * δ} ∩ (D g ∩ {p | sub p = θ}) ⊆
            cfg.goodSet k s ∩ {p | cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1 = g ∧
              p.2 ∈ Icc ((θ : ℝ) * δ) (((θ : ℝ) + 1) * δ) ∧
              |cfg.hidden k p - (a * (j : ℝ) + p.2 * 0)| ≤ 11 * a} := by
          rintro e ⟨he, ⟨hgood, hge⟩, heθ⟩
          refine ⟨hgood, hge, ?_, ?_⟩
          · have h1 := Int.floor_le (e.2 / δ)
            have h2 := Int.lt_floor_add_one (e.2 / δ)
            have heθ' : ⌊e.2 / δ⌋ = θ := heθ
            rw [heθ'] at h1 h2
            constructor
            · have := (le_div_iff₀ hδ).mp h1; linarith
            · have := (div_lt_iff₀ hδ).mp h2; linarith
          · rw [mul_zero, add_zero, ← cfg.quadratic_hiddenCoeff k e]
            refine (le_of_eq_of_le rfl he).trans ?_
            linarith [hηt]
        have hcap := hB g (a * (j : ℝ)) 0 (11 * a) ((θ : ℝ) * δ) (((θ : ℝ) + 1) * δ)
          (by linarith) (by linarith) (by simp; linarith) (by nlinarith)
        have hle := (measure_mono hsub2).trans ((hρμ _).trans hcap)
        have hfin : ENNReal.ofReal (cfg.N k ^ ε₁ * ((((θ : ℝ) + 1) * δ - (θ : ℝ) * δ) +
            cfg.N k ^ (-(4 * s))) * W g * (11 * a) ^ cfg.d) ≠ ∞ := ENNReal.ofReal_ne_top
        refine (ENNReal.toReal_mono hfin hle).trans ?_
        rw [ENNReal.toReal_ofReal (by
          have := hWnn g
          have : 0 ≤ (11 * a) ^ cfg.d := Real.rpow_nonneg (by linarith) _
          have : 0 ≤ cfg.N k ^ ε₁ := Real.rpow_nonneg hNpos.le _
          have : 0 ≤ cfg.N k ^ (-(4 * s)) := Real.rpow_nonneg hNpos.le _
          have : ((θ : ℝ) + 1) * δ - (θ : ℝ) * δ = δ := by ring
          rw [this]; positivity)]
        have hwidth : ((θ : ℝ) + 1) * δ - (θ : ℝ) * δ = δ := by ring
        rw [hwidth, Real.mul_rpow (by norm_num) ha.le]
        have h11 : (11 : ℝ) ^ cfg.d ≤ 11 := by
          calc (11 : ℝ) ^ cfg.d ≤ 11 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hd1.le
            _ = 11 := Real.rpow_one 11
        have hε : 0 ≤ cfg.N k ^ ε₁ := Real.rpow_nonneg hNpos.le _
        have had : 0 ≤ a ^ cfg.d := Real.rpow_nonneg ha.le _
        have hW := hWnn g
        calc
          cfg.N k ^ ε₁ * (δ + cfg.N k ^ (-(4 * s))) * W g * (11 ^ cfg.d * a ^ cfg.d) ≤
              cfg.N k ^ ε₁ * (2 * δ) * W g * (11 * a ^ cfg.d) := by gcongr; linarith
          _ = 22 * cfg.N k ^ ε₁ * δ * W g * a ^ cfg.d := by ring)
    refine hcard.trans (le_of_eq ?_)
    simp only [φ]
    rw [show -ε' - θ₂ = -(ε' + θ₂) by ring, Real.rpow_neg hNpos.le]
    have : 0 < a ^ cfg.d := Real.rpow_pos_of_pos ha _
    have : 0 < cfg.N k ^ (ε' + θ₂) := Real.rpow_pos_of_pos hNpos _
    rw [show ε₁ + ε' + θ₂ = ε₁ + (ε' + θ₂) by ring, Real.rpow_add hNpos]
    field_simp
    rw [Real.rpow_add hNpos, Real.rpow_add hNpos]
    ring
  · -- membership
    intro p hp
    obtain ⟨hgood, hTyp, hHCp, hkept⟩ := hp
    simp only [CL, hTyp, if_true, Finset.mem_filter]
    exact ⟨hHCp, hkept, p, ⟨hgood, rfl⟩, rfl, rfl, rfl⟩

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
