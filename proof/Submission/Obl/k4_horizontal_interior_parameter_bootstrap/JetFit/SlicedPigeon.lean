import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedCollide

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced fit: heavy starting bin and light time bins

* `abs_L_le`, `bins_count`: the scalars are bounded by `4K²` and occupy at most
  `3K(8K²/p)^d` bins of width `p` at each time;
* `exists_heavy_start_bin`: Cauchy–Schwarz over the bins at each time, then a pigeonhole over the
  starting bins (paper: "Fixing the first trajectory's starting scalar bin at `u₀` leaves at least
  `p^{2d}/K` of this mass");
* `badBins_mass_le`: time bins whose active part is shorter than `p/K₁` carry collision mass at
  most `2/K₁` times the squared pair weight (paper: "Discard bins with `|T_J| < p/K₁`").
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The scalars of the sliced model are bounded by `4K²`. -/
theorem abs_L_le {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hp1 : p ≤ 1)
    (hK : 1 ≤ K) {l : Ω} {u : ℝ} (h : (l, u) ∈ D.E) : |D.L l u| ≤ 4 * K ^ 2 := by
  have hu := H.E01 _ h
  have hm := H.model _ h
  simp only at hm hu
  have hv := H.vbound l
  have hz := H.zbound l
  have hG := H.Gbound _ hv
  have hφ := H.φbound _ hu
  have hu0 : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  have t1 : |u * D.G (D.v l)| ≤ K := by
    rw [abs_mul]; nlinarith [abs_nonneg u, abs_nonneg (D.G (D.v l))]
  have t2 : |D.φ u * D.v l| ≤ K ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hφ hv (abs_nonneg _) (by linarith)
  have t3 : |D.L l u| ≤ |D.L l u - (D.z l + u * D.G (D.v l) - D.φ u * D.v l)| +
      |D.z l + u * D.G (D.v l) - D.φ u * D.v l| := by
    have := abs_add_le (D.L l u - (D.z l + u * D.G (D.v l) - D.φ u * D.v l))
      (D.z l + u * D.G (D.v l) - D.φ u * D.v l)
    simpa using this
  have t4 : |D.z l + u * D.G (D.v l) - D.φ u * D.v l| ≤ K + K + K ^ 2 := by
    have a := abs_add_le (D.z l) (u * D.G (D.v l))
    have b := abs_sub (D.z l + u * D.G (D.v l)) (D.φ u * D.v l)
    linarith
  have t5 : K * p ≤ K := by nlinarith
  nlinarith

/-- Every time carries at most `3K(8K²/p)^d` occupied `p`-bins of scalars. -/
theorem bins_count {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hp : 0 < p)
    (hp1 : p ≤ 1) (hK : 1 ≤ K) (u : ℝ) :
    ∃ B : Finset ℤ, (B.card : ℝ) ≤ 3 * (K * (8 * K ^ 2 / p) ^ d) ∧
      ∀ l, (l, u) ∈ D.E → ⌊D.L l u / p⌋ ∈ B := by
  classical
  obtain ⟨m, cc, hcov, hm⟩ := H.count u (-(4 * K ^ 2)) (8 * K ^ 2) p le_rfl (by nlinarith)
  refine ⟨Finset.univ.biUnion (fun j : Fin m => Finset.Icc ⌊(cc j - p) / p⌋ ⌊(cc j + p) / p⌋),
    ?_, ?_⟩
  · have hcard : ∀ j : Fin m, (Finset.Icc ⌊(cc j - p) / p⌋ ⌊(cc j + p) / p⌋).card ≤ 3 := by
      intro j
      rw [Int.card_Icc]
      have e1 : (cc j - p) / p = cc j / p - 1 := by field_simp
      have e2 : (cc j + p) / p = cc j / p + 1 := by field_simp
      rw [e1, e2, Int.floor_sub_one, Int.floor_add_one]
      omega
    calc ((Finset.univ.biUnion (fun j : Fin m =>
          Finset.Icc ⌊(cc j - p) / p⌋ ⌊(cc j + p) / p⌋)).card : ℝ)
        ≤ ((∑ j : Fin m, (Finset.Icc ⌊(cc j - p) / p⌋ ⌊(cc j + p) / p⌋).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ((∑ _j : Fin m, 3 : ℕ) : ℝ) := by exact_mod_cast Finset.sum_le_sum (fun j _ => hcard j)
      _ = 3 * m := by simp [mul_comm]
      _ ≤ 3 * (K * (8 * K ^ 2 / p) ^ d) := by linarith
  · intro l hl
    have hL := abs_L_le H hp1 hK hl
    have hmem : D.L l u ∈ {x | ∃ l, (l, u) ∈ D.E ∧ x = D.L l u} ∩
        Icc (-(4 * K ^ 2)) (-(4 * K ^ 2) + 8 * K ^ 2) :=
      ⟨⟨l, hl, rfl⟩, by rw [mem_Icc]; constructor <;> linarith [(abs_le.1 hL).1, (abs_le.1 hL).2]⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov hmem)
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hj
    refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_Icc.2 ⟨?_, ?_⟩⟩
    · exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hp.le)
    · exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hp.le)


/-- **A heavy first starting bin**: some `β₀` carries collision mass
`≥ (ν⊗dt)(Elab)² / C₁²`, `C₁ = 3K(8K²/p)^d`. -/
theorem exists_heavy_start_bin {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d)
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 1 ≤ K) (u₀ : ℝ) :
    ∃ β₀ : ℤ, ((D.ν.prod volume) (Elab D u₀)) ^ 2 ≤
      ENNReal.ofReal (3 * (K * (8 * K ^ 2 / p) ^ d)) *
        (ENNReal.ofReal (3 * (K * (8 * K ^ 2 / p) ^ d)) *
          ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β₀)) := by
  classical
  have := H.finite
  set C₁ : ℝ := 3 * (K * (8 * K ^ 2 / p) ^ d) with hC₁
  have hbin : Measurable (fun q : Ω × ℝ => ⌊D.L q.1 q.2 / p⌋) :=
    Int.measurable_floor.comp (H.measL.div_const p)
  have hlow := timeColl_lower (bin := fun l u => ⌊D.L l u / p⌋) D.ν (measurableSet_Elab H u₀)
    (fun q hq => H.E01 q hq.1) hbin (C₁ := C₁) (fun u => by
      obtain ⟨B, hB, hmem⟩ := bins_count H hp hp1 hK u
      exact ⟨B, hB, fun l hl => hmem l hl.1⟩)
  obtain ⟨B₀, hB₀, hmem₀⟩ := bins_count H hp hp1 hK u₀
  have hsub : timeColl (Elab D u₀) (fun l u => ⌊D.L l u / p⌋) ⊆ ⋃ β ∈ B₀, Scol D p u₀ β := by
    intro x hx
    exact mem_iUnion₂.2 ⟨_, hmem₀ _ hx.1.2, hx, rfl⟩
  have hsum : ((D.ν.prod D.ν).prod volume) (timeColl (Elab D u₀) (fun l u => ⌊D.L l u / p⌋)) ≤
      ∑ β ∈ B₀, ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
  by_cases hB0 : B₀ = ∅
  · -- no bins at `u₀`: nothing is labeled at `u₀`
    refine ⟨0, ?_⟩
    have : ((D.ν.prod D.ν).prod volume) (timeColl (Elab D u₀) (fun l u => ⌊D.L l u / p⌋)) = 0 := by
      apply le_antisymm _ bot_le
      calc _ ≤ ∑ β ∈ B₀, ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β) := hsum
        _ = 0 := by rw [hB0, Finset.sum_empty]
    rw [this, mul_zero] at hlow
    exact hlow.trans bot_le
  obtain ⟨β₀, hβ₀, hmax⟩ := B₀.exists_max_image
    (fun β => ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β)) (Finset.nonempty_iff_ne_empty.2 hB0)
  refine ⟨β₀, hlow.trans ?_⟩
  gcongr
  calc ((D.ν.prod D.ν).prod volume) (timeColl (Elab D u₀) (fun l u => ⌊D.L l u / p⌋))
      ≤ ∑ β ∈ B₀, ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β) := hsum
    _ ≤ ∑ _β ∈ B₀, ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β₀) :=
        Finset.sum_le_sum (fun β hβ => hmax β hβ)
    _ = B₀.card * ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β₀) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal C₁ * ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β₀) := by
        gcongr
        rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hB₀

/-- Active times: a positive mass of trajectories is labeled there. -/
def actSet (D : SlicedData Ω) : Set ℝ := {u | 0 < D.ν {l | (l, u) ∈ D.E}}

/-- Time bins whose active part has length at least `p / K₁`. -/
def goodIdx (D : SlicedData Ω) (p K₁ : ℝ) : Set ℤ :=
  {i | ENNReal.ofReal (p / K₁) ≤ volume (actSet D ∩ {u | ⌊u / p⌋ = i})}

theorem measurableSet_actSet {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) :
    MeasurableSet (actSet D) := by
  haveI := H.finite
  exact measurableSet_lt measurable_const (measurable_measure_prodMk_right H.measE)

/-- **Light time bins carry little collision mass.** -/
theorem badBins_mass_le {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hp : 0 < p)
    (hp1 : p ≤ 1) (hK : 1 ≤ K) {K₁ : ℝ} (hK₁ : 0 < K₁) (u₀ : ℝ) (β₀ : ℤ) :
    ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β₀ ∩ {x | ⌊x.2 / p⌋ ∉ goodIdx D p K₁}) ≤
      ENNReal.ofReal ((2 * K / p + 2) * (K * p ^ (1 + d))) *
        ENNReal.ofReal ((2 * K / p + 2) * (K * p ^ (1 + d))) * ENNReal.ofReal (2 / K₁) := by
  classical
  haveI hfin := H.finite
  set c2 := ENNReal.ofReal ((2 * K / p + 2) * (K * p ^ (1 + d))) *
    ENNReal.ofReal ((2 * K / p + 2) * (K * p ^ (1 + d))) with hc2
  have hgc : MeasurableSet ((goodIdx D p K₁)ᶜ : Set ℤ) := MeasurableSet.of_discrete
  have hbadm : MeasurableSet {x : (Ω × Ω) × ℝ | ⌊x.2 / p⌋ ∉ goodIdx D p K₁} :=
    (Int.measurable_floor.comp (measurable_snd.div_const p)) hgc
  have hm := (measurableSet_Scol H u₀ β₀).inter hbadm
  set X : Set ℝ := actSet D ∩ Icc (0:ℝ) 1 ∩ {u | ⌊u / p⌋ ∉ goodIdx D p K₁} with hX
  have hXm : MeasurableSet X :=
    ((measurableSet_actSet H).inter measurableSet_Icc).inter
      ((Int.measurable_floor.comp (measurable_id.div_const p)) hgc)
  rw [Measure.prod_apply_symm hm]
  calc ∫⁻ u, (D.ν.prod D.ν) ((fun x => (x, u)) ⁻¹' (Scol D p u₀ β₀ ∩
        {x | ⌊x.2 / p⌋ ∉ goodIdx D p K₁}))
      ≤ ∫⁻ u, X.indicator (fun _ => c2) u := by
        apply lintegral_mono
        intro u
        dsimp only
        by_cases huX : u ∈ X
        · rw [indicator_of_mem huX]
          exact (measure_mono inter_subset_left).trans (pairWeight_le H hp (by linarith) u₀ β₀ u)
        · rw [indicator_of_notMem huX]
          apply le_of_eq
          by_cases hbad : ⌊u / p⌋ ∈ goodIdx D p K₁
          · have : (fun x : Ω × Ω => (x, u)) ⁻¹' (Scol D p u₀ β₀ ∩
                {x | ⌊x.2 / p⌋ ∉ goodIdx D p K₁}) = ∅ := by
              ext x; simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false,
                not_and]
              intro _ h; exact h hbad
            rw [this, measure_empty]
          · -- `u` is inactive or outside `[0,1]`: the slice is null
            have hsub : (fun x : Ω × Ω => (x, u)) ⁻¹' (Scol D p u₀ β₀ ∩
                {x | ⌊x.2 / p⌋ ∉ goodIdx D p K₁}) ⊆ {l | (l, u) ∈ D.E} ×ˢ univ := by
              rintro x ⟨⟨⟨⟨hl, -⟩, -⟩, -⟩, -⟩
              exact ⟨hl, trivial⟩
            have hnull : D.ν {l | (l, u) ∈ D.E} = 0 := by
              by_contra hne
              have hpos : 0 < D.ν {l | (l, u) ∈ D.E} := pos_iff_ne_zero.2 hne
              apply huX
              refine ⟨⟨hpos, ?_⟩, hbad⟩
              obtain ⟨l, hl⟩ := nonempty_of_measure_ne_zero hne
              exact H.E01 _ hl
            apply le_antisymm _ bot_le
            calc _ ≤ (D.ν.prod D.ν) ({l | (l, u) ∈ D.E} ×ˢ univ) := measure_mono hsub
              _ = 0 := by rw [Measure.prod_prod, hnull, zero_mul]
    _ = c2 * volume X := lintegral_indicator_const hXm c2
    _ ≤ c2 * ENNReal.ofReal (2 / K₁) := by
        gcongr
        -- `X` lies in the light bins `0 ≤ i ≤ ⌊1/p⌋`
        set I : Finset ℤ := (Finset.Icc 0 ⌊1 / p⌋).filter (fun i => i ∉ goodIdx D p K₁)
        have hXsub : X ⊆ ⋃ i ∈ I, actSet D ∩ {u | ⌊u / p⌋ = i} := by
          rintro u ⟨⟨hua, hu01⟩, hub⟩
          refine mem_iUnion₂.2 ⟨⌊u / p⌋, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, hub⟩,
            hua, rfl⟩
          · exact Int.floor_nonneg.2 (div_nonneg hu01.1 hp.le)
          · exact Int.floor_le_floor (div_le_div_of_nonneg_right hu01.2 hp.le)
        calc volume X ≤ ∑ i ∈ I, volume (actSet D ∩ {u | ⌊u / p⌋ = i}) :=
              (measure_mono hXsub).trans (measure_biUnion_finset_le _ _)
          _ ≤ ∑ _i ∈ I, ENNReal.ofReal (p / K₁) := by
              apply Finset.sum_le_sum
              intro i hi
              have := (Finset.mem_filter.1 hi).2
              simp only [goodIdx, mem_ofPred_eq, not_le] at this
              exact this.le
          _ = I.card * ENNReal.ofReal (p / K₁) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ENNReal.ofReal (2 / K₁) := by
              have hIc : (I.card : ℝ) ≤ 1 / p + 1 := by
                have h1 : I.card ≤ (Finset.Icc (0:ℤ) ⌊1 / p⌋).card := Finset.card_filter_le _ _
                rw [Int.card_Icc] at h1
                have h2 : (0:ℤ) ≤ ⌊1 / p⌋ + 1 - 0 := by
                  have := Int.floor_nonneg.2 (show (0:ℝ) ≤ 1 / p by positivity); omega
                have h3 : ((⌊1 / p⌋ + 1 - 0).toNat : ℝ) = ((⌊1 / p⌋ + 1 - 0 : ℤ) : ℝ) := by
                  exact_mod_cast Int.toNat_of_nonneg h2
                have h4 : (I.card : ℝ) ≤ ((⌊1 / p⌋ + 1 - 0).toNat : ℝ) := by exact_mod_cast h1
                rw [h3] at h4; push_cast at h4
                linarith [Int.floor_le (1 / p)]
              rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
              apply ENNReal.ofReal_le_ofReal
              calc (I.card : ℝ) * (p / K₁) ≤ (1 / p + 1) * (p / K₁) :=
                    mul_le_mul_of_nonneg_right hIc (by positivity)
                _ = (1 + p) / K₁ := by field_simp
                _ ≤ 2 / K₁ := by apply div_le_div_of_nonneg_right _ hK₁.le; linarith

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
