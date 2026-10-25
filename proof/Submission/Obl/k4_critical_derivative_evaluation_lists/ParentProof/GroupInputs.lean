/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, GroupInputs.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupBudget

/-! The hypotheses of scalar clustering in one group, checked for the original
frozen residual from the band cap (B) and the support count (S). -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_coefficient_clustering

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- Statement (B) at one sample. -/
def BandCapAt (k : ℕ) (s ε₁ : ℝ) : Prop :=
  ∀ (g : ℤ × ℤ × ℤ) (c₀ c₁ r τ₁ τ₂ : ℝ),
    cfg.N k ^ (-s) ≤ r → r ≤ 4 → |c₁| ≤ 4 * cfg.K k → τ₁ ≤ τ₂ →
    cfg.μ k (cfg.goodSet k s ∩
        {p | cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1 = g ∧
          p.2 ∈ Icc τ₁ τ₂ ∧ |cfg.hidden k p - (c₀ + p.2 * c₁)| ≤ r}) ≤
      ENNReal.ofReal (cfg.N k ^ ε₁ * (τ₂ - τ₁ + cfg.N k ^ (-(4 * s))) *
        cfg.groupWeight k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) g * r ^ cfg.d)

/-- Statement (S) at one sample. -/
def SupportAt (k : ℕ) (s ε₁ : ℝ) : Prop :=
  ∀ (g : ℤ × ℤ × ℤ) (τ : ℤ), ∃ J : Finset ℤ,
    (J.card : ℝ) ≤ cfg.N k ^ ε₁ * (cfg.N k ^ (-s)) ^ (-cfg.d) ∧
    ∀ p ∈ cfg.goodSet k s,
      cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1 = g →
      ⌊p.2 / cfg.N k ^ (-s)⌋ = τ → ⌊cfg.hidden k p / cfg.N k ^ (-s)⌋ ∈ J

/-- The incidences of one group in the good set. -/
def groupSet (k : ℕ) (s : ℝ) (g : ℤ × ℤ × ℤ) : Set (α × ℝ) :=
  {p | p ∈ cfg.goodSet k s ∧ cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1 = g}

theorem groupSet_subset_good (k : ℕ) (s : ℝ) (g : ℤ × ℤ × ℤ) :
    cfg.groupSet k s g ⊆ cfg.goodSet k s := fun _ hp => hp.1

theorem measurableSet_groupSet (k : ℕ) (s : ℝ) (hb : Measurable (cfg.b k))
    (hBm : ∀ i, MeasurableSet (cfg.B k s i)) (g : ℤ × ℤ × ℤ) :
    MeasurableSet (cfg.groupSet k s g) :=
  (cfg.measurableSet_goodSet k hb s hBm).inter
    ((cfg.measurable_groupCode k hb _ _).comp measurable_fst (measurableSet_singleton g))

theorem groupSet_unit (k : ℕ) (s : ℝ) (g : ℤ × ℤ × ℤ) :
    cfg.groupSet k s g ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun p hp => ⟨mem_univ _, hp.1.1⟩

/-- Original domination of one group by its restricted prior. -/
theorem group_domination (k : ℕ) (s : ℝ) (hb : Measurable (cfg.b k))
    (hBm : ∀ i, MeasurableSet (cfg.B k s i)) (hρμ : cfg.ρ k ≤ cfg.μ k)
    (hdom : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod volume))
    [SFinite (cfg.ν k)] (g : ℤ × ℤ × ℤ) :
    (cfg.ρ k).restrict (cfg.groupSet k s g) ≤ ENNReal.ofReal (cfg.K k) •
      ((cfg.ν k).restrict {l | cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) l = g}).prod
        volume := by
  have hX : MeasurableSet {l | cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) l = g} :=
    (cfg.measurable_groupCode k hb _ _) (measurableSet_singleton g)
  have hsub : cfg.groupSet k s g ⊆
      {l | cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) l = g} ×ˢ univ :=
    fun p hp => ⟨hp.2, mem_univ _⟩
  rw [Measure.restrict_prod_eq_prod_univ, ← Measure.restrict_smul]
  calc
    (cfg.ρ k).restrict (cfg.groupSet k s g) ≤ (cfg.μ k).restrict (cfg.groupSet k s g) :=
      Measure.restrict_mono le_rfl hρμ
    _ ≤ (ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume).restrict (cfg.groupSet k s g) :=
      Measure.restrict_mono le_rfl hdom
    _ ≤ _ := Measure.restrict_mono hsub le_rfl

/-- The whole mass of one group, from (B) by covering the hidden range. -/
theorem group_total_mass (k : ℕ) {s ε₁ : ℝ} (hs : 0 < s) (hρμ : cfg.ρ k ≤ cfg.μ k)
    (hK : 1 ≤ cfg.K k) (hN : 1 < cfg.N k) (hB : cfg.BandCapAt k s ε₁)
    (hm4 : cfg.N k ^ (-(4 * s)) ≤ 1) (g : ℤ × ℤ × ℤ) :
    cfg.ρ k (cfg.groupSet k s g) ≤ ENNReal.ofReal (12 * cfg.K k * cfg.N k ^ ε₁ *
      cfg.groupWeight k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) g) := by
  set W := cfg.groupWeight k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) g
  have hW : 0 ≤ W := cfg.groupWeight_nonneg k _ _ g
  have hNpos : 0 < cfg.N k := by linarith
  have ha : cfg.N k ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)
  set M : ℤ := ⌈3 * cfg.K k / 2⌉
  have hM0 : 0 ≤ M := Int.ceil_nonneg (by linarith)
  have hMle : (M : ℝ) ≤ 3 * cfg.K k / 2 + 1 := (Int.ceil_lt_add_one _).le
  -- bands of half-width one centered at the even integers
  let band : ℤ → Set (α × ℝ) := fun m => cfg.goodSet k s ∩
    {p | cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1 = g ∧
      p.2 ∈ Icc (0 : ℝ) 1 ∧ |cfg.hidden k p - ((2 * m : ℤ) + p.2 * 0)| ≤ 1}
  have hcover : cfg.groupSet k s g ⊆ ⋃ m ∈ Finset.Icc (-M) M, band m := by
    intro p hp
    obtain ⟨hgood, hgp⟩ := hp
    have ⟨ht, _, _, _, _, h2, h5, _⟩ := hgood
    have hw : |cfg.hidden k p| ≤ 3 * cfg.K k := by
      unfold hidden
      have ht1 : |p.2| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
      calc
        |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5| ≤ |cfg.b k p.1 2| + |p.2 * cfg.b k p.1 5| :=
          abs_add_le _ _
        _ ≤ cfg.K k + 1 * (2 * cfg.K k) := by
          rw [abs_mul]
          exact add_le_add h2 (mul_le_mul ht1 h5 (abs_nonneg _) zero_le_one)
        _ = 3 * cfg.K k := by ring
    set m : ℤ := ⌊cfg.hidden k p / 2 + 1 / 2⌋
    have hm1 := Int.floor_le (cfg.hidden k p / 2 + 1 / 2)
    have hm2 := Int.lt_floor_add_one (cfg.hidden k p / 2 + 1 / 2)
    refine mem_iUnion₂.mpr ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hgood, hgp, ht, ?_⟩
    · have hwl := (abs_le.mp hw).1
      have : (-(M : ℝ)) - 1 < (m : ℝ) := by
        linarith [Int.le_ceil (3 * cfg.K k / 2)]
      have : -M - 1 < m := by exact_mod_cast this
      omega
    · have hwr := (abs_le.mp hw).2
      have : (m : ℝ) < (M : ℝ) + 1 := by
        linarith [Int.le_ceil (3 * cfg.K k / 2)]
      have : m < M + 1 := by exact_mod_cast this
      omega
    · push_cast
      rw [mul_zero, add_zero, abs_le]
      constructor <;> linarith
  have hband (m : ℤ) : cfg.ρ k (band m) ≤ ENNReal.ofReal (2 * cfg.N k ^ ε₁ * W) := by
    refine (hρμ _).trans ((hB g ((2 * m : ℤ) : ℝ) 0 1 0 1 ha (by norm_num) (by simp; linarith)
      zero_le_one).trans (ENNReal.ofReal_le_ofReal ?_))
    rw [Real.one_rpow, mul_one, sub_zero]
    have hε : 0 ≤ cfg.N k ^ ε₁ := Real.rpow_nonneg hNpos.le _
    nlinarith only [mul_le_mul_of_nonneg_left hm4 (mul_nonneg hε hW), hε, hW]
  have hcard : ((Finset.Icc (-M) M).card : ℝ) ≤ 6 * cfg.K k := by
    rw [Int.card_Icc]
    have hnat : (((M + 1 - -M).toNat : ℕ) : ℤ) = 2 * M + 1 := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have : (((M + 1 - -M).toNat : ℕ) : ℝ) = 2 * (M : ℝ) + 1 := by exact_mod_cast hnat
    rw [this]
    linarith
  calc
    cfg.ρ k (cfg.groupSet k s g) ≤ cfg.ρ k (⋃ m ∈ Finset.Icc (-M) M, band m) := measure_mono hcover
    _ ≤ ∑ m ∈ Finset.Icc (-M) M, cfg.ρ k (band m) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc (-M) M, ENNReal.ofReal (2 * cfg.N k ^ ε₁ * W) :=
      Finset.sum_le_sum (fun m _ => hband m)
    _ = ENNReal.ofReal (((Finset.Icc (-M) M).card : ℝ) * (2 * cfg.N k ^ ε₁ * W)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hε : 0 ≤ cfg.N k ^ ε₁ := Real.rpow_nonneg hNpos.le _
      nlinarith only [mul_le_mul_of_nonneg_right hcard (mul_nonneg (mul_nonneg zero_le_two hε) hW)]

/-- The support finset of one group: time bins of `[0,1]` times the hidden
bins supplied by (S). -/
theorem group_support_finset (k : ℕ) {s ε₁ : ℝ} (hN : 1 < cfg.N k) (hs : 0 < s)
    (hS : cfg.SupportAt k s ε₁) (g : ℤ × ℤ × ℤ) :
    ∃ F : Finset (ℤ × ℤ),
      (F.card : ℝ) ≤ 2 * cfg.N k ^ ε₁ * (cfg.N k ^ (-s)) ^ (-1 - cfg.d) ∧
      ∀ l t, (l, t) ∈ cfg.groupSet k s g →
        (⌊t / cfg.N k ^ (-s)⌋, ⌊quadratic (cfg.clampedCoeff k l) t / cfg.N k ^ (-s)⌋) ∈ F := by
  set a := cfg.N k ^ (-s)
  have hNpos : 0 < cfg.N k := by linarith
  have ha : 0 < a := Real.rpow_pos_of_pos hNpos _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)
  choose J hJcard hJ using hS g
  let T : Finset ℤ := Finset.Icc 0 ⌊1 / a⌋
  refine ⟨T.biUnion (fun τ => {τ} ×ˢ J τ), ?_, ?_⟩
  · have hT : (T.card : ℝ) ≤ 2 / a := by
      have hfl : (0 : ℤ) ≤ ⌊1 / a⌋ := Int.floor_nonneg.mpr (by positivity)
      have hc : (T.card : ℝ) = (⌊1 / a⌋ : ℝ) + 1 := by
        simp only [T, Int.card_Icc, sub_zero]
        have hnat : (((⌊1 / a⌋ + 1).toNat : ℕ) : ℤ) = ⌊1 / a⌋ + 1 := by
          rw [Int.toNat_of_nonneg (by omega)]
        exact_mod_cast hnat
      rw [hc]
      have := Int.floor_le (1 / a)
      have h1a : 1 ≤ 1 / a := by rw [le_div_iff₀ ha]; linarith
      calc
        (⌊1 / a⌋ : ℝ) + 1 ≤ 1 / a + 1 / a := by linarith
        _ = 2 / a := by ring
    calc
      ((T.biUnion (fun τ => {τ} ×ˢ J τ)).card : ℝ) ≤ ∑ τ ∈ T, (({τ} ×ˢ J τ).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ = ∑ τ ∈ T, ((J τ).card : ℝ) := by
        apply Finset.sum_congr rfl; intro τ _
        rw [Finset.card_product, Finset.card_singleton, one_mul]
      _ ≤ ∑ _τ ∈ T, cfg.N k ^ ε₁ * a ^ (-cfg.d) := Finset.sum_le_sum (fun τ _ => hJcard τ)
      _ = (T.card : ℝ) * (cfg.N k ^ ε₁ * a ^ (-cfg.d)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 / a * (cfg.N k ^ ε₁ * a ^ (-cfg.d)) := by gcongr
      _ = 2 * cfg.N k ^ ε₁ * a ^ (-1 - cfg.d) := by
        rw [show -1 - cfg.d = -1 + -cfg.d by ring, Real.rpow_add ha, Real.rpow_neg_one]
        field_simp
  · intro l t hlt
    have hgood := hlt.1
    have hq : quadratic (cfg.clampedCoeff k l) t = cfg.hidden k (l, t) := by
      rw [cfg.clampedCoeff_of_good hgood]
      exact cfg.quadratic_hiddenCoeff k (l, t)
    rw [hq]
    refine Finset.mem_biUnion.mpr ⟨⌊t / a⌋, ?_, ?_⟩
    · have ht := hgood.1
      exact Finset.mem_Icc.mpr ⟨Int.floor_nonneg.mpr (div_nonneg ht.1 ha.le),
        Int.floor_mono (div_le_div_of_nonneg_right ht.2 ha.le)⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,
        hJ ⌊t / a⌋ (l, t) hgood hlt.2 rfl⟩


theorem abs_clampedCoeff_one_le (k : ℕ) (hK : 0 ≤ cfg.K k) (l : α) :
    |cfg.clampedCoeff k l 1| ≤ 2 * cfg.K k := by
  unfold clampedCoeff
  split_ifs with hl
  · rw [cfg.hiddenCoeff_apply_one]; exact hl.2
  · simp only [PiLp.zero_apply, abs_zero]; linarith

/-- The polynomial-band cap required by scalar clustering in one group, in
original units with the group reference weight. -/
theorem group_clustering_band (k : ℕ) {s ε₁ ηc : ℝ} (hs : 0 < s) (hρμ : cfg.ρ k ≤ cfg.μ k)
    (hK : 1 ≤ cfg.K k) (hN : 1 < cfg.N k) (hd : 0 ≤ cfg.d) (hd1 : cfg.d < 1)
    (hB : cfg.BandCapAt k s ε₁)
    (hm4 : cfg.N k ^ (-(4 * s)) ≤ 1)
    (hc1 : 12 * cfg.K k * cfg.N k ^ ε₁ ≤ cfg.N k ^ ηc)
    (hc2 : 8 * cfg.N k ^ ε₁ ≤ cfg.N k ^ ηc) (g : ℤ × ℤ × ℤ)
    (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : cfg.N k ^ (-s) ≤ r)
    (hex : ∃ l, cfg.clampedCoeff k l ∈ Metric.ball b r) :
    cfg.ρ k (cfg.groupSet k s g ∩
        {p | |quadratic (cfg.clampedCoeff k p.1) p.2 - quadratic b p.2| ≤ 3 * r}) ≤
      ENNReal.ofReal (cfg.groupWeight k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) g *
        (cfg.N k ^ ηc * r ^ cfg.d)) := by
  set W := cfg.groupWeight k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) g
  have hW : 0 ≤ W := cfg.groupWeight_nonneg k _ _ g
  have hNpos : 0 < cfg.N k := by linarith
  have hr0 : 0 < r := (Real.rpow_pos_of_pos hNpos _).trans_le hr
  by_cases hr1 : 1 ≤ r
  · have hrd : 1 ≤ r ^ cfg.d := Real.one_le_rpow hr1 hd
    calc
      _ ≤ cfg.ρ k (cfg.groupSet k s g) := measure_mono inter_subset_left
      _ ≤ ENNReal.ofReal (12 * cfg.K k * cfg.N k ^ ε₁ * W) :=
        cfg.group_total_mass k hs hρμ hK hN hB hm4 g
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hη : 0 ≤ cfg.N k ^ ηc := Real.rpow_nonneg hNpos.le _
        calc
          12 * cfg.K k * cfg.N k ^ ε₁ * W ≤ cfg.N k ^ ηc * W := mul_le_mul_of_nonneg_right hc1 hW
          _ ≤ cfg.N k ^ ηc * W * r ^ cfg.d := le_mul_of_one_le_right (by positivity) hrd
          _ = _ := by ring
  · replace hr1 := lt_of_not_ge hr1
    obtain ⟨l, hl⟩ := hex
    have hdist : ‖cfg.clampedCoeff k l - b‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hl
    have hb2 : |b 2| ≤ r := by
      have hh := PiLp.norm_apply_le (cfg.clampedCoeff k l - b) 2
      simp only [Real.norm_eq_abs, PiLp.sub_apply, cfg.clampedCoeff_apply_two, zero_sub,
        abs_neg] at hh
      exact hh.trans hdist.le
    have hb1 : |b 1| ≤ 4 * cfg.K k := by
      have hh := PiLp.norm_apply_le (cfg.clampedCoeff k l - b) 1
      simp only [Real.norm_eq_abs, PiLp.sub_apply] at hh
      have hc := cfg.abs_clampedCoeff_one_le k (by linarith) l
      have : |b 1| ≤ |cfg.clampedCoeff k l 1| + |cfg.clampedCoeff k l 1 - b 1| := by
        have := abs_sub_abs_le_abs_sub (b 1) (cfg.clampedCoeff k l 1)
        rw [abs_sub_comm (b 1)] at this
        linarith
      linarith
    have hsub : cfg.groupSet k s g ∩
        {p | |quadratic (cfg.clampedCoeff k p.1) p.2 - quadratic b p.2| ≤ 3 * r} ⊆
        cfg.goodSet k s ∩
          {p | cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1 = g ∧
            p.2 ∈ Icc (0 : ℝ) 1 ∧ |cfg.hidden k p - (b 0 + p.2 * b 1)| ≤ 4 * r} := by
      rintro p ⟨⟨hgood, hgp⟩, hband⟩
      refine ⟨hgood, hgp, hgood.1, ?_⟩
      have hq : quadratic (cfg.clampedCoeff k p.1) p.2 = cfg.hidden k p := by
        rw [cfg.clampedCoeff_of_good hgood]
        exact cfg.quadratic_hiddenCoeff k p
      have hband' : |cfg.hidden k p - quadratic b p.2| ≤ 3 * r := by
        rw [← hq]; exact hband
      have ht := hgood.1
      have htsq : |p.2 ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [ht.1, ht.2]
      have hgap : |quadratic b p.2 - (b 0 + p.2 * b 1)| ≤ r := by
        change |b 0 + p.2 * b 1 + p.2 ^ 2 * b 2 - (b 0 + p.2 * b 1)| ≤ r
        rw [add_sub_cancel_left, abs_mul]
        simpa only [one_mul] using mul_le_mul htsq hb2 (abs_nonneg _) zero_le_one
      calc
        |cfg.hidden k p - (b 0 + p.2 * b 1)| ≤
            |cfg.hidden k p - quadratic b p.2| + |quadratic b p.2 - (b 0 + p.2 * b 1)| :=
          abs_sub_le _ _ _
        _ ≤ 3 * r + r := add_le_add hband' hgap
        _ = 4 * r := by ring
    have hcap := hB g (b 0) (b 1) (4 * r) 0 1 (by linarith) (by linarith) hb1 zero_le_one
    calc
      _ ≤ cfg.ρ k _ := measure_mono hsub
      _ ≤ cfg.μ k _ := hρμ _
      _ ≤ _ := hcap
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [sub_zero, Real.mul_rpow (by norm_num) hr0.le]
        have h4 : (4 : ℝ) ^ cfg.d ≤ 4 := by
          calc (4 : ℝ) ^ cfg.d ≤ 4 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hd1.le
            _ = 4 := Real.rpow_one 4
        have hε : 0 ≤ cfg.N k ^ ε₁ := Real.rpow_nonneg hNpos.le _
        have hrd : 0 ≤ r ^ cfg.d := Real.rpow_nonneg hr0.le _
        have h1m : 1 + cfg.N k ^ (-(4 * s)) ≤ 2 := by linarith
        calc
          cfg.N k ^ ε₁ * (1 + cfg.N k ^ (-(4 * s))) * W * (4 ^ cfg.d * r ^ cfg.d) ≤
              cfg.N k ^ ε₁ * 2 * W * (4 * r ^ cfg.d) := by gcongr
          _ = (8 * cfg.N k ^ ε₁) * W * r ^ cfg.d := by ring
          _ ≤ cfg.N k ^ ηc * W * r ^ cfg.d := by gcongr
          _ = _ := by ring

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
