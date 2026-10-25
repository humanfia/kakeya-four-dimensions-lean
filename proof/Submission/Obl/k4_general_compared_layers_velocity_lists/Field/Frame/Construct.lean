-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Frame.Construct; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Frame.Coeff
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Frame.Measure
import Submission.Obl.k4_general_compared_layers_velocity_lists.Confine.Groups

/-!
# The list frame of a field-ready sample at one index

At a fixed index `k` with the full true assignment at depth `r`, a compared sample and
its common field give a `ListFrame`: the block of the field, its normalized coordinates,
the background `C₁(τ, ζ) U + C₃ U²`, the prior `ν(· | A_Q)`, the normalized law of the
field submeasure, the scalar coefficients of the lines, and the residual lists. The
numerical conditions are stated explicitly; they hold eventually (`Build.lean`).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent.FieldFrame

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The lines of the block with controlled scalar coefficients. -/
def frameGood (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (Cf : Fin 4 → ℝ) (ε : ℝ) : Set α :=
  p.B k r Q ∩ {l | ∀ i, |rawCoeff p k r Q Cf l i| ≤ p.N k ^ ε}

/-- The scalar coefficients of the frame (zero off the good lines). -/
def frameCoeff (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (Cf : Fin 4 → ℝ) (ε : ℝ) (l : α) :
    Fin 5 → ℝ := by
  classical
  exact if l ∈ frameGood p k r Q Cf ε then rawCoeff p k r Q Cf l else 0

theorem frameCoeff_of_mem {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)} {Cf : Fin 4 → ℝ} {ε : ℝ} {l : α}
    (hl : l ∈ frameGood p k r Q Cf ε) : frameCoeff p k r Q Cf ε l = rawCoeff p k r Q Cf l := by
  classical
  unfold frameCoeff
  split_ifs
  rfl

theorem frameCoeff_bound {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)} {Cf : Fin 4 → ℝ} {ε : ℝ}
    (hN : 0 < p.N k) (l : α) (i : Fin 5) : |frameCoeff p k r Q Cf ε l i| ≤ p.N k ^ ε := by
  classical
  unfold frameCoeff
  split_ifs with hl
  · exact hl.2 i
  · simp only [Pi.zero_apply, abs_zero]
    exact (Real.rpow_pos_of_pos hN _).le

theorem measurableSet_frameGood {k : ℕ} (hb : Measurable (p.b k)) {r : ℝ} {Q : Fin (p.n k r)}
    (hB : MeasurableSet (p.B k r Q)) (Cf : Fin 4 → ℝ) (ε : ℝ) :
    MeasurableSet (frameGood p k r Q Cf ε) := by
  unfold frameGood
  refine hB.inter ?_
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le
    ((measurable_pi_iff.mp (measurable_rawCoeff p hb r Q Cf)) i).abs measurable_const

theorem measurable_frameCoeff {k : ℕ} (hb : Measurable (p.b k)) {r : ℝ} {Q : Fin (p.n k r)}
    (hB : MeasurableSet (p.B k r Q)) (Cf : Fin 4 → ℝ) (ε : ℝ) :
    Measurable (frameCoeff p k r Q Cf ε) := by
  classical
  unfold frameCoeff
  exact Measurable.ite (measurableSet_frameGood p hb hB Cf ε)
    (measurable_rawCoeff p hb r Q Cf) measurable_const

theorem blockStart_nonneg (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) : 0 ≤ p.blockStart k r Q := by
  unfold Parent.blockStart
  positivity

theorem blockStart_add_le (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) :
    p.blockStart k r Q + p.blockLen k r ≤ 1 := by
  unfold Parent.blockStart Parent.blockLen
  have hT : (0 : ℝ) < 2 ^ p.T k r := by positivity
  have hj : ((p.j k r Q : ℕ) : ℝ) + 1 ≤ 2 ^ p.T k r := by
    have := (p.j k r Q).isLt
    exact_mod_cast this
  rw [div_add' _ _ _ hT.ne', div_le_one hT]
  · calc ((p.j k r Q : ℕ) : ℝ) + (2 ^ p.T k r)⁻¹ * 2 ^ p.T k r =
          ((p.j k r Q : ℕ) : ℝ) + 1 := by rw [inv_mul_cancel₀ hT.ne']
      _ ≤ 2 ^ p.T k r := hj

theorem mem_unit_of_mem_block {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)} {t : ℝ}
    (ht : t ∈ block (p.T k r) (p.j k r Q)) : t ∈ Icc (0 : ℝ) 1 := by
  rw [block_eq_Icc] at ht
  exact ⟨(blockStart_nonneg p k r Q).trans ht.1, ht.2.trans (blockStart_add_le p k r Q)⟩

/-- The facts about one true block used by its list frame. -/
theorem atDepth_block {k : ℕ} {r R : ℝ} (hat : p.AtDepth k r R) (hN : 0 < p.N k)
    (hK : 0 < p.K k) (Q : Fin (p.n k r)) :
    MeasurableSet (p.A k r Q) ∧ MeasurableSet (p.B k r Q) ∧ p.B k r Q ⊆ p.A k r Q ∧
    p.ν k (p.A k r Q) ≠ 0 ∧ (∀ e, |p.c k r Q e| ≤ p.K k) ∧
    (∀ l ∈ p.A k r Q, ∀ t ∈ block (p.T k r) (p.j k r Q),
      |p.x k l t 1 - p.c k r Q 0 - t * p.c k r Q 1| ≤ p.K k * p.blockLen k r ∧
      |p.x k l t 2 - p.c k r Q 2 - t * p.c k r Q 3 - p.c k r Q 4 * p.x k l t 1| ≤
        p.K k * p.blockWidth k r) := by
  obtain ⟨hAm, hBm, hBA⟩ := hat.2.2.1 Q
  obtain ⟨hlow, -, -, hc, -, hgeo, -⟩ := hat.2.2.2.2.1 Q
  refine ⟨hAm, hBm, hBA, ?_, hc, ?_⟩
  · apply ne_of_gt
    refine lt_of_lt_of_le ?_ hlow
    rw [ENNReal.ofReal_pos]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(p.T k r : ℤ)) := by positivity
    have h3 : (0 : ℝ) < p.N k ^ (-r) := Real.rpow_pos_of_pos hN _
    have h4 : (0 : ℝ) < p.N k ^ (-p.ℓ * r) := Real.rpow_pos_of_pos hN _
    have h5 : (0 : ℝ) < (p.N k ^ (-r)) ^ p.d := Real.rpow_pos_of_pos h3 _
    positivity
  · intro l hl t ht
    obtain ⟨h1, h2, -⟩ := hgeo l hl t ht
    have hq : (2 : ℝ) ^ (-(p.T k r : ℤ)) = p.blockLen k r := by
      rw [zpow_neg, zpow_natCast]
      rfl
    rw [hq] at h1 h2
    refine ⟨h1, ?_⟩
    unfold Parent.blockWidth
    rw [← mul_assoc]
    exact h2

/-- The list frame of a field-ready sample at one index, under explicit numerical
conditions. -/
theorem listFrame_of_atDepth (h : p.Valid) {k : ℕ} {r u v m H ε ε₁ R : ℝ}
    (hat : p.AtDepth k r R) (hr : 0 ≤ r) (s : p.ComparedSample k r u v m H)
    (F : p.FieldReady k s (p.N k ^ (-(r + (1 - p.d) * u / 2))) ε₁)
    (hKH : p.K k ≤ H) (hε₁ : ε₁ ≤ ε) (hε₁0 : 0 ≤ ε₁)
    (hlaw : p.K k ≤ p.N k ^ ε)
    (hcoef : 40 * p.K k ^ 2 * p.N k ^ ε₁ ≤ p.N k ^ ε)
    (hbg : 40 * p.K k ^ 2 * p.N k ^ ε₁ * ((2 : ℝ) ^ p.T k r * (p.N k ^ (-p.ℓ * r))⁻¹) ^ 2 ≤
      p.N k ^ (m / 10))
    (hframe : 6 * p.K k * (2 : ℝ) ^ p.T k r ≤ p.N k ^ (m / 10))
    (hfieldnum : 2 * p.K k ^ 2 * (p.N k ^ ε₁ * p.N k ^ (-(r + (1 - p.d) * u / 2))) ≤
      p.N k ^ (-r - v))
    (hvarnum : 5832 * p.N k ^ (m / 1000) * p.K k ^ 6 * p.N k ^ (-m) ≤ p.N k ^ (-r - v))
    (hσK : 3 * p.K k ^ 2 * p.N k ^ (-m) ≤ 1)
    (hcard : 2000 * H ^ 11 ≤ p.N k ^ ε) :
    Nonempty (p.ListFrame k r v m ε) := by
  classical
  have hN2 : 2 ≤ p.N k := h.scale k
  have hN : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := by linarith
  have hK1 : 1 ≤ p.K k := h.subpower.1 k
  have hK0 : 0 < p.K k := by linarith
  obtain ⟨hbmeas, hνprob, -, hμ, hρμ, -, -, hPdeg, -, hnative⟩ := h.basic k
  obtain ⟨hAm, hBm, hBA, hν0, hc, hgeo⟩ := atDepth_block p hat hN hK0 F.block
  have hq0 : 0 < p.blockLen k r := blockLen_pos p k r
  have hq1 : p.blockLen k r ≤ 1 := blockLen_le_one p k r
  have hg0 : 0 < p.N k ^ (-p.ℓ * r) := Real.rpow_pos_of_pos hN _
  have hg1 : p.N k ^ (-p.ℓ * r) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1
    have := h.transverse_pos
    nlinarith
  have hw0 : 0 < p.blockWidth k r := mul_pos hq0 hg0
  have hσ0 : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have hσ1 : p.N k ^ (-m) ≤ 1 := by
    have h3 : (1 : ℝ) ≤ 3 * p.K k ^ 2 := by nlinarith
    nlinarith
  have hwt0 : p.blockWeight k r F.block ≠ 0 := by
    unfold Parent.blockWeight
    exact mul_ne_zero (by simpa using hq0) hν0
  have hwttop : p.blockWeight k r F.block ≠ ⊤ := by
    unfold Parent.blockWeight
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  -- almost sure facts on the field submeasure
  have hFμ : F.law ≤ p.μ k := F.le_law.trans (s.le_rho.trans hρμ)
  have hacμ : F.law ≪ p.μ k := Measure.absolutelyContinuous_of_le hFμ
  have hacs : F.law ≪ s.law := Measure.absolutelyContinuous_of_le F.le_law
  have hnat : ∀ᵐ ω ∂F.law, ∀ t ∈ Icc (0 : ℝ) 1, |p.signal k ω.1 t| ≤ p.K k :=
    hacμ.ae_le (hnative.mono fun ω hω t ht => (hω.1 t ht).1)
  have hcov : ∀ᵐ ω ∂F.law, ∃ e, ω ∈ s.event 1 e := hacs.ae_le (s.event_cover 1)
  have hdyμ : ∀ᵐ ω ∂p.μ k, ω.2 ∉ dyadicTimes (p.T k r) := by
    rw [ae_iff]
    have hset : {ω : α × ℝ | ¬ω.2 ∉ dyadicTimes (p.T k r)} =
        (univ : Set α) ×ˢ dyadicTimes (p.T k r) := by
      ext ω
      simp
    rw [hset]
    apply le_antisymm _ zero_le
    calc p.μ k ((univ : Set α) ×ˢ dyadicTimes (p.T k r))
        ≤ (ENNReal.ofReal (p.K k) • (p.ν k).prod volume)
            ((univ : Set α) ×ˢ dyadicTimes (p.T k r)) := hμ _
      _ = 0 := by
          rw [Measure.smul_apply, Measure.prod_prod,
            (countable_dyadicTimes (p.T k r)).measure_zero, mul_zero, smul_zero]
  have hdy : ∀ᵐ ω ∂F.law, ω.2 ∉ dyadicTimes (p.T k r) := hacμ.ae_le hdyμ
  have hsupp := F.support
  have hgoodF : ∀ᵐ ω ∂F.law, ω.1 ∈ frameGood p k r F.block F.C ε := by
    filter_upwards [hsupp, hnat] with ω hs hn
    refine ⟨hs.1, ?_⟩
    have hb3 : |p.b k ω.1 3| ≤ p.K k := by
      have := hs.2.2.2
      linarith [abs_nonneg (p.b k ω.1 0), abs_nonneg (p.b k ω.1 1), abs_nonneg (p.b k ω.1 4)]
    have hB1 : 1 ≤ p.N k ^ ε₁ := Real.one_le_rpow hN1 hε₁0
    intro i
    refine (abs_rawCoeff_le p hK1 F.C_bound hB1 hN hc hb3 (hgeo ω.1 (hBA hs.1))
      (fun t ht => hn t (mem_unit_of_mem_block p ht)) i).trans hcoef
  -- the frame
  have hlawdom : normLaw (p.blockStart k r F.block) (p.blockLen k r) (p.blockWeight k r F.block)
      F.law ≤ ENNReal.ofReal (p.N k ^ ε) •
        (condPrior (p.ν k) (p.A k r F.block)).prod volume := by
    have hsuppA : ∀ᵐ ω ∂F.law, ω.1 ∈ p.A k r F.block := by
      filter_upwards [hsupp] with ω hs
      exact hBA hs.1
    refine (normLaw_domination hq0 hμ hFμ hsuppA).trans ?_
    exact IsOrderedSMul.smul_le_smul_right _ _ (ENNReal.ofReal_le_ofReal hlaw) _
  have htime : normLaw (p.blockStart k r F.block) (p.blockLen k r) (p.blockWeight k r F.block)
      F.law (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
    apply normLaw_time_support hq0
    filter_upwards [hsupp] with ω hs
    have := hs.2.1
    rwa [block_eq_Icc] at this
  have hmass : ENNReal.ofReal (p.N k ^ (-ε)) ≤ normLaw (p.blockStart k r F.block)
      (p.blockLen k r) (p.blockWeight k r F.block) F.law univ := by
    rw [normLaw_univ]
    have h1 : ENNReal.ofReal (p.N k ^ (-ε)) ≤ ENNReal.ofReal (p.N k ^ (-ε₁)) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
    calc ENNReal.ofReal (p.N k ^ (-ε)) ≤ ENNReal.ofReal (p.N k ^ (-ε₁)) := h1
      _ = (p.blockWeight k r F.block)⁻¹ *
            (ENNReal.ofReal (p.N k ^ (-ε₁)) * p.blockWeight k r F.block) := by
          rw [mul_comm (ENNReal.ofReal _), ← mul_assoc, ENNReal.inv_mul_cancel hwt0 hwttop,
            one_mul]
      _ ≤ (p.blockWeight k r F.block)⁻¹ * F.law univ := by
          gcongr
          exact F.mass_lower
  have ht₀ : |p.blockStart k r F.block| ≤ 1 := by
    rw [abs_of_nonneg (blockStart_nonneg p k r F.block)]
    linarith [blockStart_add_le p k r F.block]
  have hqinv : (p.blockLen k r)⁻¹ = (2 : ℝ) ^ p.T k r := by
    unfold Parent.blockLen
    rw [inv_inv]
  have hwinv : (p.blockWidth k r)⁻¹ = (2 : ℝ) ^ p.T k r * (p.N k ^ (-p.ℓ * r))⁻¹ := by
    unfold Parent.blockWidth
    rw [mul_inv, hqinv]
  have hbgbound : (∑ e ∈ (bgPoly (p.blockStart k r F.block) (p.blockLen k r) (p.blockWidth k r)
      (p.c k r F.block) F.C).support,
      |(bgPoly (p.blockStart k r F.block) (p.blockLen k r) (p.blockWidth k r)
        (p.c k r F.block) F.C).coeff e|) ≤ p.N k ^ (m / 10) := by
    have hqw : (p.blockLen k r)⁻¹ ≤ (p.blockWidth k r)⁻¹ := by
      apply inv_anti₀ hw0
      unfold Parent.blockWidth
      exact mul_le_of_le_one_right hq0.le hg1
    have hq1' : 1 ≤ (p.blockLen k r)⁻¹ := (one_le_inv₀ hq0).mpr hq1
    have := coeffL1_bgPoly_le hq0 hw0 hqw hq1' ht₀ hK1 hc F.C_bound
    rw [hwinv] at this
    exact this.trans hbg
  have hframebound : 1 + |(p.blockLen k r)⁻¹| * (2 + |p.blockStart k r F.block| +
      |p.c k r F.block 0| + |p.c k r F.block 1|) ≤ p.N k ^ (m / 10) := by
    rw [hqinv, abs_of_pos (by positivity)]
    have hT1 : (1 : ℝ) ≤ 2 ^ p.T k r := one_le_pow₀ (by norm_num)
    have e1 := hc 0
    have e2 := hc 1
    have e3 : (2 : ℝ) ^ p.T k r * (2 + |p.blockStart k r F.block| + |p.c k r F.block 0| +
        |p.c k r F.block 1|) ≤ 2 ^ p.T k r * (3 + 2 * p.K k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have e4 : (1 : ℝ) ≤ p.K k * 2 ^ p.T k r := by nlinarith
    nlinarith
  refine ⟨{
    parent := F.block
    t₀ := p.blockStart k r F.block
    q := p.blockLen k r
    z₀ := p.c k r F.block 0
    zv := p.c k r F.block 1
    background := bgPoly (p.blockStart k r F.block) (p.blockLen k r) (p.blockWidth k r)
      (p.c k r F.block) F.C
    prior := condPrior (p.ν k) (p.A k r F.block)
    law := normLaw (p.blockStart k r F.block) (p.blockLen k r) (p.blockWeight k r F.block) F.law
    coeff := frameCoeff p k r F.block F.C ε
    good := frameGood p k r F.block F.C ε
    good_measurable := measurableSet_frameGood p hbmeas hBm F.C ε
    good_subset := Set.inter_subset_left
    coeff_measurable := measurable_frameCoeff p hbmeas hBm F.C ε
    prior_probability := condPrior_prob _ hν0 (measure_ne_top _ _)
    law_domination := hlawdom
    time_support := htime
    good_ae := ae_normLaw hq0.ne' _ (P := fun ω => ω.1 ∈ frameGood p k r F.block F.C ε) hgoodF
    coeff_bound := frameCoeff_bound p hN
    mass_lower := hmass
    q_pos := hq0
    q_eq := rfl
    time_eq := block_eq_Icc p k r F.block
    background_degree := totalDegree_bgPoly _ _ _ _ _
    background_bound := hbgbound
    frame_bound := hframebound
    scalarY_eq := ?_
    scalarX_eq := ?_
    original_domination := ?_
    lists := frameLists p k s F.block
    lists_bound := ?_
    lists_ae := ?_ }⟩
  · intro l hl u
    rw [frameCoeff_of_mem p hl, scalarY_rawCoeff]
  · intro l hl u
    rw [frameCoeff_of_mem p hl, scalarX_rawCoeff p hPdeg]
    rfl
  · show p.blockWeight k r F.block • _ ≤ _
    rw [normLaw_pushback hq0.ne' hwt0 hwttop F.law]
    exact F.le_law.trans s.le_rho
  · intro a
    calc _ ≤ 2000 * H ^ 11 * p.N k ^ (p.d * v) := frameLists_card p k s F.block hN hK1 hKH hσ1 a
      _ ≤ p.N k ^ ε * p.N k ^ (p.d * v) :=
          mul_le_mul_of_nonneg_right hcard (Real.rpow_pos_of_pos hN _).le
  · apply ae_normLaw hq0.ne' _ (P := fun ω =>
      (scalarCell (frameCoeff p k r F.block F.C ε ω.1) ω.2 (p.N k ^ (-m)),
        ⌊scalarX (frameCoeff p k r F.block F.C ε ω.1) ω.2 / p.N k ^ (-r - v)⌋) ∈
        frameLists p k s F.block ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋)
    filter_upwards [hsupp, hcov, hdy, F.field, hgoodF] with ω hs hcv hd hf hg
    obtain ⟨l, t⟩ := ω
    obtain ⟨e, he⟩ := hcv
    simp only [normTime]
    rw [frameCoeff_of_mem p hg]
    have hpar : s.parent 1 e = F.block := by
      obtain ⟨-, hB', ht', -⟩ := s.event_data 1 e (l, t) he
      exact block_eq_of_mem hat.2.2.2.1 ((hat.2.2.1 (s.parent 1 e)).2.2 hB') (hBA hs.1) ht'
        hs.2.1 hd
    have htt : p.blockStart k r F.block +
        p.blockLen k r * ((t - p.blockStart k r F.block) / p.blockLen k r) = t := by
      field_simp
      ring
    have hcell : scalarCell (rawCoeff p k r F.block F.C l)
        ((t - p.blockStart k r F.block) / p.blockLen k r) (p.N k ^ (-m)) =
        ![⌊((t - p.blockStart k r F.block) / p.blockLen k r) / p.N k ^ (-m)⌋,
          ⌊p.zetaN k r F.block (l, t) / p.N k ^ (-m)⌋] := by
      have hY := scalarY_rawCoeff p k r F.block F.C l
        ((t - p.blockStart k r F.block) / p.blockLen k r)
      rw [htt] at hY
      simp only [scalarY] at hY
      simp only [scalarCell, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCell, hY]
      rfl
    have hX : scalarX (rawCoeff p k r F.block F.C l)
        ((t - p.blockStart k r F.block) / p.blockLen k r) =
        p.signal k l t - eval (p.base k l t) (bgPoly (p.blockStart k r F.block) (p.blockLen k r)
          (p.blockWidth k r) (p.c k r F.block) F.C) := by
      rw [scalarX_rawCoeff p hPdeg]
      unfold resid
      rw [htt]
    rw [hcell, hX]
    obtain ⟨hζ, hU⟩ := hgeo l (hBA hs.1) t hs.2.1
    exact mem_frameLists p k s F.block F.C hN hK1 hKH hc hfieldnum hvarnum hσK hs.2.1 hs.2.2
      hζ hU he hpar hf

end Parent.FieldFrame

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
