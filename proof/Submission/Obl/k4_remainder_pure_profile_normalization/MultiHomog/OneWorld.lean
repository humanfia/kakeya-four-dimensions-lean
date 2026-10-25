import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Bounds

/-!
# The encoded world satisfies the hypotheses of single-world homogenization

At one sample, the encoded prior and event satisfy every per-sample condition of
`Submission.Obl.k4_joint_homogenization.Format`, with format exponent `Me`, the same
degree bound, and slack `2K + 6`.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set Filter
open scoped ENNReal

namespace Sample

variable {S : Sample}

/-- The format exponent of the encoded world. -/
def Me (S : Sample) : ℕ := 11 * S.M + 12 * S.M₀ + 18

namespace Hyp

variable (h : S.Hyp)
include h

theorem pow_le_Me {n : ℕ} (hn : n ≤ S.Me) : S.N ^ n ≤ S.N ^ S.Me :=
  pow_le_pow_right₀ h.one_le_N hn

theorem prior_isProb {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B) :
    IsProbabilityMeasure S.prior := by
  have := hT.prob
  constructor
  rw [Sample.prior, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  have : ∀ γ, (S.ν γ).map (S.enc γ) univ = 1 := fun γ => by
    rw [Measure.map_apply (measurable_enc γ) MeasurableSet.univ, preimage_univ, measure_univ]
  simp only [this, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => h.ω_nonneg γ), hT.weight_sum, ENNReal.ofReal_one]

/-- The density factor of the encoded prior pieces is polynomially bounded. -/
theorem coeff_bound (γ : Fin S.W) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ S.N ^ S.M) :
    S.ω γ * (c * |(S.a * S.b γ * S.θ γ) ^ 2|⁻¹) ≤ S.N ^ S.Me := by
  set P : ℝ := S.N ^ S.mL * S.N ^ (4 * S.M₀ + S.M + 3) * S.N ^ (3 * S.M + 2) with hP
  have hPpos : 0 < P := by have := h.N_pos; positivity
  have hlow : P⁻¹ ≤ S.a * S.b γ * S.θ γ := by
    rw [hP, mul_inv, mul_inv]
    have h1 := h.a_ge
    have h2 := h.b_ge γ
    have h3 := h.θ_ge γ
    have := h.N_pos
    apply mul_le_mul (mul_le_mul h1 h2 (by positivity) h.a_pos.le) h3 (by positivity)
    exact (mul_pos h.a_pos (h.b_pos γ)).le
  have habθ : 0 < S.a * S.b γ * S.θ γ := mul_pos (mul_pos h.a_pos (h.b_pos γ)) (h.θ_pos γ)
  have hsq : |(S.a * S.b γ * S.θ γ) ^ 2|⁻¹ ≤ P ^ 2 := by
    rw [abs_of_pos (pow_pos habθ 2)]
    rw [inv_le_comm₀ (pow_pos habθ 2) (pow_pos hPpos 2), ← inv_pow]
    exact pow_le_pow_left₀ (inv_pos.mpr hPpos).le hlow 2
  have hexp : S.N ^ S.M * P ^ 2 = S.N ^ S.Me := by
    rw [hP, ← pow_add, ← pow_add, ← pow_mul, ← pow_add]
    congr 1
    unfold Sample.Me Sample.mL
    ring
  calc S.ω γ * (c * |(S.a * S.b γ * S.θ γ) ^ 2|⁻¹) ≤ 1 * (S.N ^ S.M * P ^ 2) := by
        apply mul_le_mul (h.ω_le γ) _ (by positivity) zero_le_one
        exact mul_le_mul hc hsq (by positivity) (h.pow_pos' _).le
    _ = S.N ^ S.Me := by rw [one_mul, hexp]

theorem index_bound (γ : Fin S.W) {i : ℕ} (hi : (i : ℝ) ≤ S.N ^ S.M) :
    (encIdx S.W γ i : ℝ) ≤ S.N ^ S.Me := by
  have h1 := encIdx_le γ i
  have hW := h.W_le
  have hNM := h.one_le_pow S.M
  have h2 : (S.W : ℝ) * (i + 1) ≤ S.N ^ S.M * (2 * S.N ^ S.M) := by
    apply mul_le_mul hW (by linarith) (by positivity) (h.pow_pos' _).le
  have h3 : S.N ^ S.M * (2 * S.N ^ S.M) ≤ S.N ^ (2 * S.M + 1) := by
    have : S.N ^ (2 * S.M + 1) = S.N ^ S.M * S.N ^ S.M * S.N := by
      rw [← pow_add, ← pow_succ]; ring_nf
    rw [this]
    have := h.N_ge
    nlinarith [h.pow_pos' S.M]
  exact h1.trans (h2.trans (h3.trans (h.pow_le_Me (by unfold Sample.Me; omega))))

/-- The encoded prior is a polynomially bounded piecewise Lebesgue measure. -/
theorem prior_pieces {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B) :
    ∃ m : ℕ, (m : ℝ) ≤ S.N ^ S.Me ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ)
      (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ S.N ^ S.Me ∧
        (i j : ℝ) ≤ S.N ^ S.Me ∧ fmt 6 (S.N ^ S.Me) D (A j) ∧
        (∀ x ∈ A j, ∀ b, |x b| ≤ S.N ^ S.Me)) ∧
      S.prior = ∑ j, ENNReal.ofReal (c j) •
        Measure.map (fun x => (i j, x)) (volume.restrict (A j)) := by
  choose m hm c i A hA hν using hT.prior
  have hprior : S.prior = ∑ γ, ENNReal.ofReal (S.ω γ) • ∑ j, ENNReal.ofReal
      (c γ j * |(S.a * S.b γ * S.θ γ) ^ 2|⁻¹) •
        Measure.map (fun x => (encIdx S.W γ (i γ j), x))
          (volume.restrict {x | decCoeff S.a (S.b γ) (S.θ γ) (S.o γ) x ∈ A γ j}) := by
    unfold Sample.prior
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [hν γ]
    congr 1
    exact map_encLine_prior γ h.a_ne (h.b_ne γ) (h.θ_ne γ) (S.o γ) (c γ)
      (fun j => (hA γ j).1) (i γ) (A γ)
  rw [hprior, mixture_reindex m S.ω h.ω_nonneg _ _ _]
  refine ⟨∑ γ, m γ, ?_, _, _, _, fun J => ?_, rfl⟩
  · have hsum : ((∑ γ, m γ : ℕ) : ℝ) ≤ ∑ _γ : Fin S.W, S.N ^ S.M := by
      push_cast
      exact Finset.sum_le_sum fun γ _ => hm γ
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have h2 : (S.W : ℝ) * S.N ^ S.M ≤ S.N ^ (2 * S.M) := by
      rw [two_mul, pow_add]
      exact mul_le_mul_of_nonneg_right h.W_le (h.pow_pos' _).le
    exact hsum.trans (h2.trans (h.pow_le_Me (by unfold Sample.Me; omega)))
  · set γ := (finSigmaFinEquiv.symm J).1
    set j := (finSigmaFinEquiv.symm J).2
    obtain ⟨hc0, hc, hi, hfmt, hbdd⟩ := hA γ j
    refine ⟨mul_nonneg (h.ω_nonneg γ) (mul_nonneg hc0 (by positivity)),
      h.coeff_bound γ hc0 hc, h.index_bound γ hi, ?_, ?_⟩
    · have := fmt_diagAffine hfmt (fun j => (encDiag S.a (S.b γ) (S.θ γ) j)⁻¹)
        (fun j => -(encShift (S.o γ) j / encDiag S.a (S.b γ) (S.θ γ) j))
      rw [← decCoeff_eq_diagAffine] at this
      exact fmt_mono this (h.pow_le_Me (by unfold Sample.Me; omega)) le_rfl
    · intro z hz e
      have hz' := hbdd _ hz e
      have := h.abs_encCoeff_le γ (decCoeff S.a (S.b γ) (S.θ γ) (S.o γ) z) e
      rw [h.enc_dec] at this
      have h1 := h.one_le_pow S.M
      have h2 : S.N ^ S.M + 1 ≤ S.N ^ (S.M + 1) := by
        rw [pow_succ]; nlinarith [h.N_ge]
      linarith [h.pow_le_Me (n := S.M + 1) (by unfold Sample.Me; omega)]

omit h in
theorem event_time {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B) :
    S.event ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  rintro p ⟨γ, -, -, hmem⟩
  exact ⟨mem_univ _, (hT.event_time γ hmem).2⟩

theorem event_bdd {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B) :
    ∀ p ∈ S.event, (p.1.1 : ℝ) ≤ S.N ^ S.Me ∧ ∀ e, |p.1.2 e| ≤ S.N ^ S.Me := by
  rintro p ⟨γ, -, hmod, hmem⟩
  obtain ⟨h1, h2⟩ := hT.event_bdd γ _ hmem
  have hW : 0 < S.W := h.W_ge
  constructor
  · have hdecomp : p.1.1 = encIdx S.W γ (p.1.1 / S.W) := by
      unfold encIdx
      rw [← hmod]
      exact (Nat.mod_add_div _ _).symm
    rw [hdecomp]
    exact h.index_bound γ h1
  · intro e
    have := h.abs_encCoeff_le γ (decCoeff S.a (S.b γ) (S.θ γ) (S.o γ) p.1.2) e
    rw [h.enc_dec] at this
    have h1' := h.one_le_pow S.M
    have h2' : S.N ^ S.M + 1 ≤ S.N ^ (S.M + 1) := by
      rw [pow_succ]; nlinarith [h.N_ge]
    have := h2 e
    linarith [h.pow_le_Me (n := S.M + 1) (by unfold Sample.Me; omega)]

theorem event_fmt {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B) (n : ℕ) :
    fmt 7 (S.N ^ S.Me) D {x : Fin 7 → ℝ | ((n, fun j : Fin 6 => x j.castSucc), x 6) ∈ S.event} := by
  have hW : 0 < S.W := h.W_ge
  set γ₀ : Fin S.W := ⟨n % S.W, Nat.mod_lt _ hW⟩
  have huniq : ∀ γ : Fin S.W, n % S.W = (γ : ℕ) → γ = γ₀ := fun γ hγ => Fin.ext hγ.symm
  by_cases hR : S.Retained γ₀
  · have hset : {x : Fin 7 → ℝ | ((n, fun j : Fin 6 => x j.castSucc), x 6) ∈ S.event} =
        {x : Fin 7 → ℝ | ((n / S.W, decCoeff S.a (S.b γ₀) (S.θ γ₀) (S.o γ₀)
          (fun j : Fin 6 => x j.castSucc)), x 6) ∈ S.E γ₀} := by
      ext x
      constructor
      · rintro ⟨γ, -, hmod, hmem⟩
        have := huniq γ hmod
        subst this
        exact hmem
      · intro hx
        exact ⟨γ₀, hR, rfl, hx⟩
    rw [hset, decCoeff_eq_diagAffine]
    exact fmt_mono (fmt_slice_diagAffine (hT.event_fmt γ₀ (n / S.W)) _ _)
      (h.pow_le_Me (by unfold Sample.Me; omega)) le_rfl
  · have hset : {x : Fin 7 → ℝ | ((n, fun j : Fin 6 => x j.castSucc), x 6) ∈ S.event} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨γ, hγ, hmod, -⟩
      have := huniq γ hmod
      subst this
      exact hR hγ
    rw [hset]
    exact fmt_empty (h.pow_pos' _).le D

/-- Almost every encoded trajectory has coefficients at most one. -/
theorem prior_ae_coeff {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B) :
    ∀ᵐ l ∂S.prior, ∀ e, |l.2 e| ≤ 1 := by
  have hS : MeasurableSet {l : Trajectory | ¬ ∀ e, |l.2 e| ≤ 1} := by
    have : {l : Trajectory | ¬ ∀ e, |l.2 e| ≤ 1} = ⋃ e : Fin 6, {l : Trajectory | 1 < |l.2 e|} := by
      ext l; simp [not_forall, not_le]
    rw [this]
    refine MeasurableSet.iUnion fun e => measurableSet_lt measurable_const ?_
    exact (continuous_abs.measurable.comp ((measurable_pi_apply e).comp measurable_snd))
  rw [ae_iff, Sample.prior, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun γ _ => ?_
  rw [Measure.smul_apply, Measure.map_apply (measurable_enc γ) hS]
  have hnull : S.ν γ {l | ¬ S.GoodLine l} = 0 := by
    have := ae_goodLine hT γ
    rwa [ae_iff] at this
  have hsub : S.enc γ ⁻¹' {l : Trajectory | ¬ ∀ e, |l.2 e| ≤ 1} ⊆ {l | ¬ S.GoodLine l} := by
    intro l hl hgood
    exact hl (fun e => h.enc_coeff_le_one γ hgood e)
  rw [measure_mono_null hsub hnull, smul_zero]

theorem prior_ae_bound {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B) :
    ∀ᵐ l ∂S.prior, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1,
        ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2] :
          EuclideanSpace ℝ (Fin 2))‖ +
        ‖(WithLp.toLp 2 ![l.2 3, l.2 4] : EuclideanSpace ℝ (Fin 2))‖ ≤ 2 * S.K + 6 ∧
      |![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 3| ≤ 2 * S.K + 6 := by
  filter_upwards [h.prior_ae_coeff hT] with l hl t ht
  have hK := h.K_ge
  have ht0 := ht.1
  have ht1 := ht.2
  have hlin : ∀ e e' : Fin 6, |l.2 e + t * l.2 e'| ≤ 2 := by
    intro e e'
    calc |l.2 e + t * l.2 e'| ≤ |l.2 e| + |t * l.2 e'| := abs_add_le _ _
      _ = |l.2 e| + t * |l.2 e'| := by rw [abs_mul, abs_of_nonneg ht0]
      _ ≤ 1 + 1 * 1 := by
        gcongr
        · exact hl e
        · exact hl e'
      _ = 2 := by norm_num
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three, Matrix.cons_val_zero]
  constructor
  · have n1 := norm_toLp_two_le (l.2 0 + t * l.2 3) (l.2 1 + t * l.2 4)
    have n2 := norm_toLp_two_le (l.2 3) (l.2 4)
    have := hlin 0 3
    have := hlin 1 4
    have := hl 3
    have := hl 4
    linarith
  · have := hlin 2 5
    linarith

/-- The encoded event retains at least half of the selected mass. -/
theorem coverage {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B) :
    ENNReal.ofReal ((2 * S.K + 6)⁻¹) ≤ ((S.prior.prod volume).restrict S.event) univ := by
  have := hT.prob
  have hK := h.K_pos
  rw [Measure.restrict_apply_univ, prior_prod_apply (measurableSet_event hT.event_meas)]
  simp only [h.preimage_encInc_event]
  set A := ∑ γ, ENNReal.ofReal (S.ω γ) * ((S.ν γ).prod volume) ({_p | S.Retained γ} ∩ S.E γ)
  set B := ∑ γ, ENNReal.ofReal (S.ω γ) * ((S.ν γ).prod volume) ({_p | ¬ S.Retained γ} ∩ S.E γ)
  have hAB : ∑ γ, ENNReal.ofReal (S.ω γ) * ((S.ν γ).prod volume) (S.E γ) = A + B := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← mul_add]
    congr 1
    by_cases hγ : S.Retained γ <;> simp [hγ]
  have hunit : ∀ γ, ((S.ν γ).prod volume) (S.E γ) ≤ 1 := fun γ => by
    calc ((S.ν γ).prod volume) (S.E γ) ≤ ((S.ν γ).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) :=
          measure_mono (hT.event_time γ)
      _ = 1 := by simp
  have hB : B ≤ ENNReal.ofReal ((2 * S.K)⁻¹) := by
    calc B ≤ ∑ _γ : Fin S.W, ENNReal.ofReal S.thr := by
          refine Finset.sum_le_sum fun γ _ => ?_
          by_cases hγ : S.Retained γ
          · simp [hγ]
          · simp only [hγ, not_false_eq_true, ofPred_true, univ_inter]
            calc ENNReal.ofReal (S.ω γ) * ((S.ν γ).prod volume) (S.E γ)
                ≤ ENNReal.ofReal S.thr * 1 := by
                  gcongr
                  · exact (not_le.mp hγ).le
                  · exact hunit γ
              _ = ENNReal.ofReal S.thr := mul_one _
      _ = ENNReal.ofReal (S.W * S.thr) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((2 * S.K)⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          unfold Sample.thr
          rw [mul_inv, mul_inv, ← mul_assoc]
          have hNM := h.pow_pos' S.M
          have : (S.W : ℝ) * (S.N ^ S.M)⁻¹ ≤ 1 := by
            rw [mul_inv_le_iff₀ hNM, one_mul]; exact h.W_le
          calc (S.W : ℝ) * ((2 : ℝ)⁻¹ * S.K⁻¹) * (S.N ^ S.M)⁻¹
              = ((S.W : ℝ) * (S.N ^ S.M)⁻¹) * ((2 : ℝ)⁻¹ * S.K⁻¹) := by ring
            _ ≤ 1 * ((2 : ℝ)⁻¹ * S.K⁻¹) := by
                apply mul_le_mul_of_nonneg_right this; positivity
            _ = (2 : ℝ)⁻¹ * S.K⁻¹ := one_mul _
  have hmass := hT.mass
  rw [hAB] at hmass
  have hhalf : ENNReal.ofReal (S.K⁻¹) = ENNReal.ofReal ((2 * S.K)⁻¹) + ENNReal.ofReal ((2 * S.K)⁻¹) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have hA : ENNReal.ofReal ((2 * S.K)⁻¹) ≤ A := by
    have h1 : ENNReal.ofReal ((2 * S.K)⁻¹) + ENNReal.ofReal ((2 * S.K)⁻¹) ≤
        A + ENNReal.ofReal ((2 * S.K)⁻¹) := by
      rw [← hhalf]
      exact hmass.trans (add_le_add le_rfl hB)
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h1
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hA
  apply inv_anti₀ (by positivity)
  linarith

end Hyp

end Sample

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
