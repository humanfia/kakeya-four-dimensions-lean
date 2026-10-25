import Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing.NumericStep
import Submission.Obl.k4_subcritical_endpoint_native_pairing.FrozenCaps

/-! The two endpoint depths `s₀` and `3 s₀ / 2`. One simultaneous endpoint call
at a loss `ε₁` much smaller than the final loss gives both endpoint families
on one law; the comparison is applied at the first depth, and then at the
second depth on the retained law. Floors stay those of the original residual. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_subcritical_endpoint_native_pairing.Data

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The auxiliary loss exponent. -/
def auxLoss (s₀ ε η d : ℝ) : ℝ :=
  min (s₀ / 2) (ε * min (1 / 2) (min (η / (20 + η)) ((1 - d) / 14)))

theorem auxLoss_spec {s₀ ε η d : ℝ} (hs₀ : 0 < s₀) (hε : 0 < ε) (hη : 0 < η)
    (hd : d < 1) :
    0 < auxLoss s₀ ε η d ∧ auxLoss s₀ ε η d < ε ∧ auxLoss s₀ ε η d < s₀ ∧
      11 * auxLoss s₀ ε η d < η * (ε - auxLoss s₀ ε η d) ∧
      7 * auxLoss s₀ ε η d < (1 - d) * ε := by
  set m := min (1 / 2 : ℝ) (min (η / (20 + η)) ((1 - d) / 14)) with hm
  have hd' : 0 < 1 - d := by linarith
  have hm1 : m ≤ 1 / 2 := min_le_left _ _
  have hm2 : m ≤ η / (20 + η) := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : m ≤ (1 - d) / 14 := (min_le_right _ _).trans (min_le_right _ _)
  have hmpos : 0 < m := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hx : auxLoss s₀ ε η d ≤ ε * m := min_le_right _ _
  have hxs : auxLoss s₀ ε η d ≤ s₀ / 2 := min_le_left _ _
  have hxpos : 0 < auxLoss s₀ ε η d := lt_min (by linarith) (by positivity)
  refine ⟨hxpos, ?_, by linarith, ?_, ?_⟩
  · nlinarith
  · -- 11x < η(ε - x) ⟸ x ≤ εη/(20+η)
    have h1 : ε * m * (20 + η) ≤ ε * η := by
      have := mul_le_mul_of_nonneg_left hm2 hε.le
      rw [mul_div_assoc'] at this
      have h20 : (0 : ℝ) < 20 + η := by linarith
      calc ε * m * (20 + η) ≤ ε * η / (20 + η) * (20 + η) :=
            mul_le_mul_of_nonneg_right this h20.le
        _ = ε * η := by field_simp
    nlinarith
  · have := mul_le_mul_of_nonneg_left hm3 hε.le
    nlinarith

theorem paired_ready (hM : Matching) (h : cfg.Prepared) {M sMax RE s₀ : ℝ}
    (hM0 : 0 < M) (hMe : M < cfg.e₀) (hE : cfg.EndpointWith M sMax RE)
    (hs₀ : 0 < s₀) (hsMax : 3 * s₀ / 2 < sMax) (h100 : 100 * s₀ < M) :
    cfg.PairedReady M RE s₀ := by
  obtain ⟨η, hη, R₀, hR₀, HB⟩ := comparison_bound hM h.dimension_nonneg h.dimension_lt_one
  intro ε hε
  obtain ⟨hε₁, hε₁ε, hε₁s, hgain, hlist⟩ :=
    auxLoss_spec (d := cfg.d) hs₀ hε hη h.dimension_lt_one
  set ε₁ := auxLoss s₀ ε η cfg.d with hε₁def
  let depth : Fin 2 → ℝ := ![s₀, 3 * s₀ / 2]
  have hκ := h.rate_pos
  have hκ2 := h.subcritical_rate
  have hd0 : depth 0 = s₀ := rfl
  have hd1 : depth 1 = 3 * s₀ / 2 := rfl
  have hdepth : ∀ r, 0 < depth r ∧ depth r < sMax := by
    intro r; fin_cases r
    · exact ⟨hs₀, by simp [depth]; linarith⟩
    · exact ⟨by simp [depth]; linarith, by simp [depth]; linarith⟩
  have hsU : sMax < cfg.U := by linarith [hE.2.1, hE.1]
  have hdepthU : ∀ r, depth r ≤ cfg.U := fun r => ((hdepth r).2.trans hsU).le
  have hdepthM : ∀ r, depth r + 2 * cfg.κ * depth r < M := by
    intro r
    have hlo : depth r ≤ 3 * s₀ / 2 := by fin_cases r <;> simp [depth] <;> linarith
    have hpos := (hdepth r).1
    nlinarith
  have hε₁d : ∀ r, ε₁ < depth r := by
    intro r
    have hlo : s₀ ≤ depth r := by fin_cases r <;> simp [depth] <;> linarith
    linarith
  -- Eventual inputs.
  have hlev := eventually_endpoint_levels hE 2 depth hdepth hε₁
  have hnat : ∀ᶠ k in atTop, ∀ r, Nonempty (cfg.NativeLevel k (depth r)) :=
    Filter.eventually_all.mpr fun r => h.eventually_native_level (hdepth r).1 (hdepthU r)
  have hnum : ∀ᶠ k in atTop, ∀ r, DepthNumerics cfg k (depth r) M ε ε₁ η R₀ :=
    Filter.eventually_all.mpr fun r => eventually_depthNumerics h (hdepth r).1 (hdepthM r)
      hε₁ hε₁ε (hε₁d r) hη hgain hlist
  have hcaps := h.eventually_original_joint_caps (r := M + 1) (M := M) (by linarith) hM0
  have hfinal : ∀ᶠ k in atTop, 2 * cfg.N k ^ (-ε) < cfg.N k ^ (-ε₁) := by
    have := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
      h.scale_limit (show -ε < -ε₁ by linarith) 2
    exact this
  filter_upwards [hlev, hnat, hnum, hcaps, hfinal] with k hlevk hnatk hnumk hcapsk hfinalk
  obtain ⟨ρH, hρH, hmassH, H, hcovH⟩ := hlevk
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have na : ∀ r, cfg.NativeLevel k (depth r) := fun r => (hnatk r).some
  have hgood : ∀ r, ∀ᵐ p ∂cfg.μ k,
      p.1 ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)) :=
    fun r => (na r).original_good_lines_ae h hMe.le
  have hphys : PhysicalCaps cfg k M (cfg.N k ^ (-(M + 1))) := hcapsk
  haveI : IsFiniteMeasure (cfg.ρ k) :=
    ⟨(residual_mass_le h k).trans_lt ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure ρH := isFiniteMeasure_of_le (cfg.ρ k) hρH
  have hpow : 0 < cfg.N k ^ (-ε₁) := Real.rpow_pos_of_pos hN _
  -- The first depth on the endpoint law.
  have hmass₀ : ENNReal.ofReal (cfg.N k ^ (-ε₁) / 2) ≤ ρH univ :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hmassH
  obtain ⟨ξ₀, hξ₀, hloss₀, L₀, hL₀card, hL₀⟩ := numeric_step h HB (hdepth 0).1.le hε₁.le
    ρH hρH (H 0) (hcovH.mono fun p hp => hp 0) (na 0) (hgood 0) hphys (hnumk 0) hmass₀
  have hξ₀mass : ENNReal.ofReal (cfg.N k ^ (-ε₁) - cfg.N k ^ (-ε₁) / 4) ≤ ξ₀ univ :=
    ofReal_sub_le_of_le_add (by linarith) (by linarith) (hmassH.trans hloss₀)
  -- The second depth on the retained law.
  haveI : IsFiniteMeasure ξ₀ := isFiniteMeasure_of_le ρH hξ₀
  have hmass₁ : ENNReal.ofReal (cfg.N k ^ (-ε₁) / 2) ≤ ξ₀ univ :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hξ₀mass
  obtain ⟨ξ₁, hξ₁, hloss₁, L₁, hL₁card, hL₁⟩ := numeric_step h HB (hdepth 1).1.le hε₁.le
    ξ₀ (hξ₀.trans hρH) (H 1) (ae_mono hξ₀ (hcovH.mono fun p hp => hp 1)) (na 1) (hgood 1)
    hphys (hnumk 1) hmass₁
  have hξ₁mass : ENNReal.ofReal (cfg.N k ^ (-ε₁) - cfg.N k ^ (-ε₁) / 4 -
      cfg.N k ^ (-ε₁) / 4) ≤ ξ₁ univ :=
    ofReal_sub_le_of_le_add (by linarith) (by linarith) (hξ₀mass.trans hloss₁)
  -- Both depths on the final law.
  have hall : ∀ r : Fin 2, ∃ L : Fin (H r).count × ℕ →
      Finset (Fin (cfg.n k (depth r)) × ℤ × ℤ × ℤ),
      (∀ x, ((L x).card : ℝ) ≤ cfg.N k ^ ε) ∧
      ∀ᵐ ω ∂ξ₁, ∃ (hh : Fin (H r).count) (i : Fin (cfg.n k (depth r))),
        ω.1 ∈ (H r).A hh ∧ ω.1 ∈ cfg.B k (depth r) i ∧
        ω.2 ∈ I (cfg.T k (depth r)) (cfg.j k (depth r) i) ∧
        (∃ e ∈ L (hh, (cfg.j k (depth r) i : ℕ)), e.1 = i) ∧
        ∀ t ∈ I (cfg.T k (depth r)) (cfg.j k (depth r) i),
        ∀ p ∈ Icc (((H r).tag hh 1 : ℝ) * cfg.parameterWidth k (depth r))
          ((((H r).tag hh 1 : ℝ) + 1) * cfg.parameterWidth k (depth r)),
        ∀ q ∈ Icc (((H r).tag hh 2 : ℝ) * cfg.parameterWidth k (depth r))
          ((((H r).tag hh 2 : ℝ) + 1) * cfg.parameterWidth k (depth r)),
          |cfg.nativeParameter k (depth r) i (((H r).tag hh 0 : ℝ) * cfg.N k ^ (-M)) t p q -
            predictor ((H r).coeff hh) t p q| ≤ cfg.N k ^ ε * cfg.N k ^ (-depth r) := by
    intro r
    fin_cases r
    · exact ⟨L₀, hL₀card, ae_mono hξ₁ hL₀⟩
    · exact ⟨L₁, hL₁card, hL₁⟩
  choose L hLcard hL using hall
  -- The paired relation: listed and compared on whole boxes.
  let paired : (r : Fin 2) → Fin (H r).count → Fin (cfg.n k (depth r)) → Prop :=
    fun r hh i => (∃ e ∈ L r (hh, (cfg.j k (depth r) i : ℕ)), e.1 = i) ∧
      ∀ t ∈ I (cfg.T k (depth r)) (cfg.j k (depth r) i),
      ∀ p ∈ Icc (((H r).tag hh 1 : ℝ) * cfg.N k ^ (-2 * cfg.κ * depth r))
        ((((H r).tag hh 1 : ℝ) + 1) * cfg.N k ^ (-2 * cfg.κ * depth r)),
      ∀ q ∈ Icc (((H r).tag hh 2 : ℝ) * cfg.N k ^ (-2 * cfg.κ * depth r))
        ((((H r).tag hh 2 : ℝ) + 1) * cfg.N k ^ (-2 * cfg.κ * depth r)),
        |cfg.nativeParameter k (depth r) i (((H r).tag hh 0 : ℝ) * cfg.N k ^ (-M)) t p q -
          predictor ((H r).coeff hh) t p q| ≤ cfg.N k ^ ε * cfg.N k ^ (-depth r)
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hpowle : cfg.N k ^ ε₁ ≤ cfg.N k ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN1 hε₁ε.le
  refine ⟨ξ₁, fun r => (H r).count, fun r => (H r).A, fun r => (H r).tag,
    fun r => (H r).coeff, paired, hξ₁.trans (hξ₀.trans hρH), ?_, ?_, ?_⟩
  · -- final mass
    refine le_trans ?_ hξ₁mass
    apply ENNReal.ofReal_le_ofReal
    linarith
  · intro r
    refine ⟨(H r).measurable, fun hh hh' hne => (H r).disjoint hne, fun hh => ?_,
      fun hh i hp => hp.2, fun hh j₀ => ?_⟩
    · refine ⟨(H r).bins hh, (H r).coefficient_bound hh, ?_, ?_, ?_⟩
      · intro t ht p hp q hq
        exact ((H r).norm_bound hh t ht p hp q hq).trans hpowle
      · intro l hl t ht
        have hf := (H r).fit hh l hl t ht
        unfold hiddenWidth at hf
        exact hf.trans (mul_le_mul_of_nonneg_right hpowle (Real.rpow_pos_of_pos hN _).le)
      · refine le_trans ?_ ((H r).floor hh)
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        apply ENNReal.ofReal_le_ofReal
        unfold parameterWidth hiddenWidth
        have hD : 0 ≤ (cfg.N k ^ (-2 * cfg.κ * depth r)) ^ 2 *
            (cfg.N k ^ (-depth r)) ^ cfg.d := by
          have := Real.rpow_pos_of_pos hN (-2 * cfg.κ * depth r)
          have := Real.rpow_pos_of_pos hN (-depth r)
          positivity
        exact div_le_div_of_nonneg_left hD (Real.rpow_pos_of_pos hN _) hpowle
    · -- the native lists
      have hsub : {i : Fin (cfg.n k (depth r)) | paired r hh i ∧ cfg.j k (depth r) i = j₀} ⊆
          ↑((L r (hh, (j₀ : ℕ))).image Prod.fst) := by
        intro i hi
        obtain ⟨⟨e, he, hei⟩, -⟩ := hi.1
        rw [hi.2] at he
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨e, he, hei⟩)
      calc (Set.ncard {i : Fin (cfg.n k (depth r)) |
            paired r hh i ∧ cfg.j k (depth r) i = j₀} : ℝ)
          ≤ (Set.ncard (↑((L r (hh, (j₀ : ℕ))).image Prod.fst) :
              Set (Fin (cfg.n k (depth r)))) : ℝ) := by
            exact_mod_cast Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = (((L r (hh, (j₀ : ℕ))).image Prod.fst).card : ℝ) := by
            rw [Set.ncard_coe_finset]
        _ ≤ ((L r (hh, (j₀ : ℕ))).card : ℝ) := by exact_mod_cast Finset.card_image_le
        _ ≤ _ := hLcard r _
  · filter_upwards [ae_all_iff.mpr hL] with ω hω r
    obtain ⟨hh, i, h1, h2, h3, h4, h5⟩ := hω r
    exact ⟨hh, i, h1, h2, h3, h4, h5⟩

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing
