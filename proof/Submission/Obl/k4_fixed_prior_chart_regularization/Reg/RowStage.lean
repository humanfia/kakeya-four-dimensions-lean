-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/Reg/RowStage.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.RowStep
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.LocalStage

/-!
# Stage 2: the row comparison at all scales

Paper §9: "Iterate at all tested scales, upper bounds persisting under restriction, to obtain the
comparison `K(|t-t'| + ζ)` using slow grids." The tested scales are `r_k = N^(-c k/J)`,
`k ≤ J`, with `c/J ≤ ε/4`, and the comparison factor is `Λ = N^(ε/4)`. Each scale costs
`m ↦ m²/12` in mass (`row_scale_step`), so after the `J + 1` scales the mass is
`mseq (J+1) = 12 (N^(-η)/12)^(2^(J+1))`, still `≥ N^(-ε)` for `η` small against `2^(-J)`.
Two retained times at distance `q ∈ [r_(k+1), r_k]` compare at scale `r_k ≤ N^(c/J) q`
(`exists_scale_above`); at distance `≤ ζ` they compare at the finest scale.
-/

open MeasureTheory Set Filter

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.Reg

/-- Every distance in `[N^(-c), 1]` lies below a grid scale at most `N^(c/J)` times larger. -/
theorem exists_scale_above {N c q : ℝ} {J : ℕ} (hN : 1 ≤ N) (hJ : 0 < J) (hc : 0 < c)
    (hq : N ^ (-c) ≤ q) (hq1 : q ≤ 1) :
    ∃ k : ℕ, k ≤ J ∧ q ≤ N ^ (-(c * k / J)) ∧ N ^ (-(c * k / J)) ≤ N ^ (c / J) * q := by
  have hN0 : 0 < N := by linarith
  have hone : 1 ≤ N ^ (c / J) := Real.one_le_rpow hN (by positivity)
  obtain ⟨k, hkJ, h1, h2⟩ := exists_grid_width hN hJ hc hq hq1
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.rpow_zero] at h1 h2 ⊢
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.rpow_zero]; exact hq1
    · simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.rpow_zero]; nlinarith
  · have e : N ^ (-(c * ((k - 1 : ℕ) : ℝ) / J)) = N ^ (c / J) * N ^ (-(c * k / J)) := by
      rw [← Real.rpow_add hN0]
      congr 1
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      field_simp
      ring
    refine ⟨k - 1, by omega, ?_, ?_⟩
    · rw [e]; exact h2
    · rw [e]; exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The mass after `k` scales. -/
def mseq (a : ℝ) (k : ℕ) : ℝ := 12 * (a / 12) ^ (2 ^ k)

theorem mseq_succ (a : ℝ) (k : ℕ) : mseq a (k + 1) = mseq a k ^ 2 / 12 := by
  simp only [mseq, pow_succ, pow_mul]
  ring

theorem mseq_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ mseq a k := by
  unfold mseq; positivity

theorem mseq_anti {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) {k k' : ℕ} (hk : k ≤ k') :
    mseq a k' ≤ mseq a k := by
  unfold mseq
  have h1 : a / 12 ≤ 1 := by linarith
  have h2 : (a / 12) ^ (2 ^ k') ≤ (a / 12) ^ (2 ^ k) :=
    pow_le_pow_of_le_one (by positivity) h1 (Nat.pow_le_pow_right (by norm_num) hk)
  linarith

set_option maxHeartbeats 4000000 in
/-- **Stage 2**: the row comparison. -/
theorem stageRow : StageRow := by
  intro d hd hd1 c hc ε hε
  set J : ℕ := ⌈4 * c / ε⌉₊ + 1 with hJ_def
  have hJ : 0 < J := Nat.succ_pos _
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hcJ : c / J ≤ ε / 4 := by
    have h1 : 4 * c / ε ≤ (⌈4 * c / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (J : ℝ) = (⌈4 * c / ε⌉₊ : ℝ) + 1 := by rw [hJ_def]; push_cast; ring
    rw [div_le_iff₀ hJ']
    rw [div_le_iff₀ hε] at h1
    nlinarith
  set P : ℕ := 2 ^ (J + 1) with hP_def
  have hP1 : (1 : ℝ) ≤ P := by
    have : 1 ≤ P := Nat.one_le_two_pow
    exact_mod_cast this
  have hd1' : 0 < 1 - d := by linarith
  set η : ℝ := ε * (1 - d) / (8 * (9 + P)) with hη_def
  have hη : 0 < η := by positivity
  have hηP : η * (9 + P) = ε * (1 - d) / 8 := by
    rw [hη_def]; field_simp
  have hηε : η ≤ ε := by
    rw [hη_def, div_le_iff₀ (by positivity)]
    nlinarith
  have hηP' : η * P < ε := by
    have : η * P ≤ η * (9 + P) := by nlinarith
    rw [hηP] at this
    nlinarith
  -- eventual inequalities
  have hev1 := JetFit.eventually_mul_rpow_le (10240 * 12 ^ P) (x := η * (9 + P))
    (y := ε / 4 * (1 - d)) (by rw [hηP]; nlinarith)
  have hev2 := JetFit.eventually_mul_rpow_le (12 ^ P) (x := η * P) (y := ε) hηP'
  have hev3 := JetFit.eventually_mul_rpow_le 2 (x := ε / 2) (y := ε) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((hev1.and hev2).and hev3)
  refine ⟨η, hη, hηε, max N₁ 2, le_max_right _ _, ?_⟩
  intro N hN Ω _ ν hν y β γ E F hU hL
  have hN1 : 1 ≤ N := le_trans (by norm_num) ((le_max_right _ _).trans hN)
  have hN0 : 0 < N := by linarith
  obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hN₁ N ((le_max_left _ _).trans hN)
  set K : ℝ := N ^ η with hK_def
  have hK1 : 1 ≤ K := Real.one_le_rpow hN1 hη.le
  have hK0 : 0 < K := by linarith
  set ζ : ℝ := N ^ (-c) with hζ_def
  have hζ : 0 < ζ := Real.rpow_pos_of_pos hN0 _
  set a : ℝ := N ^ (-η) with ha_def
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have haK : a = K⁻¹ := by rw [ha_def, hK_def, Real.rpow_neg hN0.le]
  set Λ : ℝ := N ^ (ε / 4) with hΛ_def
  have hΛ1 : 1 ≤ Λ := Real.one_le_rpow hN1 (by positivity)
  set rs : ℕ → ℝ := fun k => N ^ (-(c * k / J)) with hrs_def
  have hrs : ∀ k, k ≤ J → ζ ≤ rs k ∧ rs k ≤ 1 := by
    intro k hk
    have hkJ : (k : ℝ) ≤ J := by exact_mod_cast hk
    constructor
    · apply Real.rpow_le_rpow_of_exponent_le hN1
      have : c * k / J ≤ c := by rw [div_le_iff₀ hJ']; nlinarith
      linarith
    · apply Real.rpow_le_one_of_one_le_of_nonpos hN1
      have : 0 ≤ c * k / J := by positivity
      linarith
  -- the scale condition at the smallest mass
  have hBJ : 61440 * K ^ 9 * Λ ^ (d - 1) ≤ mseq a J ^ 2 / 24 := by
    have hm2 : mseq a J ^ 2 = 144 * (a ^ P / 12 ^ P) := by
      simp only [mseq, hP_def, pow_succ, pow_mul, div_pow]; ring
    have haP : a ^ P = N ^ (-(η * P)) := by
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have hK9 : K ^ 9 = N ^ (9 * η) := by
      rw [hK_def, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have hΛd : Λ ^ (d - 1) = N ^ (-(ε / 4 * (1 - d))) := by
      rw [hΛ_def, ← Real.rpow_mul hN0.le]; ring_nf
    rw [hm2, haP, hK9, hΛd]
    have h12 : (0 : ℝ) < 12 ^ P := by positivity
    -- from `10240 · 12^P · N^(η(9+P)) ≤ N^(ε/4 (1-d))`
    have e1 : N ^ (η * (9 + P)) = N ^ (9 * η) * N ^ (η * P) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have e2 : N ^ (-(η * P)) * N ^ (η * P) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    have e3 : N ^ (-(ε / 4 * (1 - d))) * N ^ (ε / 4 * (1 - d)) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    have hpos1 : 0 < N ^ (η * P) := Real.rpow_pos_of_pos hN0 _
    have hpos2 : 0 < N ^ (ε / 4 * (1 - d)) := Real.rpow_pos_of_pos hN0 _
    have hpos3 : 0 < N ^ (9 * η) := Real.rpow_pos_of_pos hN0 _
    rw [e1] at hc1
    have hx : N ^ (-(η * P)) = (N ^ (η * P))⁻¹ := Real.rpow_neg hN0.le _
    have hy : N ^ (-(ε / 4 * (1 - d))) = (N ^ (ε / 4 * (1 - d)))⁻¹ := Real.rpow_neg hN0.le _
    rw [hx, hy]
    have hrhs : 144 * ((N ^ (η * (P : ℝ)))⁻¹ / 12 ^ P) / 24 = 6 / (N ^ (η * P) * 12 ^ P) := by
      field_simp; ring
    rw [hrhs, le_div_iff₀ (by positivity)]
    calc 61440 * N ^ (9 * η) * (N ^ (ε / 4 * (1 - d)))⁻¹ * (N ^ (η * P) * 12 ^ P)
        = 6 * (10240 * 12 ^ P * (N ^ (9 * η) * N ^ (η * P))) *
            (N ^ (ε / 4 * (1 - d)))⁻¹ := by ring
      _ ≤ 6 * N ^ (ε / 4 * (1 - d)) * (N ^ (ε / 4 * (1 - d)))⁻¹ := by gcongr
      _ = 6 := by field_simp
  -- the iteration
  have hind : ∀ k : ℕ, k ≤ J + 1 → ∃ G : Set (Ω × ℝ), G ⊆ E ∧ MeasurableSet G ∧
      ENNReal.ofReal (mseq a k) ≤ (ν.prod volume) G ∧ ∀ k' < k, ∀ t u,
        (∃ l, (l, t) ∈ G) → (∃ l, (l, u) ∈ G) → |t - u| ≤ rs k' → ∀ i,
          |F t i - F u i| ≤ 2 * Λ * rs k' := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨E, subset_refl _, hU.measurableSet_E, ?_, fun k' hk' => absurd hk' (by omega)⟩
      have : mseq a 0 ≤ K⁻¹ := by
        simp only [mseq, pow_zero, pow_one]; rw [haK]; field_simp; rfl
      exact (ENNReal.ofReal_le_ofReal this).trans hU.mass
    | succ k ih =>
      intro hk
      obtain ⟨G, hGE, hGm, hGmass, hGcomp⟩ := ih (by omega)
      obtain ⟨hr1, hr2⟩ := hrs k (by omega)
      have hBk : 61440 * K ^ 9 * Λ ^ (d - 1) ≤ mseq a k ^ 2 / 24 := by
        refine hBJ.trans ?_
        have := mseq_anti ha0.le ha1 (show k ≤ J by omega)
        have h0 := mseq_nonneg ha0.le J
        have : mseq a J ^ 2 ≤ mseq a k ^ 2 := pow_le_pow_left₀ h0 this 2
        linarith
      obtain ⟨G', hG'G, hG'm, hG'mass, hG'comp⟩ := row_scale_step hU hL hK1 hζ hd hd1 G hGm
        hGE (rs k) Λ (mseq a k) hr1 hr2 hΛ1 (mseq_nonneg ha0.le k) hGmass hBk
      refine ⟨G', hG'G.trans hGE, hG'm, ?_, ?_⟩
      · rw [mseq_succ]; exact hG'mass
      · intro k' hk' t u ⟨l, hl⟩ ⟨l', hl'⟩ htu i
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | heq
        · exact hGcomp k' hlt t u ⟨l, hG'G hl⟩ ⟨l', hG'G hl'⟩ htu i
        · subst heq; exact hG'comp t u ⟨l, hl⟩ ⟨l', hl'⟩ htu i
  obtain ⟨G, hGE, hGm, hGmass, hGcomp⟩ := hind (J + 1) le_rfl
  -- the final mass
  have hmass : ENNReal.ofReal (N ^ ε)⁻¹ ≤ (ν.prod volume) G := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hGmass
    have hm : mseq a (J + 1) = 12 * (N ^ (-(η * P)) / 12 ^ P) := by
      simp only [mseq, hP_def, div_pow]
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    rw [hm]
    have hε0 : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 _
    have hx : N ^ (-(η * P)) = (N ^ (η * P))⁻¹ := by
      rw [Real.rpow_neg hN0.le]
    rw [hx]
    have hpos1 : 0 < N ^ (η * P) := Real.rpow_pos_of_pos hN0 _
    have h12 : (0 : ℝ) < 12 ^ P := by positivity
    rw [inv_le_iff_one_le_mul₀ hε0]
    field_simp
    nlinarith [hc2]
  refine ⟨G, hGE, ?_, ?_⟩
  · have hle : K ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 hηε
    exact (hU.mono_bound hK0 hle hζ.le).restrict_labels hGm hGE hmass
  · -- the comparison
    have hΛc : 2 * Λ * N ^ (c / J) ≤ N ^ ε := by
      have : 2 * Λ * N ^ (c / J) ≤ 2 * N ^ (ε / 2) := by
        rw [hΛ_def, mul_assoc, ← Real.rpow_add hN0]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      linarith
    have hone : 1 ≤ N ^ (c / J) := Real.one_le_rpow hN1 (by positivity)
    rintro t u ⟨l, hl⟩ ⟨l', hl'⟩ i
    have ht := (hU.subset_E (hGE hl)).2
    have hu := (hU.subset_E (hGE hl')).2
    have hq1 : |t - u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
    have hεpos : 0 ≤ N ^ ε := (Real.rpow_pos_of_pos hN0 _).le
    by_cases hqζ : |t - u| ≤ ζ
    · -- the finest scale
      have hJζ : rs J = ζ := by
        simp only [hrs_def, hζ_def]; congr 1; field_simp
      have h := hGcomp J (by omega) t u ⟨l, hl⟩ ⟨l', hl'⟩ (by rw [hJζ]; exact hqζ) i
      rw [hJζ] at h
      calc |F t i - F u i| ≤ 2 * Λ * ζ := h
        _ ≤ N ^ ε * ζ := by
            apply mul_le_mul_of_nonneg_right _ hζ.le
            nlinarith
        _ ≤ N ^ ε * (|t - u| + ζ) := by
            apply mul_le_mul_of_nonneg_left _ hεpos
            linarith [abs_nonneg (t - u)]
    · push Not at hqζ
      obtain ⟨k, hkJ, hk1, hk2⟩ := exists_scale_above hN1 hJ hc hqζ.le hq1
      have h := hGcomp k (by omega) t u ⟨l, hl⟩ ⟨l', hl'⟩ hk1 i
      calc |F t i - F u i| ≤ 2 * Λ * rs k := h
        _ ≤ 2 * Λ * (N ^ (c / J) * |t - u|) := by
            apply mul_le_mul_of_nonneg_left hk2 (by positivity)
        _ = (2 * Λ * N ^ (c / J)) * |t - u| := by ring
        _ ≤ N ^ ε * |t - u| := mul_le_mul_of_nonneg_right hΛc (abs_nonneg _)
        _ ≤ N ^ ε * (|t - u| + ζ) := by
            apply mul_le_mul_of_nonneg_left _ hεpos
            linarith

end Submission.Obl.k4_fixed_prior_chart_regularization.Reg

end
