-- Adapted from LOT tree g-oai-074, obligation o245, session x0854, commit 3602b8f657fd9f9293587a9dd3e1bdba2451d373.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/RegSlope/Main.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope.Scale
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.Stages

/-!
# Slope regularization: the stage

`stageSlope : Reg.StageSlope`. On a finite grid of widths `s_k = N^(-c_k)` from `N^(-c_top)`
(`c_top = min (ε/2) c`) down to `ζ = N^(-c)`, consecutive ratios `≤ N^(ε/2)`:
long labels, pair durations and heavy codes at every width (`scale_codes`), heavy entries at
every width, then one slope bin per cube and a residue class of cubes, width after width
(`select_bin_class`, at most `(2K + 9) K K₃` bins per cube by `cube_bins`). Two retained
incidences within `s_k` in every coordinate share their slope bin at width `s_k`
(`slope_of_sep`).
-/

open MeasureTheory Set Filter

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

open FirstJet Submission.Obl.k4_scalar_coefficient_clustering

/-- For `α < β` and any `C`, eventually `C N^α ≤ N^β`. -/
theorem ev_rpow (C α β : ℝ) (h : α < β) : ∀ᶠ N : ℝ in atTop, C * N ^ α ≤ N ^ β := by
  have ht : Tendsto (fun N : ℝ => N ^ (β - α)) atTop atTop := tendsto_rpow_atTop (by linarith)
  filter_upwards [ht.eventually_ge_atTop C, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  have e : N ^ β = N ^ (β - α) * N ^ α := by rw [← Real.rpow_add hN0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)

/-- Slope comparison from shared slope bins on a grid of widths. -/
theorem slope_of_sep {Ω : Type*} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {A : Set (Ω × ℝ)}
    {K K' ζ Q : ℝ} {M : ℕ} {s : ℕ → ℝ} (hγ : ∀ l, |γ l| ≤ K) (hs0 : ∀ k, 0 < s k)
    (hsM : s M = ζ) (hstep : ∀ k < M, s k ≤ Q * s (k + 1)) (hQ : Q ≤ K') (hK'1 : 1 ≤ K')
    (htop : 2 * K ≤ K' * s 0)
    (hsep : ∀ k ≤ M, ∀ p ∈ A, ∀ p' ∈ A,
      (∀ i, |cube (s k) y β γ p i - cube (s k) y β γ p' i| ≤ 1) →
        ⌊γ p.1 / s k⌋ = ⌊γ p'.1 / s k⌋) :
    Reg.SlopeComparison y β γ A K' ζ := by
  intro l l' t u hl hl'
  set D := |t - u| + |xbar β γ l t - xbar β γ l' u| + |y l 0 - y l' 0| + |y l 1 - y l' 1|
    with hD
  have a1 := abs_nonneg (t - u)
  have a2 := abs_nonneg (xbar β γ l t - xbar β γ l' u)
  have a3 := abs_nonneg (y l 0 - y l' 0)
  have a4 := abs_nonneg (y l 1 - y l' 1)
  have hζ0 : 0 < ζ := hsM ▸ hs0 M
  have hK'0 : 0 ≤ K' := by linarith
  have hat : ∀ k ≤ M, D ≤ s k → |γ l - γ l'| < s k := by
    intro k hk hDk
    have hcube : ∀ i, |cube (s k) y β γ (l, t) i - cube (s k) y β γ (l', u) i| ≤ 1 := by
      intro i
      fin_cases i
      · exact floor_sub_le_one (hs0 k) (by linarith)
      · exact floor_sub_le_one (hs0 k) (by linarith)
      · exact floor_sub_le_one (hs0 k) (by linarith)
      · exact floor_sub_le_one (hs0 k) (by linarith)
    exact abs_sub_lt_of_floor_eq (hs0 k) (hsep k hk (l, t) hl (l', u) hl' hcube)
  by_cases hDM : D ≤ s M
  · have h := hat M le_rfl hDM
    rw [hsM] at h
    nlinarith
  push_neg at hDM
  by_cases hDtop : s 0 < D
  · have hγγ : |γ l - γ l'| ≤ 2 * K := by
      calc |γ l - γ l'| ≤ |γ l| + |γ l'| := abs_sub _ _
        _ ≤ 2 * K := by linarith [hγ l, hγ l']
    nlinarith
  push_neg at hDtop
  have hM0 : M ≠ 0 := by
    rintro rfl; linarith
  have hex : ∃ k, s (k + 1) < D := ⟨M - 1, by rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM0)]⟩
  classical
  set k₀ := Nat.find hex with hk₀
  have hk₀P : s (k₀ + 1) < D := Nat.find_spec hex
  have hk₀M : k₀ < M := by
    have := Nat.find_min' hex (show s (M - 1 + 1) < D by
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM0)])
    omega
  have hDk₀ : D ≤ s k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
    · rw [h0]; exact hDtop
    · have := Nat.find_min hex (show k₀ - 1 < k₀ by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  have h := hat k₀ hk₀M.le hDk₀
  have hs := hstep k₀ hk₀M
  have hQ0 : 0 ≤ Q := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg (hs0 (k₀ + 1))
    linarith [hs0 k₀]
  refine le_of_lt ?_
  calc |γ l - γ l'| < s k₀ := h
    _ ≤ Q * s (k₀ + 1) := hs
    _ ≤ Q * D := mul_le_mul_of_nonneg_left hk₀P.le hQ0
    _ ≤ K' * D := mul_le_mul_of_nonneg_right hQ (by linarith)
    _ ≤ K' * (D + ζ) := by nlinarith

set_option maxHeartbeats 1000000 in
/-- The slope stage at one large `N`. -/
theorem slope_at_N {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ}
    {d c ε η ε₂ N Q : ℝ} {M : ℕ} {ck ηc : ℕ → ℝ}
    (hU : UnregularizedChart ν y β γ E F d (N ^ η) (N ^ (-c))) (hd : 0 ≤ d) (hd1 : d < 1)
    (hN : 1 ≤ N) (hη0 : 0 < η) (hηε : η ≤ ε)
    (hHC : ∀ k ≤ M, HeavyCoverAt d (ck k) ε₂ (ηc k) N)
    (hsζ : ∀ k ≤ M, N ^ (-c) ≤ N ^ (-ck k)) (hs1 : ∀ k ≤ M, N ^ (-ck k) ≤ 1)
    (hsM : N ^ (-ck M) = N ^ (-c)) (hstep : ∀ k < M, N ^ (-ck k) ≤ Q * N ^ (-ck (k + 1)))
    (hQ : Q ≤ N ^ ε) (htop : 2 * N ^ η ≤ N ^ ε * N ^ (-ck 0))
    (n1 : ∀ k ≤ M, 2 * N ^ η ≤ N ^ ηc k)
    (n2 : ∀ k ≤ M, 4 * ((4 * N ^ η + 5) * N ^ η) / (N ^ (-η) / 8) ≤ N ^ ηc k)
    (n3 : ∀ k ≤ M, 2 * (16 * (M + 1) / N ^ (-η) * ((4 * N ^ η + 3) * N ^ η)) ≤ N ^ ηc k)
    (n4 : ∀ k ≤ M, (4 * N ^ η + 5) ^ 2 * N ^ (-ηc k) ≤ N ^ (-η) / (8 * (M + 1)))
    (n5 : (16 * ((2 * N ^ η + 9) * N ^ η * (16 * (M + 1) * N ^ ε₂ / N ^ (-η)) + 1)) ^ (M + 1) *
      N ^ (-ε) ≤ N ^ (-η) / 2) :
    ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧ UnregularizedChart ν y β γ E' F d (N ^ ε) (N ^ (-c)) ∧
      Reg.SlopeComparison y β γ E' (N ^ ε) (N ^ (-c)) := by
  classical
  have hN0 : 0 < N := by linarith
  set K := N ^ η with hKdef
  set m₀ := N ^ (-η) with hm₀def
  have hK0 : 0 < K := Real.rpow_pos_of_pos hN0 _
  have hm₀0 : 0 < m₀ := Real.rpow_pos_of_pos hN0 _
  have hKm : m₀ = K⁻¹ := by rw [hm₀def, hKdef, Real.rpow_neg hN0.le]
  set δ := m₀ / 8 with hδdef
  have hδ : 0 < δ := by positivity
  set K₂ := 16 * (M + 1) / m₀ with hK₂def
  have hK₂ : 0 < K₂ := by positivity
  set K₃ := 16 * (M + 1) * N ^ ε₂ / m₀ with hK₃def
  have hK₃ : 0 < K₃ := by have := Real.rpow_pos_of_pos hN0 ε₂; positivity
  set μ := ν.prod (volume : Measure ℝ) with hμ
  have hEm := hU.measurableSet_E
  set L := longLabels E δ with hLdef
  have hLm : MeasurableSet L := measurableSet_longLabels hEm δ
  set Ea := E ∩ L ×ˢ univ with hEadef
  have hEam : MeasurableSet Ea := hEm.inter (hLm.prod MeasurableSet.univ)
  have hs0 : ∀ k, 0 < N ^ (-ck k) := fun k => Real.rpow_pos_of_pos hN0 _
  -- heavy codes at every width
  have hC := fun k (hk : k ≤ M) => scale_codes hU hd hd1 hN0 (hHC k hk) (hsζ k hk) (hs1 k hk)
    hδ hK₂ (n1 k hk) (n2 k hk) (n3 k hk)
  choose! C hCm hCsub hCμ Ent hEnt hEntmem using hC
  set Ec := Ea ∩ ⋂ k ∈ Finset.range (M + 1), C k with hEcdef
  have hEcm : MeasurableSet Ec := hEam.inter (Finset.measurableSet_biInter _ fun k hk =>
    hCm k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  have hEcE : Ec ⊆ E := fun p hp => hp.1.1
  have hEcC : ∀ k ≤ M, Ec ⊆ C k := fun k hk p hp =>
    (mem_iInter₂.mp hp.2) k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  -- heavy entries at every width
  set φ : ℕ → ℝ := fun k => N ^ (-ck k) * ((N ^ (-ck k)) ^ 2 * (N ^ (-ck k)) ^ d) / K₃ with hφdef
  have hφ0 : ∀ k, 0 < φ k := fun k => by have := hs0 k; positivity
  set H : ℕ → Set (Ω × ℝ) := fun k =>
    heavyEntries μ Ec (N ^ (-ck k)) y β γ (ENNReal.ofReal (φ k)) with hHdef
  set Ed := Ec ∩ ⋂ k ∈ Finset.range (M + 1), H k with hEddef
  have hHm : ∀ k, MeasurableSet (H k) := fun k =>
    measurableSet_heavyEntries μ hEcm hU.measurable_y hU.measurable_β hU.measurable_γ _ _
  have hEdm : MeasurableSet Ed := hEcm.inter (Finset.measurableSet_biInter _ fun k _ => hHm k)
  have hEdH : ∀ k ≤ M, Ed ⊆ H k := fun k hk p hp =>
    (mem_iInter₂.mp hp.2) k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  -- the losses
  have hloss1 : μ (E \ Ea) ≤ ENNReal.ofReal δ := by
    have : E \ Ea = E ∩ Lᶜ ×ˢ univ := by
      ext p; simp only [hEadef, mem_diff, mem_inter_iff, mem_prod, mem_univ, and_true,
        mem_compl_iff]; tauto
    rw [this]; exact short_labels_mass hEm δ
  have hloss2 : μ (Ea \ Ec) ≤ ENNReal.ofReal ((M + 1) * (m₀ / (4 * (M + 1)))) := by
    calc μ (Ea \ Ec) ≤ μ (⋃ k ∈ Finset.range (M + 1), Ea \ C k) := by
          apply measure_mono
          rintro p ⟨hpa, hpc⟩
          simp only [hEcdef, mem_inter_iff, not_and, mem_iInter₂, not_forall] at hpc
          obtain ⟨k, hk, hpk⟩ := hpc hpa
          exact mem_biUnion hk ⟨hpa, hpk⟩
      _ ≤ ∑ k ∈ Finset.range (M + 1), μ (Ea \ C k) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ Finset.range (M + 1), ENNReal.ofReal (m₀ / (4 * (M + 1))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          refine (hCμ k hk').trans (ENNReal.ofReal_le_ofReal ?_)
          have e : 2 / K₂ = m₀ / (8 * (M + 1)) := by rw [hK₂def]; field_simp; ring
          rw [e]
          have := n4 k hk'
          have e2 : m₀ / (4 * (M + 1)) = m₀ / (8 * (M + 1)) + m₀ / (8 * (M + 1)) := by
            field_simp; ring
          linarith
      _ = ENNReal.ofReal ((M + 1) * (m₀ / (4 * (M + 1)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          push_cast; ring_nf
  have hloss3 : μ (Ec \ Ed) ≤ ENNReal.ofReal ((M + 1) * (m₀ / (8 * (M + 1)))) := by
    calc μ (Ec \ Ed) ≤ μ (⋃ k ∈ Finset.range (M + 1), Ec \ H k) := by
          apply measure_mono
          rintro p ⟨hpc, hpd⟩
          simp only [hEddef, mem_inter_iff, not_and, mem_iInter₂, not_forall] at hpd
          obtain ⟨k, hk, hpk⟩ := hpd hpc
          exact mem_biUnion hk ⟨hpc, hpk⟩
      _ ≤ ∑ k ∈ Finset.range (M + 1), μ (Ec \ H k) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ Finset.range (M + 1), ENNReal.ofReal (m₀ / (8 * (M + 1))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hsub : Ec \ H k = Ec ∩ {p | μ (Ec ∩ entry (N ^ (-ck k)) y β γ ⁻¹'
              {entry (N ^ (-ck k)) y β γ p}) < ENNReal.ofReal (φ k)} := by
            ext p
            simp only [hHdef, heavyEntries, mem_diff, mem_setOf_eq, mem_inter_iff, not_and,
              not_le]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨h1, h2 h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
          rw [hsub]
          refine (light_fibres_mass μ (Ent k) (fun p hp => hEntmem k hk' p (hEcC k hk' hp))
            _).trans ?_
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          set sk := N ^ (-ck k) with hsk
          have hsk0 : 0 < sk := hs0 k
          have hE := hEnt k hk'
          have hNe : N ^ (-ε₂) * N ^ ε₂ = 1 := by
            rw [← Real.rpow_add hN0]; simp
          have hNε : 0 < N ^ ε₂ := Real.rpow_pos_of_pos hN0 _
          calc ((Ent k).card : ℝ) * φ k
              = ((Ent k).card : ℝ) * (sk ^ 2 * (sk ^ d * N ^ (-ε₂))) * (sk * N ^ ε₂ / K₃) := by
                show ((Ent k).card : ℝ) * (sk * (sk ^ 2 * sk ^ d) / K₃) = _
                have : ((Ent k).card : ℝ) * (sk ^ 2 * (sk ^ d * N ^ (-ε₂))) * (sk * N ^ ε₂ / K₃) =
                    ((Ent k).card : ℝ) * (sk * (sk ^ 2 * sk ^ d) / K₃) * (N ^ (-ε₂) * N ^ ε₂) := by
                  ring
                rw [this, hNe, mul_one]
            _ ≤ (1 / sk + 1) * (sk * N ^ ε₂ / K₃) := by gcongr
            _ = (1 + sk) * N ^ ε₂ / K₃ := by field_simp
            _ ≤ 2 * N ^ ε₂ / K₃ := by
                gcongr; linarith [hs1 k hk']
            _ = m₀ / (8 * (M + 1)) := by rw [hK₃def]; field_simp; ring
      _ = ENNReal.ofReal ((M + 1) * (m₀ / (8 * (M + 1)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          push_cast; ring_nf
  have hEd : ENNReal.ofReal (m₀ / 2) ≤ μ Ed := by
    have hmass : ENNReal.ofReal m₀ ≤ μ E := by rw [hKm]; exact hU.mass
    have hsplit : μ E ≤ μ Ed + (μ (E \ Ea) + μ (Ea \ Ec) + μ (Ec \ Ed)) := by
      calc μ E ≤ μ (Ed ∪ ((E \ Ea) ∪ (Ea \ Ec) ∪ (Ec \ Ed))) := by
            apply measure_mono
            intro p hp
            by_cases h1 : p ∈ Ea
            · by_cases h2 : p ∈ Ec
              · by_cases h3 : p ∈ Ed
                · left; exact h3
                · right; right; exact ⟨h2, h3⟩
              · right; left; right; exact ⟨h1, h2⟩
            · right; left; left; exact ⟨hp, h1⟩
        _ ≤ μ Ed + μ ((E \ Ea) ∪ (Ea \ Ec) ∪ (Ec \ Ed)) := measure_union_le _ _
        _ ≤ μ Ed + (μ (E \ Ea) + μ (Ea \ Ec) + μ (Ec \ Ed)) := by
            gcongr
            exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    have hl : μ (E \ Ea) + μ (Ea \ Ec) + μ (Ec \ Ed) ≤ ENNReal.ofReal (m₀ / 2) := by
      have hM1 : (0 : ℝ) < M + 1 := by positivity
      calc μ (E \ Ea) + μ (Ea \ Ec) + μ (Ec \ Ed)
          ≤ ENNReal.ofReal δ + ENNReal.ofReal ((M + 1) * (m₀ / (4 * (M + 1)))) +
            ENNReal.ofReal ((M + 1) * (m₀ / (8 * (M + 1)))) := add_le_add (add_le_add hloss1 hloss2) hloss3
        _ = ENNReal.ofReal (m₀ / 2) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; rw [hδdef]; field_simp; ring
    have h := hmass.trans (hsplit.trans (add_le_add le_rfl hl))
    have e : ENNReal.ofReal m₀ = ENNReal.ofReal (m₀ / 2) + ENNReal.ofReal (m₀ / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    rw [e] at h
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h
  -- one slope bin per cube, width after width
  set P₀ : ℕ := ⌈(2 * K + 9) * K * K₃⌉₊ with hP₀def
  have hbins : ∀ k ≤ M, ∀ z, ∃ T : Finset ℤ, T.card ≤ P₀ ∧
      ∀ p ∈ Ed, cube (N ^ (-ck k)) y β γ p = z → ⌊γ p.1 / N ^ (-ck k)⌋ ∈ T := by
    intro k hk z
    obtain ⟨T, hT, hTmem⟩ := cube_bins (ν := ν) hU (hs0 k) (hsζ k hk) (hs1 k hk) hEcm hEcE
      (hφ0 k) z
    refine ⟨T, ?_, fun p hp hpz => hTmem p (hEdH k hk hp) hpz⟩
    have hsk := hs0 k
    have e : (2 * K + 9) * K * (N ^ (-ck k) * ((N ^ (-ck k)) ^ 2 * (N ^ (-ck k)) ^ d)) / φ k =
        (2 * K + 9) * K * K₃ := by
      simp only [hφdef]; field_simp
    rw [e] at hT
    exact_mod_cast hT.trans (Nat.le_ceil _)
  have hsel : ∀ n : ℕ, n ≤ M + 1 → ∃ A ⊆ Ed, MeasurableSet A ∧
      μ Ed ≤ ((16 * P₀ : ℕ) : ENNReal) ^ n * μ A ∧
      ∀ k < n, ∀ p ∈ A, ∀ p' ∈ A,
        (∀ i, |cube (N ^ (-ck k)) y β γ p i - cube (N ^ (-ck k)) y β γ p' i| ≤ 1) →
          ⌊γ p.1 / N ^ (-ck k)⌋ = ⌊γ p'.1 / N ^ (-ck k)⌋ := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨Ed, subset_rfl, hEdm, by simp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn
      obtain ⟨A, hAEd, hAm, hAμ, hAsep⟩ := ih (by omega)
      have hnM : n ≤ M := by omega
      obtain ⟨A', hA'A, hA'm, hA'μ, hA'sep⟩ := select_bin_class μ hAm
        (measurable_cube hU.measurable_y hU.measurable_β hU.measurable_γ (N ^ (-ck n)))
        (g := fun p => ⌊γ p.1 / N ^ (-ck n)⌋)
        (Int.measurable_floor.comp ((hU.measurable_γ.comp measurable_fst).div_const _)) P₀
        (fun z => by
          obtain ⟨T, hT, hTmem⟩ := hbins n hnM z
          exact ⟨T, hT, fun p hp hpz => hTmem p (hAEd hp) hpz⟩)
      refine ⟨A', hA'A.trans hAEd, hA'm, ?_, ?_⟩
      · calc μ Ed ≤ ((16 * P₀ : ℕ) : ENNReal) ^ n * μ A := hAμ
          _ ≤ ((16 * P₀ : ℕ) : ENNReal) ^ n * (16 * P₀ * μ A') := by gcongr
          _ = ((16 * P₀ : ℕ) : ENNReal) ^ (n + 1) * μ A' := by push_cast; ring
      · intro k hk p hp p' hp' hnear
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
        · exact hAsep k hk' p (hA'A hp) p' (hA'A hp') hnear
        · subst hk'; exact hA'sep p hp p' hp' hnear
  obtain ⟨E', hE'Ed, hE'm, hE'μ, hE'sep⟩ := hsel (M + 1) le_rfl
  have hE'E : E' ⊆ E := hE'Ed.trans fun p hp => hEcE hp.1
  -- the mass of `E'`
  have hP₀le : (P₀ : ℝ) ≤ (2 * K + 9) * K * K₃ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hP₀pos : 0 < P₀ := Nat.ceil_pos.mpr (by positivity)
  have hmass' : ENNReal.ofReal (N ^ ε)⁻¹ ≤ μ E' := by
    have hneg : (N ^ ε)⁻¹ = N ^ (-ε) := (Real.rpow_neg hN0.le ε).symm
    rw [hneg]
    set B : ENNReal := ((16 * P₀ : ℕ) : ENNReal) ^ (M + 1) with hB
    have hB0 : B ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : 16 * P₀ ≠ 0))
    have hBtop : B ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    have h1 : B * ENNReal.ofReal (N ^ (-ε)) ≤ ENNReal.ofReal (m₀ / 2) := by
      rw [show B = ENNReal.ofReal (((16 * P₀ : ℕ) : ℝ) ^ (M + 1)) by
          rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast],
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      refine le_trans ?_ n5
      push_cast
      have hNε : 0 ≤ N ^ (-ε) := Real.rpow_nonneg hN0.le _
      gcongr
    have h2 : B * ENNReal.ofReal (N ^ (-ε)) ≤ B * μ E' := h1.trans (hEd.trans hE'μ)
    exact (ENNReal.mul_le_mul_iff_right hB0 hBtop).mp h2
  refine ⟨E', hE'E, ?_, ?_⟩
  · exact (hU.mono_bound hK0 (Real.rpow_le_rpow_of_exponent_le hN hηε)
      (Real.rpow_nonneg hN0.le _)).restrict_labels hE'm hE'E hmass'
  · refine slope_of_sep (M := M) (s := fun k => N ^ (-ck k)) (Q := Q) (K := K) hU.bound_γ hs0
      hsM hstep hQ (Real.one_le_rpow hN (hη0.le.trans hηε)) htop ?_
    intro k hk p hp p' hp' hnear
    exact hE'sep k (Nat.lt_succ_of_le hk) p hp p' hp' hnear

theorem slope_numerics {N η ηm ηck : ℝ} {M : ℕ} (hN : 1 ≤ N) (hη : 0 < η) (hηm : ηm ≤ ηck)
    (e2 : 288 * N ^ (3 * η) ≤ N ^ ηm) (e3 : 648 * (M + 1) * N ^ (3 * η) ≤ N ^ ηm) :
    2 * N ^ η ≤ N ^ ηck ∧
    4 * ((4 * N ^ η + 5) * N ^ η) / (N ^ (-η) / 8) ≤ N ^ ηck ∧
    2 * (16 * (M + 1) / N ^ (-η) * ((4 * N ^ η + 3) * N ^ η)) ≤ N ^ ηck ∧
    (4 * N ^ η + 5) ^ 2 * N ^ (-ηck) ≤ N ^ (-η) / (8 * (M + 1)) := by
  have hN0 : 0 < N := by linarith
  set K := N ^ η with hK
  have hK1 : 1 ≤ K := Real.one_le_rpow hN hη.le
  have hK3 : N ^ (3 * η) = K ^ 3 := by
    rw [hK, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hKinv : N ^ (-η) = K⁻¹ := Real.rpow_neg hN0.le η
  have hmono : N ^ ηm ≤ N ^ ηck := Real.rpow_le_rpow_of_exponent_le hN hηm
  rw [hK3] at e2 e3
  have hK0 : 0 < K := by linarith
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [pow_le_pow_left₀ zero_le_one hK1 3, sq_nonneg K]
  · rw [hKinv]
    have e : 4 * ((4 * K + 5) * K) / (K⁻¹ / 8) = 32 * K ^ 2 * (4 * K + 5) := by
      field_simp; ring
    rw [e]
    nlinarith [pow_le_pow_left₀ zero_le_one hK1 2]
  · rw [hKinv]
    have e : 2 * (16 * (M + 1) / K⁻¹ * ((4 * K + 3) * K)) = 32 * (M + 1) * (K ^ 2 * (4 * K + 3)) := by
      field_simp; ring
    rw [e]
    have : K ^ 2 * (4 * K + 3) ≤ 7 * K ^ 3 := by nlinarith [sq_nonneg K]
    nlinarith
  · rw [hKinv, Real.rpow_neg hN0.le]
    have hNm : 0 < N ^ ηm := Real.rpow_pos_of_pos hN0 _
    have h1 : (4 * K + 5) ^ 2 ≤ 81 * K ^ 2 := by nlinarith
    have h2 : (N ^ ηck)⁻¹ ≤ (N ^ ηm)⁻¹ := inv_anti₀ hNm hmono
    have h3 : 81 * K ^ 2 / N ^ ηm ≤ 1 / (K * (8 * (M + 1))) := by
      rw [div_le_div_iff₀ hNm (by positivity)]
      have : 81 * K ^ 2 * (K * (8 * (M + 1))) = 648 * (M + 1) * K ^ 3 := by ring
      linarith
    calc (4 * K + 5) ^ 2 * (N ^ ηck)⁻¹ ≤ 81 * K ^ 2 * (N ^ ηm)⁻¹ :=
          mul_le_mul h1 h2 (inv_nonneg.mpr (Real.rpow_nonneg hN0.le _)) (by positivity)
      _ = 81 * K ^ 2 / N ^ ηm := by rw [div_eq_mul_inv]
      _ ≤ 1 / (K * (8 * (M + 1))) := h3
      _ = K⁻¹ / (8 * (M + 1)) := by field_simp

theorem slope_numerics5 {N η ε ε₂ : ℝ} {M : ℕ} (hN : 1 ≤ N) (hη : 0 < η) (hε₂ : 0 < ε₂)
    (e5 : 2 * (2832 * (M + 1)) ^ (M + 1) * N ^ ((M + 1) * (3 * η + ε₂)) ≤ N ^ (ε - η)) :
    (16 * ((2 * N ^ η + 9) * N ^ η * (16 * (M + 1) * N ^ ε₂ / N ^ (-η)) + 1)) ^ (M + 1) *
      N ^ (-ε) ≤ N ^ (-η) / 2 := by
  have hN0 : 0 < N := by linarith
  set K := N ^ η with hK
  have hK1 : 1 ≤ K := Real.one_le_rpow hN hη.le
  have hK0 : 0 < K := by linarith
  have hKinv : N ^ (-η) = K⁻¹ := Real.rpow_neg hN0.le η
  have hE1 : 1 ≤ N ^ ε₂ := Real.one_le_rpow hN hε₂.le
  have hM : (1 : ℝ) ≤ M + 1 := by have := Nat.cast_nonneg (α := ℝ) M; linarith
  have hbase : 16 * ((2 * K + 9) * K * (16 * (M + 1) * N ^ ε₂ / N ^ (-η)) + 1) ≤
      2832 * (M + 1) * N ^ (3 * η + ε₂) := by
    rw [hKinv, Real.rpow_add hN0]
    have hK3 : N ^ (3 * η) = K ^ 3 := by
      rw [hK, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    rw [hK3]
    have e : (2 * K + 9) * K * (16 * (M + 1) * N ^ ε₂ / K⁻¹) =
        16 * (M + 1) * N ^ ε₂ * (K ^ 2 * (2 * K + 9)) := by field_simp
    rw [e]
    have h1 : K ^ 2 * (2 * K + 9) ≤ 11 * K ^ 3 := by nlinarith [sq_nonneg K]
    have h2 : 1 ≤ (M + 1) * N ^ ε₂ * K ^ 3 := by
      have : 1 ≤ K ^ 3 := one_le_pow₀ hK1
      nlinarith [mul_le_mul hM hE1 zero_le_one (by linarith)]
    have h3 : 0 ≤ 16 * (M + 1) * N ^ ε₂ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h3]
  have hpow : (2832 * (M + 1) * N ^ (3 * η + ε₂)) ^ (M + 1) =
      (2832 * (M + 1)) ^ (M + 1) * N ^ ((M + 1) * (3 * η + ε₂)) := by
    rw [mul_pow, ← Real.rpow_natCast (N ^ (3 * η + ε₂)), ← Real.rpow_mul hN0.le]
    push_cast
    rw [mul_comm (3 * η + ε₂)]
  have hNε : 0 ≤ N ^ (-ε) := Real.rpow_nonneg hN0.le _
  have hb0 : 0 ≤ 16 * ((2 * K + 9) * K * (16 * (M + 1) * N ^ ε₂ / N ^ (-η)) + 1) := by
    have : 0 < N ^ (-η) := Real.rpow_pos_of_pos hN0 _
    positivity
  calc (16 * ((2 * K + 9) * K * (16 * (M + 1) * N ^ ε₂ / N ^ (-η)) + 1)) ^ (M + 1) * N ^ (-ε)
      ≤ (2832 * (M + 1) * N ^ (3 * η + ε₂)) ^ (M + 1) * N ^ (-ε) := by
        gcongr
    _ = (2832 * (M + 1)) ^ (M + 1) * N ^ ((M + 1) * (3 * η + ε₂)) * N ^ (-ε) := by rw [hpow]
    _ ≤ N ^ (ε - η) / 2 * N ^ (-ε) := by gcongr; linarith
    _ = N ^ (-η) / 2 := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hN0]; congr 2; ring

/-- **The slope stage of the chart regularization.** -/
theorem stageSlope : Reg.StageSlope := by
  intro d hd hd1 c hc ε hε
  set ct := min (ε / 2) c with hctdef
  have hct : 0 < ct := lt_min (by positivity) hc
  have hctc : ct ≤ c := min_le_right _ _
  have hctε : ct ≤ ε / 2 := min_le_left _ _
  set M : ℕ := ⌈2 * (c - ct) / ε⌉₊ + 1 with hMdef
  have hMpos : (0 : ℝ) < M := by rw [hMdef]; push_cast; positivity
  have hMge : 2 * (c - ct) / ε ≤ M := by
    rw [hMdef]; push_cast; linarith [Nat.le_ceil (2 * (c - ct) / ε)]
  set ck : ℕ → ℝ := fun k => ct + k * ((c - ct) / M) with hckdef
  have hgap0 : 0 ≤ (c - ct) / M := div_nonneg (by linarith) hMpos.le
  have hgap : (c - ct) / M ≤ ε / 2 := by
    rw [div_le_iff₀ hMpos]
    have := (div_le_iff₀ hε).mp hMge
    linarith
  have hckpos : ∀ k, 0 < ck k := fun k => by
    simp only [hckdef]; have := Nat.cast_nonneg (α := ℝ) k; positivity
  have hckle : ∀ k ≤ M, ck k ≤ c := by
    intro k hk
    simp only [hckdef]
    have hk' : (k : ℝ) ≤ M := by exact_mod_cast hk
    have : (k : ℝ) * ((c - ct) / M) ≤ M * ((c - ct) / M) :=
      mul_le_mul_of_nonneg_right hk' hgap0
    rw [mul_div_cancel₀ _ hMpos.ne'] at this
    linarith
  have hckM : ck M = c := by
    simp only [hckdef]; rw [mul_div_cancel₀ _ hMpos.ne']; ring
  have hck0 : ck 0 = ct := by simp [hckdef]
  have hckstep : ∀ k, ck (k + 1) = ck k + (c - ct) / M := by
    intro k; simp only [hckdef]; push_cast; ring
  set ε₂ := ε / (16 * (M + 2)) with hε₂def
  have hε₂ : 0 < ε₂ := by positivity
  -- the clustering at every width
  have hcl := fun k => heavyCoverAt_eventually d (ck k) ε₂ hd hd1 (hckpos k) hε₂
  choose ηc hηc N₀c hN₀c hHC using hcl
  have hne : (Finset.range (M + 1)).Nonempty := ⟨0, by simp⟩
  set ηm := (Finset.range (M + 1)).inf' hne ηc with hηmdef
  have hηm : 0 < ηm := (Finset.lt_inf'_iff hne).mpr fun k _ => hηc k
  have hηmle : ∀ k ≤ M, ηm ≤ ηc k := fun k hk =>
    Finset.inf'_le _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  set Nc := (Finset.range (M + 1)).sup' hne N₀c with hNcdef
  have hNcle : ∀ k ≤ M, N₀c k ≤ Nc := fun k hk =>
    Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  -- the loss
  set η := min (ε / (16 * (M + 2))) (ηm / 8) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ ε / (16 * (M + 2)) := min_le_left _ _
  have hη2 : η ≤ ηm / 8 := min_le_right _ _
  have hM2 : (2 : ℝ) ≤ M + 2 := by linarith
  have hηε : η ≤ ε := by
    have : ε / (16 * (M + 2)) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  -- eventual inequalities
  have he5 : ((M : ℝ) + 1) * (3 * η + ε₂) < ε - η := by
    have h1 : ((M : ℝ) + 1) * (3 * η + ε₂) ≤ ((M : ℝ) + 2) * (4 * (ε / (16 * (M + 2)))) := by
      have : 3 * η + ε₂ ≤ 4 * (ε / (16 * (M + 2))) := by rw [hε₂def]; linarith
      nlinarith
    have h2 : ((M : ℝ) + 2) * (4 * (ε / (16 * (M + 2)))) = ε / 4 := by field_simp; ring
    have h3 : η ≤ ε / 32 := by
      have : ε / (16 * (M + 2)) ≤ ε / 32 := by
        apply div_le_div_of_nonneg_left hε.le (by norm_num); nlinarith
      linarith
    linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (max 2 Nc)).and <|
     (ev_rpow 288 (3 * η) ηm (by linarith)).and <|
     (ev_rpow (648 * (M + 1)) (3 * η) ηm (by linarith)).and <|
     (ev_rpow 2 η (ε - ct) (by
        have : ε / (16 * (M + 2)) ≤ ε / 32 := by
          apply div_le_div_of_nonneg_left hε.le (by norm_num); nlinarith
        linarith)).and <|
     (ev_rpow (2 * (2832 * (M + 1)) ^ (M + 1)) ((M + 1) * (3 * η + ε₂)) (ε - η) he5))
  refine ⟨η, hη, hηε, max N₁ (max 2 Nc), le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩
  intro N hN Ω _ ν hν y β γ E F hU _ _
  obtain ⟨e1, e2, e3, e4, e5⟩ := hN₁ N ((le_max_left _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_left _ _).trans e1
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hNc : Nc ≤ N := (le_max_right _ _).trans e1
  have hQ : N ^ ((c - ct) / M) ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hnum := fun k (hk : k ≤ M) => slope_numerics (M := M) hN1 hη (hηmle k hk) e2 e3
  refine slope_at_N (ck := ck) (ηc := ηc) (M := M) (Q := N ^ ((c - ct) / M)) hU hd hd1 hN1 hη
    hηε (fun k hk => hHC k N ((hNcle k hk).trans hNc))
    (fun k hk => Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hckle k hk]))
    (fun k _ => Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith [hckpos k]))
    (by rw [hckM]) (fun k _ => le_of_eq ?_) hQ ?_
    (fun k hk => (hnum k hk).1) (fun k hk => (hnum k hk).2.1) (fun k hk => (hnum k hk).2.2.1)
    (fun k hk => (hnum k hk).2.2.2) (slope_numerics5 hN1 hη hε₂ e5)
  · rw [hckstep k, ← Real.rpow_add hN0]; congr 1; ring
  · rw [hck0, ← Real.rpow_add hN0]
    calc 2 * N ^ η ≤ N ^ (ε - ct) := e4
      _ = N ^ (ε + -ct) := by ring_nf

end Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

end
