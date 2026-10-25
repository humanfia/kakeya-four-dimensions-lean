-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.LipschitzRefine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzChain
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.ParityCubes

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- Lipschitz stages for a given family: refinements of an `η`-extremal family with a plane map
of precision `δ` on which the map varies by less than `2 ρc` at the scales `δ ^ (j / N)`. -/
theorem lipschitz_stages_refine {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) (hTS : TwoScaleTheoremP σ)
    (N : ℕ) (hN : 2 ≤ N) :
    ∀ m : ℕ, m ≤ N - 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (10 * N) →
      ∃ η d1 : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (V : Space → Space),
        Family η δ n x v Y → Separated η δ n x v →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
        Measurable V → (∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) →
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) →
        ∃ Y' : Fin n → Set Space, (∀ i, Y' i ⊆ Y i) ∧ Family ε δ n x v Y' ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ m → ∃ ρc : ℝ, δ ^ ((j : ℝ) / N) ≤ ρc ∧
            ρc ≤ δ ^ ((j : ℝ) / N - ε) ∧
            ∀ p ∈ ⋃ i, Y' i, ∀ q ∈ ⋃ i, Y' i, dist p q < ρc / 16 →
              dist (V p) (V q) < 2 * ρc := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  intro m
  induction m with
  | zero =>
    intro _ ε hε _
    refine ⟨ε, 1, hε, le_rfl, one_pos, ?_⟩
    intro δ hδ _ _ n x v Y V hF _ _ _ _ _
    exact ⟨Y, fun i => subset_rfl, hF, fun j hj1 hj0 => absurd hj0 (by omega)⟩
  | succ m ih =>
    intro hm ε hε hεN
    have hε10 : ε ≤ 1 / 10 := by
      have : 1 / (10 * (N : ℝ)) ≤ 1 / 10 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      linarith
    obtain ⟨η1, d1, hη1, hη1ε, hd1, hstep⟩ := lipschitz_scale_step hσ hσ2 hTS hε hε10
    obtain ⟨η, d2, hη, hηη1, hd2, hprev⟩ := ih (by omega) η1 hη1 (hη1ε.trans hεN)
    refine ⟨η, min d1 d2, hη, hηη1.trans hη1ε, lt_min hd1 hd2, ?_⟩
    intro δ hδ hδd hδ100 n x v Y V hF hS hvol hVm hVu hVp
    have hδ1 : δ ≤ 1 := by linarith
    obtain ⟨Y1, hY1Y, hF1, hscales⟩ := hprev δ hδ (hδd.trans (min_le_right _ _)) hδ100 n x v Y V
      hF hS hvol hVm hVu hVp
    have hsub1 : (⋃ i, Y1 i) ⊆ ⋃ i, Y i := iUnion_mono hY1Y
    set t := δ ^ (((m + 1 : ℕ) : ℝ) / N) with ht
    have hεN' : ε ≤ 1 / N := by
      calc ε ≤ 1 / (10 * N) := hεN
        _ ≤ 1 / N := div_le_div_of_nonneg_left (by norm_num) hNpos (by linarith)
    have hm1 : (((m + 1 : ℕ) : ℝ)) ≤ N - 1 := by
      have : m + 1 ≤ N - 1 := hm
      have h2 : ((m + 1 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h2; simpa using h2
    have hm0 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have hεN1 : ε * N ≤ 1 := by rw [le_div_iff₀ hNpos] at hεN'; linarith
    have ht1 : δ ^ (1 - ε) ≤ t := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      rw [div_le_iff₀ hNpos]; nlinarith
    have ht2 : t ≤ δ ^ ε := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      rw [le_div_iff₀ hNpos]; linarith
    obtain ⟨Y2, hY2Y1, hF2, ρc, hρc1, hρc2, hvar⟩ := hstep δ hδ (hδd.trans (min_le_left _ _))
      hδ100 n x v Y1 V hF1 (hS.mono_error hδ hδ1 hηη1)
      ((measure_mono hsub1).trans (hvol.trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))))
      hVm (fun p hp => hVu p (hsub1 hp)) (fun i p hp => hVp i p (hY1Y i hp)) t ht1 ht2
    have hsub2 : (⋃ i, Y2 i) ⊆ ⋃ i, Y1 i := iUnion_mono hY2Y1
    refine ⟨Y2, fun i => (hY2Y1 i).trans (hY1Y i), hF2, ?_⟩
    intro j hj1 hjm
    rcases Nat.lt_or_ge j (m + 1) with hlt | hge
    · obtain ⟨ρ, hρ1, hρ2, hρv⟩ := hscales j hj1 (by omega)
      refine ⟨ρ, hρ1, hρ2.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)), ?_⟩
      intro p hp q hq hpq
      exact hρv p (hsub2 hp) q (hsub2 hq) hpq
    · have hj : j = m + 1 := by omega
      subst hj
      refine ⟨ρc, hρc1, ?_, hvar⟩
      calc ρc ≤ δ ^ (-ε) * t := hρc2
        _ = δ ^ (((m + 1 : ℕ) : ℝ) / N - ε) := by
            rw [ht, ← Real.rpow_add hδ]; ring_nf

/-- **Lipschitz plane map for a given family** (sticky Lemma 4.7): an `η`-extremal family with
a plane map of precision `δ` that is constant on the grid cubes of a side `s ∈ [δ / 16, δ]` has an
`ε`-extremal refinement on which the plane map is `δ ^ (-ε)`-Lipschitz. -/
theorem lipschitz_refine {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) (hTS : TwoScaleTheoremP σ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η d1 : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (V : Space → Space) (s : ℝ),
        Family η δ n x v Y → Separated η δ n x v →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
        Measurable V → (∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) →
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) →
        0 < s → δ / 16 ≤ s → s ≤ δ → (∀ q q', cubeIndex s q = cubeIndex s q' → V q = V q') →
        ∃ Y' : Fin n → Set Space, (∀ i, Y' i ⊆ Y i) ∧ Family ε δ n x v Y' ∧
          ∀ p ∈ ⋃ i, Y' i, ∀ q ∈ ⋃ i, Y' i, dist (V p) (V q) ≤ δ ^ (-ε) * dist p q := by
  classical
  set N : ℕ := ⌈4 / ε⌉₊ + 2 with hNdef
  have hN : 2 ≤ N := by omega
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNinv : 1 / (N : ℝ) ≤ ε / 4 := by
    have h1 : 4 / ε ≤ (N : ℝ) := by
      have := Nat.le_ceil (4 / ε)
      have h2 : ((⌈4 / ε⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (show ⌈4 / ε⌉₊ ≤ N by omega)
      linarith
    rw [div_le_iff₀ hNpos]
    rw [div_le_iff₀ hε] at h1
    linarith
  set ε0 := min (ε / 4) (1 / (10 * N)) with hε0
  have hε00 : 0 < ε0 := lt_min (by positivity) (by positivity)
  have hε0a : ε0 ≤ ε / 4 := min_le_left _ _
  have hε0b : ε0 ≤ 1 / (10 * N) := min_le_right _ _
  have hε0N : ε0 ≤ 1 / N := hε0b.trans (div_le_div_of_nonneg_left (by norm_num) hNpos
    (by linarith))
  obtain ⟨c1, hc1, hcut1⟩ := exists_power_cutoff (a := ε / 2) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 32)
  obtain ⟨c2, hc2, hcut2⟩ := exists_power_cutoff (a := 1 / (N : ℝ)) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 16)
  obtain ⟨η, d1, hη, hηε0, hd1, hstages⟩ :=
    lipschitz_stages_refine hσ hσ2 hTS N hN (N - 1) le_rfl ε0 hε00 hε0b
  refine ⟨η, min d1 (min c1 c2), hη, hηε0.trans hε0a |>.trans (by linarith), lt_min hd1 (lt_min hc1 hc2), ?_⟩
  intro δ hδ hδd hδ100 n x v Y0 V s hF0 hS hvol0 hVm hVu0 hVp0 hs hslo hshi hcube
  obtain ⟨Y, hYY0, hF, hscales⟩ := hstages δ hδ (hδd.trans (min_le_left _ _)) hδ100 n x v Y0 V
    hF0 hS hvol0 hVm hVu0 hVp0
  have hsub0 : (⋃ i, Y i) ⊆ ⋃ i, Y0 i := iUnion_mono hYY0
  have hVu : ∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1 := fun p hp => hVu0 p (hsub0 hp)
  have hVp : ∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ := fun i p hp => hVp0 i p (hYY0 i hp)
  have hδ1 : δ ≤ 1 := by linarith
  have hq1 : δ ^ (ε / 2) ≤ 1 / 32 := hcut1 δ hδ (hδd.trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hq2 : δ ^ (1 / (N : ℝ)) ≤ 1 / 16 := hcut2 δ hδ (hδd.trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  -- parity selection at the cube side
  obtain ⟨c, hc⟩ := exists_heavy_parityClass (massMeasure Y) (⋃ i, Y i) s
  set Y'' : Fin n → Set Space := fun i => Y i ∩ parityClass s c with hY''
  have hYm := hF.2.2.2.2.1
  have hpm := measurableSet_parityClass hs c
  have hmass : ∑ i, volume (Y i) ≤ 8 * ∑ i, volume (Y'' i) := by
    have h1 := hc
    rw [massMeasure_apply hYm (MeasurableSet.iUnion hYm),
      massMeasure_apply hYm ((MeasurableSet.iUnion hYm).inter hpm)] at h1
    have e1 : ∀ i, Y i ∩ ⋃ j, Y j = Y i := fun i => inter_eq_left.2 (subset_iUnion Y i)
    have e2 : ∀ i, Y i ∩ ((⋃ j, Y j) ∩ parityClass s c) = Y'' i := by
      intro i; rw [hY'', ← inter_assoc, e1]
    simp only [e1, e2] at h1
    exact h1
  have hsubU : (⋃ i, Y'' i) ⊆ ⋃ i, Y i := iUnion_mono fun i => inter_subset_left
  -- the scales
  let ρf : ℕ → ℝ := fun j => if h : 1 ≤ j ∧ j ≤ N - 1 then Classical.choose (hscales j h.1 h.2)
    else 1
  have hρf : ∀ j, 1 ≤ j → j ≤ N - 1 → δ ^ ((j : ℝ) / N) ≤ ρf j ∧
      ρf j ≤ δ ^ ((j : ℝ) / N - ε0) ∧
      ∀ p ∈ ⋃ i, Y i, ∀ q ∈ ⋃ i, Y i, dist p q < ρf j / 16 → dist (V p) (V q) < 2 * ρf j := by
    intro j hj1 hj2
    have h := Classical.choose_spec (hscales j hj1 hj2)
    simp only [ρf, dif_pos (And.intro hj1 hj2)]
    exact h
  have hρfpos : ∀ j, 1 ≤ j → j ≤ N - 1 → 0 < ρf j := fun j hj1 hj2 =>
    (Real.rpow_pos_of_pos hδ _).trans_le (hρf j hj1 hj2).1
  -- data for the multi-scale assembly
  let s' : ℕ → ℝ := fun j => if j < N - 1 then ρf (j + 1) / 16 else s
  let r' : ℕ → ℝ := fun j => 2 * ρf (j + 1)
  set L := 32 * δ ^ (-(1 / (N : ℝ) + ε0)) with hL
  have hNsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  -- power identities
  have hpow : ∀ a b : ℝ, δ ^ a * δ ^ b = δ ^ (a + b) := fun a b => (Real.rpow_add hδ a b).symm
  have hs'pos : ∀ j, 0 < s' j := by
    intro j
    simp only [s']
    split_ifs with h
    · exact div_pos (hρfpos (j + 1) (by omega) (by omega)) (by norm_num)
    · exact hs
  have hδs : δ ≤ ρf (N - 1) / 16 := by
    have h1 := (hρf (N - 1) (by omega) le_rfl).1
    have h2 : δ ^ (((N - 1 : ℕ) : ℝ) / N) * δ ^ (1 / (N : ℝ)) = δ := by
      rw [hpow, hNsub]
      have : ((N : ℝ) - 1) / N + 1 / N = 1 := by field_simp; ring
      rw [this, Real.rpow_one]
    have h3 : 0 ≤ δ ^ (((N - 1 : ℕ) : ℝ) / N) := Real.rpow_nonneg hδ.le _
    nlinarith
  have hanti : ∀ j, s' (j + 1) ≤ s' j := by
    intro j
    simp only [s']
    by_cases h1 : j + 1 < N - 1
    · have h0 : j < N - 1 := by omega
      rw [if_pos h1, if_pos h0]
      have ha := (hρf (j + 2) (by omega) (by omega)).2.1
      have hb := (hρf (j + 1) (by omega) (by omega)).1
      have hc' : δ ^ (((j + 2 : ℕ) : ℝ) / N - ε0) ≤ δ ^ (((j + 1 : ℕ) : ℝ) / N) := by
        apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
        push_cast
        have : ((j : ℝ) + 2) / N - ε0 - ((j : ℝ) + 1) / N = 1 / N - ε0 := by ring
        linarith
      have : ρf (j + 1 + 1) ≤ ρf (j + 1) := by
        have e : j + 1 + 1 = j + 2 := rfl
        rw [e]; linarith
      linarith
    · rw [if_neg h1]
      by_cases h0 : j < N - 1
      · rw [if_pos h0]
        have hj : j + 1 = N - 1 := by omega
        rw [hj]; linarith
      · rw [if_neg h0]
  have hscale : ∀ j < N - 1, ∀ p ∈ ⋃ i, Y'' i, ∀ q ∈ ⋃ i, Y'' i, dist p q < s' j →
      dist (V p) (V q) ≤ r' j := by
    intro j hj p hp q hq hpq
    simp only [s', if_pos hj] at hpq
    exact ((hρf (j + 1) (by omega) (by omega)).2.2 p (hsubU hp) q (hsubU hq) hpq).le
  have hfin : ∀ p ∈ ⋃ i, Y'' i, ∀ q ∈ ⋃ i, Y'' i, dist p q < s' (N - 1) → V p = V q := by
    intro p hp q hq hpq
    simp only [s', lt_irrefl, if_false] at hpq
    obtain ⟨i, hi⟩ := mem_iUnion.1 hp
    obtain ⟨j, hj⟩ := mem_iUnion.1 hq
    exact hcube p q (cubeIndex_eq_of_parity hs hi.2 hj.2 hpq)
  have hbig : ∀ p ∈ ⋃ i, Y'' i, ∀ q ∈ ⋃ i, Y'' i, dist (V p) (V q) ≤ 2 := by
    intro p hp q hq
    calc dist (V p) (V q) ≤ ‖V p‖ + ‖V q‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
      _ = 2 := by rw [hVu p (hsubU hp), hVu q (hsubU hq)]; norm_num
  have hLpos : 0 ≤ L := by positivity
  have hLs : ∀ ρ a : ℝ, δ ^ a ≤ ρ → 2 * δ ^ (a - 1 / (N : ℝ) - ε0) ≤ L * (ρ / 16) := by
    intro ρ a hρ
    have e : L * (ρ / 16) = 2 * (δ ^ (-(1 / (N : ℝ) + ε0)) * ρ) := by rw [hL]; ring
    rw [e]
    have : δ ^ (a - 1 / (N : ℝ) - ε0) = δ ^ (-(1 / (N : ℝ) + ε0)) * δ ^ a := by
      rw [hpow]; ring_nf
    rw [this]
    have hp : 0 ≤ δ ^ (-(1 / (N : ℝ) + ε0)) := Real.rpow_nonneg hδ.le _
    nlinarith
  have hL0 : 2 ≤ L * s' 0 := by
    have h0 : 0 < N - 1 := by omega
    simp only [s', if_pos h0]
    have h1 := hLs (ρf 1) ((1 : ℕ) / (N : ℝ)) (by exact_mod_cast (hρf 1 le_rfl (by omega)).1)
    have h2 : (1 : ℝ) ≤ δ ^ ((((1 : ℕ) : ℝ) / N) - 1 / (N : ℝ) - ε0) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1
      push_cast; linarith
    push_cast at h1 h2
    linarith
  have hLj : ∀ j < N - 1, r' j ≤ L * s' (j + 1) := by
    intro j hj
    simp only [r', s']
    by_cases h1 : j + 1 < N - 1
    · rw [if_pos h1]
      have h2 := hLs (ρf (j + 1 + 1)) (((j + 2 : ℕ) : ℝ) / N)
        (by have := (hρf (j + 2) (by omega) (by omega)).1; exact this)
      have h3 := (hρf (j + 1) (by omega) (by omega)).2.1
      have e : ((j + 2 : ℕ) : ℝ) / N - 1 / (N : ℝ) - ε0 = ((j + 1 : ℕ) : ℝ) / N - ε0 := by
        push_cast; ring
      rw [e] at h2
      linarith
    · rw [if_neg h1]
      have hj1 : j + 1 = N - 1 := by omega
      rw [hj1]
      have h3 := (hρf (N - 1) (by omega) le_rfl).2.1
      have h2 := hLs (16 * s) 1 (by rw [Real.rpow_one]; linarith)
      have e : (1 : ℝ) - 1 / N - ε0 = ((N - 1 : ℕ) : ℝ) / N - ε0 := by
        rw [hNsub]; field_simp
      rw [e] at h2
      have : L * (16 * s / 16) = L * s := by ring
      linarith
  have hlip := lipschitz_of_scales V (⋃ i, Y'' i) s' r' (N - 1) L hs'pos hanti hscale hfin hbig
    hL0 hLj hLpos
  -- the Lipschitz constant
  have hLε : L ≤ δ ^ (-ε) := by
    have e : δ ^ (-ε) = δ ^ (-(ε - 1 / (N : ℝ) - ε0)) * δ ^ (-(1 / (N : ℝ) + ε0)) := by
      rw [hpow]; ring_nf
    have h1 : δ ^ (ε - 1 / (N : ℝ) - ε0) ≤ 1 / 32 :=
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans hq1
    have h2 : 32 ≤ δ ^ (-(ε - 1 / (N : ℝ) - ε0)) := by
      rw [Real.rpow_neg hδ.le]
      have hp : 0 < δ ^ (ε - 1 / (N : ℝ) - ε0) := Real.rpow_pos_of_pos hδ _
      rw [le_inv_comm₀ (by norm_num) hp]
      linarith
    rw [e, hL]
    have hp : 0 ≤ δ ^ (-(1 / (N : ℝ) + ε0)) := Real.rpow_nonneg hδ.le _
    nlinarith
  refine ⟨Y'', fun i => inter_subset_left.trans (hYY0 i), ?_, ?_⟩
  · refine ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, fun i => (hYm i).inter hpm,
      fun i => inter_subset_left.trans (hF.2.2.2.2.2.1 i), ?_⟩
    have h1 := hF.2.2.2.2.2.2
    have hq : δ ^ ε * (n : ℝ) * δ ^ 2 * 8 ≤ δ ^ ε0 * (n : ℝ) * δ ^ 2 := by
      have e : δ ^ ε = δ ^ (ε - ε0) * δ ^ ε0 := by rw [hpow]; ring_nf
      have h2 : δ ^ (ε - ε0) ≤ 1 / 8 :=
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans (hq1.trans (by norm_num))
      rw [e]
      have : 0 ≤ δ ^ ε0 * (n : ℝ) * δ ^ 2 := by positivity
      nlinarith
    have h8 : ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) * 8 ≤ ∑ i, volume (Y i) := by
      calc ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) * 8
          = ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2 * 8) := by
            rw [ENNReal.ofReal_mul' (by norm_num : (0:ℝ) ≤ 8)]; norm_num
        _ ≤ ENNReal.ofReal (δ ^ ε0 * (n : ℝ) * δ ^ 2) := ENNReal.ofReal_le_ofReal hq
        _ ≤ _ := h1
    have h9 := h8.trans hmass
    rw [mul_comm (8 : ℝ≥0∞)] at h9
    exact (ENNReal.mul_le_mul_iff_left (by norm_num) (by norm_num)).1 h9
  · intro p hp q hq
    exact (hlip p hp q hq).trans (mul_le_mul_of_nonneg_right hLε dist_nonneg)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
