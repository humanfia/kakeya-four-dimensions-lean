-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.LocalGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainsAtScale
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.CoveringStability

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- Window bound at one scale `ρ`: the `V p`-projections of `√ρ`-balls of `E` meet every window
of length `R ≥ ρ` in at most `C (R/ρ)^(1-σ)` intervals of radius `ρ`. -/
def WindowBound (V : Space → Space) (E : Set Space) (ρ C σ : ℝ) : Prop :=
  ∀ p ∈ E, ∀ a R : ℝ, ρ ≤ R → ∃ (m : ℕ) (c : Fin m → ℝ),
    ((fun q => inner ℝ (V p) q) '' (E ∩ ball p (Real.sqrt ρ))) ∩ Icc a (a + R) ⊆
      ⋃ j, closedBall (c j) ρ ∧ (m : ℝ) ≤ C * (R / ρ) ^ (1 - σ)

theorem WindowBound.mono {V : Space → Space} {E E' : Set Space} {ρ C C' σ : ℝ}
    (h : WindowBound V E ρ C σ) (hE : E' ⊆ E) (hC : C ≤ C') (hσ1 : σ < 1) (hρ : 0 < ρ) :
    WindowBound V E' ρ C' σ := by
  intro p hp a R hR
  obtain ⟨m, c, hcov, hm⟩ := h p (hE hp) a R hR
  refine ⟨m, c, fun t ht => hcov ⟨image_mono (inter_subset_inter_left _ hE) ht.1, ht.2⟩, ?_⟩
  exact hm.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (div_nonneg
    (hρ.le.trans hR) hρ.le) _))

/-- A real interval of length at most `L` meeting `Icc a (a + R)`, covered by closed balls of
radius `r`: at most `⌈L / (2 r)⌉ + 1`... in the form we need: a subset of a closed ball of
radius `h` is covered by `⌈h / r⌉₊ + 1` closed balls of radius `r`. -/
theorem cover_subset_closedBall {S : Set ℝ} {t h r : ℝ} (hS : S ⊆ closedBall t h) (hr : 0 < r)
    (hh : 0 ≤ h) : ∃ c : Fin (⌈h / r⌉₊ + 1) → ℝ, S ⊆ ⋃ j, closedBall (c j) r := by
  obtain ⟨c, hc⟩ := closedBall_real_cover t h r hr hh
  exact ⟨c, hS.trans hc⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **From window bounds at the grid scales `δ^(j/M)` to the frozen covering condition at all
scales** (the interpolation in sticky Lemma 4.12). -/
theorem covering_of_window_bounds {V : Space → Space} {E : Set Space} {δ C σ : ℝ} {M : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 2 ≤ M) (hC : 1 ≤ C) (hσ1 : σ < 1)
    (hVu : ∀ p ∈ E, ‖V p‖ = 1)
    (hW : ∀ j : ℕ, 1 ≤ j → j ≤ M - 1 → WindowBound V E (δ ^ ((j : ℝ) / M)) C σ) :
    ∀ ρ, δ ≤ ρ → ρ ≤ 1 → ∀ p ∈ E,
      Covering ρ (1 - σ) (3 * δ ^ (-(1 / (M : ℝ))) * C)
        ((fun q => inner ℝ (V p) q) '' (E ∩ ball p (Real.sqrt ρ))) := by
  classical
  intro ρ hρ hρ1 p hp r R a hρr hrR
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hr0 : 0 < r := hδ.trans_le (hρ.trans hρr)
  set κ := δ ^ (-(1 / (M : ℝ))) with hκ
  have hκ1 : 1 ≤ κ := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by
    have : 0 ≤ 1 / (M : ℝ) := by positivity
    linarith)
  have hRr : 1 ≤ R / r := by rw [le_div_iff₀ hr0]; linarith
  have hpow1 : 1 ≤ (R / r) ^ (1 - σ) := Real.one_le_rpow hRr (by linarith)
  have hκδ : κ * δ ^ (1 / (M : ℝ)) = 1 := by
    rw [hκ, ← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
  by_cases hcase : δ ^ (1 / (M : ℝ)) ≤ r
  · -- coarse windows: the projection has diameter at most `2`
    have hBsub : ((fun q => inner ℝ (V p) q) '' (E ∩ ball p (Real.sqrt ρ))) ∩ Icc a (a + R) ⊆
        closedBall (inner ℝ (V p) p) 1 := by
      rintro t ⟨⟨q, hq, rfl⟩, -⟩
      rw [mem_closedBall, Real.dist_eq, ← inner_sub_right]
      calc |inner ℝ (V p) (q - p)| ≤ ‖V p‖ * ‖q - p‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 := by
            rw [hVu p hp, one_mul, ← dist_eq_norm]
            exact (mem_ball.1 hq.2).le.trans (Real.sqrt_le_one.mpr hρ1 |> fun h => by
              simpa using Real.sqrt_le_sqrt hρ1)
    obtain ⟨c, hc⟩ := cover_subset_closedBall hBsub hr0 zero_le_one
    refine ⟨⌈1 / r⌉₊ + 1, c, hc, ?_⟩
    have h1r : 1 / r ≤ κ := by
      rw [div_le_iff₀ hr0]
      calc 1 = κ * δ ^ (1 / (M : ℝ)) := hκδ.symm
        _ ≤ κ * r := mul_le_mul_of_nonneg_left hcase (by linarith)
    have hceil : ((⌈1 / r⌉₊ + 1 : ℕ) : ℝ) ≤ 3 * κ := by
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / r)
      push_cast; linarith
    calc ((⌈1 / r⌉₊ + 1 : ℕ) : ℝ) ≤ 3 * κ := hceil
      _ = 3 * κ * 1 * 1 := by ring
      _ ≤ 3 * κ * C * (R / r) ^ (1 - σ) := by gcongr
  · push Not at hcase
    -- the grid scale just above `r`
    have hex : ∃ j : ℕ, δ ^ ((j : ℝ) / M) ≤ r := ⟨M, by
      rw [div_self hM0.ne', Real.rpow_one]; linarith⟩
    set j0 := Nat.find hex with hj0def
    have hj0 : δ ^ ((j0 : ℝ) / M) ≤ r := Nat.find_spec hex
    have hj0M : j0 ≤ M := Nat.find_min' hex (by rw [div_self hM0.ne', Real.rpow_one]; linarith)
    have hj0ne0 : j0 ≠ 0 := by
      intro h
      rw [h] at hj0
      simp at hj0
      have : δ ^ (1 / (M : ℝ)) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
      linarith
    have hj0ne1 : j0 ≠ 1 := by
      intro h; rw [h] at hj0; push_cast at hj0; linarith
    set j' := j0 - 1 with hj'
    have hj'1 : 1 ≤ j' := by omega
    have hj'M : j' ≤ M - 1 := by omega
    have hrj' : r < δ ^ ((j' : ℝ) / M) := by
      have h := Nat.find_min hex (show j' < j0 by omega)
      push Not at h
      exact h
    have hj'up : δ ^ ((j' : ℝ) / M) ≤ κ * r := by
      have e : δ ^ ((j' : ℝ) / M) = κ * δ ^ ((j0 : ℝ) / M) := by
        rw [hκ, ← Real.rpow_add hδ]
        congr 1
        have h1 : j' + 1 = j0 := by omega
        have : (j0 : ℝ) = (j' : ℝ) + 1 := by rw [← h1]; push_cast; ring
        rw [this]; field_simp; ring
      rw [e]; exact mul_le_mul_of_nonneg_left hj0 (by linarith)
    set ρ' := δ ^ ((j' : ℝ) / M) with hρ'
    have hρ'0 : 0 < ρ' := Real.rpow_pos_of_pos hδ _
    have hBB : ((fun q => inner ℝ (V p) q) '' (E ∩ ball p (Real.sqrt ρ))) ⊆
        (fun q => inner ℝ (V p) q) '' (E ∩ ball p (Real.sqrt ρ')) :=
      image_mono (inter_subset_inter_right _ (ball_subset_ball
        (Real.sqrt_le_sqrt (hρr.trans hrj'.le))))
    set R' := max R ρ' with hR'
    obtain ⟨m', c', hcov', hm'⟩ := hW j' hj'1 hj'M p hp a R' (le_max_right _ _)
    have hsub : ∀ k : Fin m', ∃ cc : Fin (⌈ρ' / r⌉₊ + 1) → ℝ,
        closedBall (c' k) ρ' ⊆ ⋃ l, closedBall (cc l) r :=
      fun k => closedBall_real_cover (c' k) ρ' r hr0 hρ'0.le
    choose cc hcc using hsub
    let e : Fin m' × Fin (⌈ρ' / r⌉₊ + 1) ≃ Fin (m' * (⌈ρ' / r⌉₊ + 1)) := finProdFinEquiv
    refine ⟨m' * (⌈ρ' / r⌉₊ + 1), fun idx => cc (e.symm idx).1 (e.symm idx).2, ?_, ?_⟩
    · intro t ht
      have ht' : t ∈ ((fun q => inner ℝ (V p) q) '' (E ∩ ball p (Real.sqrt ρ'))) ∩
          Icc a (a + R') := ⟨hBB ht.1, ⟨ht.2.1, ht.2.2.trans (by
            have := le_max_left R ρ'; linarith)⟩⟩
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov' ht')
      obtain ⟨l, hl⟩ := mem_iUnion.1 (hcc k hk)
      exact mem_iUnion.2 ⟨e (k, l), by simp only [Equiv.symm_apply_apply]; exact hl⟩
    · have hρ'r : ρ' / r ≤ κ := by rw [div_le_iff₀ hr0]; exact hj'up
      have hceil : ((⌈ρ' / r⌉₊ + 1 : ℕ) : ℝ) ≤ 3 * κ := by
        have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ ρ' / r)
        push_cast; linarith
      have hR'r : (R' / ρ') ^ (1 - σ) ≤ (R / r) ^ (1 - σ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by linarith)
        rcases le_total R ρ' with h | h
        · rw [hR', max_eq_right h, div_self hρ'0.ne']; exact hRr
        · rw [hR', max_eq_left h]
          exact div_le_div_of_nonneg_left (by linarith) hr0 hrj'.le
      have hm'0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
      push_cast
      calc (m' : ℝ) * ((⌈ρ' / r⌉₊ : ℝ) + 1) ≤ (C * (R' / ρ') ^ (1 - σ)) * (3 * κ) := by
            have h2 : ((⌈ρ' / r⌉₊ : ℝ) + 1) ≤ 3 * κ := by exact_mod_cast hceil
            exact mul_le_mul hm' h2 (by positivity) (by positivity)
        _ ≤ (C * (R / r) ^ (1 - σ)) * (3 * κ) := by gcongr
        _ = 3 * κ * C * (R / r) ^ (1 - σ) := by ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- Window bounds at the grid scales `δ^(j/M)`, `j ≤ m`, for refinements of a given family. -/
theorem grains_stages_refine {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hTS : TwoScaleTheoremP σ)
    (M : ℕ) (hM : 10 ≤ M) :
    ∀ m : ℕ, m ≤ M - 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (10 * M) →
      ∃ η d1 : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (V : Space → Space),
        Family η δ n x v Y → Separated η δ n x v →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
        (∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) → (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) →
        (∀ p ∈ ⋃ i, Y i, ∀ q ∈ ⋃ i, Y i, dist (V p) (V q) ≤ δ ^ (-η) * dist p q) →
        ∃ Y' : Fin n → Set Space, (∀ i, Y' i ⊆ Y i) ∧ Family ε δ n x v Y' ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ m →
            WindowBound V (⋃ i, Y' i) (δ ^ ((j : ℝ) / M)) (δ ^ (-ε)) σ := by
  have hMR : (10 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  intro m
  induction m with
  | zero =>
    intro _ ε hε _
    refine ⟨ε, 1, hε, le_rfl, one_pos, ?_⟩
    intro δ _ _ _ n x v Y V hF _ _ _ _ _
    exact ⟨Y, fun i => subset_rfl, hF, fun j hj1 hj0 => absurd hj0 (by omega)⟩
  | succ m ih =>
    intro hm ε hε hεM
    have hε100 : ε ≤ 1 / 100 := hεM.trans (by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
    obtain ⟨ηg, dg, hηg, hηgε, hdg, hG⟩ := grains_at_scale hσ hσ1 hTS hε hε100
    obtain ⟨η, d2, hη, hηηg, hd2, hprev⟩ := ih (by omega) ηg hηg (hηgε.trans hεM)
    refine ⟨η, min dg d2, hη, hηηg.trans hηgε, lt_min hdg hd2, ?_⟩
    intro δ hδ hδd hδ100 n x v Y V hF hS hvol hVu hVp hVL
    have hδ1 : δ ≤ 1 := by linarith
    obtain ⟨Y1, hY1Y, hF1, hW1⟩ := hprev δ hδ (hδd.trans (min_le_right _ _)) hδ100 n x v Y V
      hF hS hvol hVu hVp hVL
    have hsub1 : (⋃ i, Y1 i) ⊆ ⋃ i, Y i := iUnion_mono hY1Y
    have hεM' : ε ≤ 1 / M := hεM.trans (div_le_div_of_nonneg_left (by norm_num) hM0
      (by linarith))
    have hm1 : ((m + 1 : ℕ) : ℝ) ≤ M - 1 := by
      have : m + 1 ≤ M - 1 := hm
      have h2 : ((m + 1 : ℕ) : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h2; simpa using h2
    have hm0 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have hεM1 : ε * M ≤ 1 := by rw [le_div_iff₀ hM0] at hεM'; linarith
    have hρ1 : δ ^ (1 - ε) ≤ δ ^ (((m + 1 : ℕ) : ℝ) / M) := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      rw [div_le_iff₀ hM0]; nlinarith
    have hρ2 : δ ^ (((m + 1 : ℕ) : ℝ) / M) ≤ δ ^ ε := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      rw [le_div_iff₀ hM0]; linarith
    have hLip : ∀ p ∈ ⋃ i, Y1 i, ∀ q ∈ ⋃ i, Y1 i, dist (V p) (V q) ≤ δ ^ (-ηg) * dist p q := by
      intro p hp q hq
      refine (hVL p (hsub1 hp) q (hsub1 hq)).trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    obtain ⟨Y2, hY2Y1, hF2, hwin⟩ := hG δ hδ (hδd.trans (min_le_left _ _)) hδ100 n x v Y1 V hF1
      (hS.mono_error hδ hδ1 hηηg) ((measure_mono hsub1).trans (hvol.trans
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))))
      (fun p hp => hVu p (hsub1 hp)) (fun i p hp => hVp i p (hY1Y i hp)) hLip _ hρ1 hρ2
    have hsub2 : (⋃ i, Y2 i) ⊆ ⋃ i, Y1 i := iUnion_mono hY2Y1
    refine ⟨Y2, fun i => (hY2Y1 i).trans (hY1Y i), hF2, ?_⟩
    intro j hj1 hjm
    rcases Nat.lt_or_ge j (m + 1) with hlt | hge
    · exact (hW1 j hj1 (by omega)).mono hsub2
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) hσ1
        (Real.rpow_pos_of_pos hδ _)
    · have hj : j = m + 1 := by omega
      subst hj
      exact hwin

/-- **Local grains for a given family** (sticky Lemma 4.12): an `η`-extremal family with a
`δ^(-η)`-Lipschitz plane map of precision `δ` has an `ε`-extremal refinement satisfying the frozen
local covering condition at every scale `ρ ∈ [δ, 1]`. -/
theorem local_grains_refine {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hTS : TwoScaleTheoremP σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η d1 : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (V : Space → Space),
        Family η δ n x v Y → Separated η δ n x v →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
        (∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) → (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) →
        (∀ p ∈ ⋃ i, Y i, ∀ q ∈ ⋃ i, Y i, dist (V p) (V q) ≤ δ ^ (-η) * dist p q) →
        ∃ Y' : Fin n → Set Space, (∀ i, Y' i ⊆ Y i) ∧ Family ε δ n x v Y' ∧
          ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p ∈ ⋃ i, Y' i,
            Covering ρ (1 - σ) (δ ^ (-ε))
              ((fun q => inner ℝ (V p) q) '' ((⋃ i, Y' i) ∩ ball p (Real.sqrt ρ))) := by
  set M : ℕ := ⌈8 / ε⌉₊ + 10 with hMdef
  have hM10 : 10 ≤ M := by omega
  have hM : 2 ≤ M := by omega
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hMinv : 1 / (M : ℝ) ≤ ε / 8 := by
    have h1 : 8 / ε ≤ (M : ℝ) := by
      have := Nat.le_ceil (8 / ε)
      have h2 : ((⌈8 / ε⌉₊ : ℕ) : ℝ) ≤ M := by exact_mod_cast (show ⌈8 / ε⌉₊ ≤ M by omega)
      linarith
    rw [div_le_iff₀ hM0]
    rw [div_le_iff₀ hε] at h1
    linarith
  set ε' := min (ε / 4) (1 / (10 * M)) with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) (by positivity)
  have hε'a : ε' ≤ ε / 4 := min_le_left _ _
  have hε'b : ε' ≤ 1 / (10 * M) := min_le_right _ _
  obtain ⟨η, d1, hη, hηε', hd1, hstages⟩ :=
    grains_stages_refine hσ hσ1 hTS M hM10 (M - 1) le_rfl ε' hε'0 hε'b
  obtain ⟨c1, hc1, hcut⟩ := exists_power_cutoff (a := 5 * ε / 8) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 3)
  refine ⟨η, min d1 c1, hη, hηε'.trans (hε'a.trans (by linarith)), lt_min hd1 hc1, ?_⟩
  intro δ hδ hδd hδ100 n x v Y V hF hS hvol hVu hVp hVL
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨Y', hY'Y, hF', hW⟩ := hstages δ hδ (hδd.trans (min_le_left _ _)) hδ100 n x v Y V hF
    hS hvol hVu hVp hVL
  have hsub : (⋃ i, Y' i) ⊆ ⋃ i, Y i := iUnion_mono hY'Y
  refine ⟨Y', hY'Y, hF'.mono_error hδ hδ1 (hε'a.trans (by linarith)), ?_⟩
  have hC1 : 1 ≤ δ ^ (-ε') := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hcov := covering_of_window_bounds (V := V) (E := ⋃ i, Y' i) (C := δ ^ (-ε')) (σ := σ)
    hδ hδ1 hM hC1 hσ1 (fun p hp => hVu p (hsub hp)) hW
  intro ρ hρ hρ1 p hp
  refine Covering.mono_constant (hcov ρ hρ hρ1 p hp) (hδ.trans_le hρ) ?_
  -- `3 δ^(-1/M) δ^(-ε') ≤ δ^(-ε)`
  have hq := hcut δ hδ (hδd.trans (min_le_right _ _))
  have e : δ ^ (-ε) = δ ^ (-(5 * ε / 8)) * (δ ^ (-(1 / (M : ℝ))) * δ ^ (-ε')) *
      δ ^ (1 / (M : ℝ) + ε' - 3 * ε / 8) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]; ring_nf
  have h3 : 3 ≤ δ ^ (-(5 * ε / 8)) := by
    rw [Real.rpow_neg hδ.le]
    rw [le_inv_comm₀ (by norm_num) (Real.rpow_pos_of_pos hδ _)]
    linarith
  have h4 : 1 ≤ δ ^ (1 / (M : ℝ) + ε' - 3 * ε / 8) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  rw [e]
  have hpos : 0 ≤ δ ^ (-(1 / (M : ℝ))) * δ ^ (-ε') := by positivity
  calc 3 * δ ^ (-(1 / (M : ℝ))) * δ ^ (-ε') = 3 * (δ ^ (-(1 / (M : ℝ))) * δ ^ (-ε')) * 1 := by
        ring
    _ ≤ δ ^ (-(5 * ε / 8)) * (δ ^ (-(1 / (M : ℝ))) * δ ^ (-ε')) *
        δ ^ (1 / (M : ℝ) + ε' - 3 * ε / 8) := by gcongr

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
