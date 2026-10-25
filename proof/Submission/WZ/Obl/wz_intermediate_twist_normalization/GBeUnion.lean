-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.GBeUnion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.GBeCount
import Submission.WZ.Obl.wz_nsp_convex_test_family
import Submission.WZ.Obl.wz_nsp_finite_load_selection

/-!
# The union of selected translates

For a family in `safeCyl r e` with the enlarged convex count `Kt |W + 2e(W - W)|`, choose among
the grid translations of spacing `ρ / 2` (`o055`'s test sets and `o057`'s load selection) a list
of `N = ⌈r² Kt / m⌉` translations. The union of the translated families satisfies the convex
count with coefficient `27 D C ρ^(-ε') log 3 · Kt` (`translates_count`).
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube)
open WangZahlLot.Obl.wz_compact_offset_normalization (abs_coord_le_norm)

/-- The grid is fine enough. -/
theorem grid_params {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ρ / 2 * (⌊r / ρ⌋₊ : ℝ) ≤ r / 2 ∧
      r ^ 2 / 4 ≤ (((2 * ⌊r / ρ⌋₊ + 1) * (2 * ⌊r / ρ⌋₊ + 1) : ℕ) : ℝ) * (ρ / 2) ^ 2 := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊r / ρ⌋₊ := ⟨_, rfl⟩
  rw [← hM]
  have hr : 0 < r := lt_of_lt_of_le hρ hρr
  have hrρ : 0 ≤ r / ρ := div_nonneg hr.le hρ.le
  have h0 : (M : ℝ) ≤ r / ρ := hM ▸ Nat.floor_le hrρ
  have h1 : r / ρ < M + 1 := hM ▸ Nat.lt_floor_add_one (r / ρ)
  constructor
  · calc ρ / 2 * (M : ℝ) ≤ ρ / 2 * (r / ρ) := by gcongr
      _ = r / 2 := by field_simp
  · have h2 : r ≤ ρ * (2 * M + 1) := by
      have h1' : 1 ≤ r / ρ := by rw [le_div_iff₀ hρ]; linarith
      rw [div_lt_iff₀ hρ] at h1
      nlinarith
    have h3 : r ^ 2 ≤ (ρ * (2 * M + 1)) ^ 2 := pow_le_pow_left₀ hr.le h2 2
    push_cast
    nlinarith [sq_nonneg ρ]

/-- The loads. -/
theorem load_bounds {H mG m N : ℕ} {Kt h r xq : ℝ} (cnt : Fin H → Fin mG → ℕ) (V : Fin H → ℝ)
    (hKt : 0 < Kt) (hV0 : ∀ hh, 0 ≤ V hh) (hcntle : ∀ hh s, (cnt hh s : ℝ) ≤ Kt * V hh)
    (hgrid : ∀ hh, ∑ s, (cnt hh s : ℝ) ≤ m * (2 * V hh / h ^ 2)) (hhp : 0 < h) (hm : 0 < m)
    (hN2 : (N : ℝ) ≤ 217 * xq) (hxq : xq = r ^ 2 * Kt / m) (hmGh : r ^ 2 / 4 ≤ mG * h ^ 2) :
    (∀ (k : Fin 1) hh s, 0 ≤ (cnt hh s : ℝ) / (Kt * V hh) ∧ (cnt hh s : ℝ) / (Kt * V hh) ≤ 1) ∧
      (∀ (k : Fin 1) hh, (N : ℝ) * ∑ s, (cnt hh s : ℝ) / (Kt * V hh) ≤ 4000 * (mG : ℝ)) := by
  refine ⟨fun k hh s => ⟨by have := hV0 hh; positivity,
    div_le_one_of_le₀ (hcntle hh s) (by have := hV0 hh; positivity)⟩, fun k hh => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hxq0 : 0 ≤ xq := by rw [hxq]; positivity
  rw [← Finset.sum_div]
  by_cases hV : V hh = 0
  · rw [hV, mul_zero, div_zero, mul_zero]; positivity
  have hVpos : 0 < V hh := lt_of_le_of_ne (hV0 hh) (Ne.symm hV)
  have h1 : (∑ s, (cnt hh s : ℝ)) / (Kt * V hh) ≤ 2 * m / (h ^ 2 * Kt) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (∑ s, (cnt hh s : ℝ)) * (h ^ 2 * Kt) ≤ m * (2 * V hh / h ^ 2) * (h ^ 2 * Kt) := by
          gcongr; exact hgrid hh
      _ = 2 * m * (Kt * V hh) := by field_simp
  have hX0 : 0 ≤ (∑ s, (cnt hh s : ℝ)) / (Kt * V hh) := by positivity
  calc (N : ℝ) * ((∑ s, (cnt hh s : ℝ)) / (Kt * V hh))
      ≤ (217 * xq) * (2 * m / (h ^ 2 * Kt)) := mul_le_mul hN2 h1 hX0 (by linarith)
    _ = 434 * r ^ 2 / h ^ 2 := by rw [hxq]; field_simp; ring
    _ ≤ 4000 * mG := by
        rw [div_le_iff₀ (pow_pos hhp 2)]
        have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
        linarith

/-- Summing loads over the selection. -/
theorem selected_count_le {N mG : ℕ} {Kt V C : ℝ} (cnt : Fin mG → ℕ) (φ : Fin N → Fin mG)
    (hKt : 0 < Kt) (hV : 0 ≤ V) (hcntle : ∀ s, (cnt s : ℝ) ≤ Kt * V)
    (hsel : ∑ j, (cnt (φ j) : ℝ) / (Kt * V) ≤ C) (hC : 0 ≤ C) :
    ∑ j, (cnt (φ j) : ℝ) ≤ C * (Kt * V) := by
  by_cases hV0 : V = 0
  · have : ∀ j, (cnt (φ j) : ℝ) = 0 := by
      intro j
      have := hcntle (φ j)
      rw [hV0, mul_zero] at this
      exact le_antisymm this (Nat.cast_nonneg _)
    simp [this, hV0]
  have hKV : 0 < Kt * V := mul_pos hKt (lt_of_le_of_ne hV (Ne.symm hV0))
  rw [← Finset.sum_div, div_le_iff₀ hKV] at hsel
  exact hsel

set_option maxHeartbeats 1600000 in
/-- **The selected translates.** -/
theorem translates_count {D55 C57 ε' : ℝ} (hD55 : 1 ≤ D55) (hC57 : 0 < C57)
    (h55 : ∀ r : ℝ, 0 < r → r ≤ 1 → ∃ (H : ℕ) (P : Fin H → Set Space),
      (H : ℝ) ≤ D55 * r ^ (-D55) ∧
      (∀ h : Fin H, Convex ℝ (P h) ∧ MeasurableSet (P h) ∧ 0 < volume (P h) ∧
        volume (P h) ≠ ⊤) ∧
      ∀ (K m n : ℕ) (x v : Fin m × Fin n → Space) (g : Fin n → Fin K) (B : ℝ),
        (∀ q : Fin m × Fin n, ‖v q‖ = 1 ∧ tube r (x q) (v q) ⊆ ball 0 2) →
        (∀ (k : Fin K) (h : Fin H), ENNReal.ofReal (((Set.ncard {q : Fin m × Fin n |
          g q.2 = k ∧ tube r (x q) (v q) ⊆ P h} : ℕ) : ℝ) * r ^ 2) ≤
            ENNReal.ofReal B * volume (P h)) →
        ∀ (k : Fin K) (W : Set Space), Convex ℝ W →
          ENNReal.ofReal (((Set.ncard {q : Fin m × Fin n | g q.2 = k ∧
            tube r (x q) (v q) ⊆ W} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal (D55 * B) * volume W)
    (h57 : ∀ (r : ℝ) (K H m N : ℕ) (X : Fin K → Fin H → Fin m → ℝ), 0 < r → r ≤ 1 → 0 < m →
      (H : ℝ) ≤ D55 * r ^ (-D55) → (∀ (k : Fin K) (h : Fin H) (s : Fin m),
        0 ≤ X k h s ∧ X k h s ≤ 1) →
      (∀ (k : Fin K) (h : Fin H), (N : ℝ) * ∑ s : Fin m, X k h s ≤ 4000 * (m : ℝ)) →
      ∃ f : Fin N → Fin m, ∀ (k : Fin K) (h : Fin H),
        ∑ j : Fin N, X k h (f j) ≤ C57 * r ^ (-ε') * Real.log (2 + (K : ℝ)))
    {ρ r e Kt : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρr : ρ ≤ r) (he16 : 16 * r ^ 2 ≤ e)
    (he4 : e ≤ 1 / 4) {m : ℕ} (hm : 0 < m) {x v : Fin m → Space}
    (hv : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hcyl : ∀ i, tube ρ (x i) (v i) ⊆ safeCyl r e)
    (hcount : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | tube ρ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal Kt * volume (W + (2 * e) • (W - W))) :
    0 < Kt ∧ ∃ (N : ℕ) (s : Fin N → Space),
      r ^ 2 * Kt / m ≤ N ∧ (N : ℝ) ≤ 217 * (r ^ 2 * Kt / m) ∧
      (∀ j, s j 2 = 0 ∧ s j 0 ^ 2 + s j 1 ^ 2 ≤ r ^ 2) ∧
      ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {q : Fin N × Fin m |
          tube ρ (x q.2 + s q.1) (v q.2) ⊆ W} : ℕ) : ℝ) ≤
          ENNReal.ofReal (D55 * (27 * C57 * ρ ^ (-ε') * Real.log 3 * Kt)) * volume W := by
  classical
  have he0 : 0 ≤ e := by nlinarith [sq_nonneg r]
  have hr0 : 0 < r := lt_of_lt_of_le hρ hρr
  have hr1 : r ≤ 1 := by nlinarith [sq_nonneg r]
  -- the number of tubes and the count coefficient
  have hmK := card_le_of_safeCyl hr0.le hr1 he0 he4 hm hcyl hcount
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hKt : 0 < Kt := by
    by_contra hneg
    push Not at hneg
    have : Kt * (216 * r ^ 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
    linarith
  refine ⟨hKt, ?_⟩
  obtain ⟨xq, hxq⟩ : ∃ xq : ℝ, xq = r ^ 2 * Kt / m := ⟨_, rfl⟩
  have hxq0 : 1 / 216 ≤ xq := by
    rw [hxq, le_div_iff₀ hm0]; nlinarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈xq⌉₊ := ⟨_, rfl⟩
  have hN1 : xq ≤ N := hNdef ▸ Nat.le_ceil xq
  have hN2 : (N : ℝ) ≤ 217 * xq := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ xq)
    rw [← hNdef] at this
    linarith
  -- the grid
  obtain ⟨hM1, hM2⟩ := grid_params hρ hρr
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌊r / ρ⌋₊ := ⟨_, rfl⟩
  rw [← hMdef] at hM1 hM2
  obtain ⟨mG, hmGdef⟩ : ∃ mG : ℕ, mG = (2 * M + 1) * (2 * M + 1) := ⟨_, rfl⟩
  rw [← hmGdef] at hM2
  have hmG : 0 < mG := by rw [hmGdef]; positivity
  have hhpos : 0 < ρ / 2 := by positivity
  let σg : Fin mG → Space := fun s =>
    sgrid (ρ / 2) M (finProdFinEquiv.symm (hmGdef ▸ s)).1 (finProdFinEquiv.symm (hmGdef ▸ s)).2
  have hσ2 : ∀ s, σg s 2 = 0 := fun s => sgrid_two _ _ _ _
  have hσsq : ∀ s, σg s 0 ^ 2 + σg s 1 ^ 2 ≤ r ^ 2 := by
    intro s
    have h1 := sgrid_sq_le hhpos.le M (finProdFinEquiv.symm (hmGdef ▸ s)).1
      (finProdFinEquiv.symm (hmGdef ▸ s)).2
    have h4 : 0 ≤ ρ / 2 * M := by positivity
    have h5 : (ρ / 2 * M) ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ h4 hM1 2
    nlinarith
  -- translated tubes stay in the unit ball
  have hTball : ∀ s i, tube ρ (x i + σg s) (v i) ⊆ ball 0 1 := fun s i =>
    translate_subset_ball he16 he4 (hcyl i) (hσ2 s) (hσsq s)
  -- the test sets
  obtain ⟨H, P, hH, hPprop, htr⟩ := h55 ρ hρ hρ1
  have hP'conv : ∀ hh, Convex ℝ (P hh ∩ ball 0 2) := fun hh => (hPprop hh).1.inter (convex_ball _ _)
  have hP'bdd : ∀ hh, Bornology.IsBounded (P hh ∩ ball 0 2) := fun hh =>
    isBounded_ball.subset inter_subset_right
  have hP'vol : ∀ hh, volume ((P hh ∩ ball 0 2) + (2 * e) • ((P hh ∩ ball 0 2) - (P hh ∩ ball 0 2)))
      ≤ ENNReal.ofReal 27 * volume (P hh ∩ ball 0 2) := by
    intro hh
    refine (volume_add_smul_sub_le (hP'conv hh) (hP'bdd hh) (t := 2 * e) (by positivity)).trans ?_
    gcongr
    have : 1 + 4 * (2 * e) ≤ 3 := by linarith
    calc (1 + 4 * (2 * e)) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (by linarith) this 3
      _ = 27 := by norm_num
  have hP'fin : ∀ hh, volume (P hh ∩ ball 0 2) ≠ ⊤ := fun hh =>
    ne_top_of_le_ne_top (hPprop hh).2.2.2 (measure_mono inter_subset_left)
  have hP'plusfin : ∀ hh, volume ((P hh ∩ ball 0 2) + (2 * e) •
      ((P hh ∩ ball 0 2) - (P hh ∩ ball 0 2))) ≠ ⊤ := fun hh =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hP'fin hh)) (hP'vol hh)
  obtain ⟨V, hVdef⟩ : ∃ V : Fin H → ℝ, V = fun hh => (volume ((P hh ∩ ball 0 2) + (2 * e) •
      ((P hh ∩ ball 0 2) - (P hh ∩ ball 0 2)))).toReal := ⟨_, rfl⟩
  have hV0 : ∀ hh, 0 ≤ V hh := fun hh => by rw [hVdef]; exact ENNReal.toReal_nonneg
  have hVP : ∀ hh, (volume (P hh ∩ ball 0 2)).toReal ≤ V hh := by
    intro hh
    rw [hVdef]
    apply ENNReal.toReal_mono (hP'plusfin hh)
    apply measure_mono
    intro p hp
    exact ⟨p, hp, 0, ⟨0, ⟨p, hp, p, hp, sub_self p⟩, smul_zero _⟩, add_zero p⟩
  have hV27 : ∀ hh, V hh ≤ 27 * (volume (P hh)).toReal := by
    intro hh
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hP'fin hh))
      (hP'vol hh)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at h1
    have h2 : (volume (P hh ∩ ball 0 2)).toReal ≤ (volume (P hh)).toReal :=
      ENNReal.toReal_mono (hPprop hh).2.2.2 (measure_mono inter_subset_left)
    rw [hVdef]
    linarith
  -- the counts of translates
  obtain ⟨cnt, hcnt⟩ : ∃ cnt : Fin H → Fin mG → ℕ, cnt = fun hh s =>
      (Finset.univ.filter (fun i => tube ρ (x i + σg s) (v i) ⊆ P hh ∩ ball 0 2)).card :=
    ⟨_, rfl⟩
  have hcntle : ∀ hh s, (cnt hh s : ℝ) ≤ Kt * V hh := by
    intro hh s
    rw [hcnt, hVdef]
    exact count_translate_le hKt.le hcount (hP'conv hh) (hP'plusfin hh) (σg s)
  have hgrid : ∀ hh, ∑ s : Fin mG, (cnt hh s : ℝ) ≤ m * (2 * V hh / (ρ / 2) ^ 2) := by
    intro hh
    have he : ∑ s : Fin mG, (cnt hh s : ℝ) =
        ∑ ab : Fin (2 * M + 1) × Fin (2 * M + 1),
          ((Finset.univ.filter (fun i => tube ρ (x i + sgrid (ρ / 2) M ab.1 ab.2) (v i) ⊆
            P hh ∩ ball 0 2)).card : ℝ) := by
      subst hmGdef
      rw [← Equiv.sum_comp finProdFinEquiv]
      refine Finset.sum_congr rfl fun ab _ => ?_
      simp only [hcnt, σg, Equiv.symm_apply_apply]
    rw [he]
    refine (grid_sum_le hhpos le_rfl (fun i => hv2 i) M (hP'fin hh)).trans ?_
    gcongr
    exact hVP hh
  obtain ⟨hX01, hXavg⟩ := load_bounds cnt V hKt hV0 hcntle hgrid hhpos hm hN2 hxq hM2
  -- the selection
  obtain ⟨φ, hφ⟩ := h57 ρ 1 H mG N (fun _ hh s => (cnt hh s : ℝ) / (Kt * V hh)) hρ hρ1 hmG hH
    hX01 hXavg
  refine ⟨N, fun j => σg (φ j), hxq ▸ hN1, hxq ▸ hN2, fun j => ⟨hσ2 _, hσsq _⟩, ?_⟩
  -- counts on the test sets
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hρε : 0 < ρ ^ (-ε') := Real.rpow_pos_of_pos hρ _
  obtain ⟨B55, hB55⟩ : ∃ B55 : ℝ, B55 = 27 * C57 * ρ ^ (-ε') * Real.log 3 * Kt * ρ ^ 2 :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ B55 := by rw [hB55]; positivity
  have htest : ∀ (k : Fin 1) (hh : Fin H), ENNReal.ofReal (((Set.ncard {q : Fin N × Fin m |
      (fun _ : Fin m => (0 : Fin 1)) q.2 = k ∧
        tube ρ (x q.2 + σg (φ q.1)) (v q.2) ⊆ P hh} : ℕ) : ℝ) * ρ ^ 2) ≤
      ENNReal.ofReal B55 * volume (P hh) := by
    intro k hh
    have hset : {q : Fin N × Fin m | (fun _ : Fin m => (0 : Fin 1)) q.2 = k ∧
        tube ρ (x q.2 + σg (φ q.1)) (v q.2) ⊆ P hh} =
        ↑(Finset.univ.filter (fun q : Fin N × Fin m =>
          tube ρ (x q.2 + σg (φ q.1)) (v q.2) ⊆ P hh ∩ ball 0 2)) := by
      ext q
      simp only [mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and,
        Subsingleton.elim ((fun _ : Fin m => (0 : Fin 1)) q.2) k]
      constructor
      · intro hq; exact subset_inter hq ((hTball _ _).trans (ball_subset_ball (by norm_num)))
      · intro hq; exact hq.trans inter_subset_left
    rw [hset, Set.ncard_coe_finset]
    have hfib : ((Finset.univ.filter (fun q : Fin N × Fin m =>
        tube ρ (x q.2 + σg (φ q.1)) (v q.2) ⊆ P hh ∩ ball 0 2)).card : ℝ) =
        ∑ j : Fin N, (cnt hh (φ j) : ℝ) := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcnt]
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    have hsel := hφ k hh
    have hlog3 : Real.log (2 + ((1 : ℕ) : ℝ)) = Real.log 3 := by norm_num
    rw [hlog3] at hsel
    have hcs := selected_count_le (cnt hh) φ hKt (hV0 hh) (hcntle hh) hsel (by positivity)
    have hfinal : ((Finset.univ.filter (fun q : Fin N × Fin m =>
        tube ρ (x q.2 + σg (φ q.1)) (v q.2) ⊆ P hh ∩ ball 0 2)).card : ℝ) * ρ ^ 2 ≤
        B55 * (volume (P hh)).toReal := by
      rw [hfib, hB55]
      have h27 := hV27 hh
      have hC : 0 ≤ C57 * ρ ^ (-ε') * Real.log 3 := by positivity
      calc (∑ j : Fin N, (cnt hh (φ j) : ℝ)) * ρ ^ 2
          ≤ C57 * ρ ^ (-ε') * Real.log 3 * (Kt * V hh) * ρ ^ 2 := by gcongr
        _ ≤ C57 * ρ ^ (-ε') * Real.log 3 * (Kt * (27 * (volume (P hh)).toReal)) * ρ ^ 2 := by
            gcongr
        _ = 27 * C57 * ρ ^ (-ε') * Real.log 3 * Kt * ρ ^ 2 * (volume (P hh)).toReal := by ring
    rw [← ENNReal.ofReal_toReal (hPprop hh).2.2.2, ← ENNReal.ofReal_mul hB0]
    exact ENNReal.ofReal_le_ofReal hfinal
  -- the transfer to all convex sets
  intro W hW
  have htr' := htr 1 N m (fun q => x q.2 + σg (φ q.1)) (fun q => v q.2)
    (fun _ => (0 : Fin 1)) B55
    (fun q => ⟨hv _, (hTball _ _).trans (ball_subset_ball (by norm_num))⟩) htest 0 W hW
  have hset : {q : Fin N × Fin m | (fun _ : Fin m => (0 : Fin 1)) q.2 = 0 ∧
      tube ρ (x q.2 + σg (φ q.1)) (v q.2) ⊆ W} =
      {q : Fin N × Fin m | tube ρ (x q.2 + σg (φ q.1)) (v q.2) ⊆ W} := by
    ext q; simp
  rw [hset] at htr'
  have hρ2 : 0 < ρ ^ 2 := by positivity
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)] at htr'
  have hB : D55 * B55 = D55 * (27 * C57 * ρ ^ (-ε') * Real.log 3 * Kt) * ρ ^ 2 := by
    rw [hB55]; ring
  rw [hB, ENNReal.ofReal_mul' hρ2.le, mul_right_comm] at htr'
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hρ2).ne' ENNReal.ofReal_ne_top).mp htr'

end WangZahlLot.Obl.wz_intermediate_twist_normalization
