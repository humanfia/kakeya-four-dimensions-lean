-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_measurable_angular_selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_measurable_angular_selection`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_measurable_angular_selection`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_measurable_angular_selection/`
belong to this obligation.

## Proof

Take `A = 2`. Every point `p` has an incidence pattern `S p = {i | p ∈ Y i}`; all choices
below depend on `p` only through `S p`, so they are measurable (there are finitely many
patterns, and each pattern class is a finite intersection of the `Y i` and their complements).

Let `K` be such that `δ ≤ 2^{-K} < 2δ`. For a pattern `S`, let `G S ρ` be the largest number of
directions of `S` within projective distance `ρ` of one direction `v j`, `j ∈ S`. Choose
`k ≤ K` maximizing `G S (2 * 2^{-k}) / (2^{-k})^β`, and a center `j` realizing
`G S (2 * 2^{-k})`. Keep the directions within `2θ` of `v j`, `θ = 2^{-k}`.

* Since `G S 2 = #S`, maximality at `k = 0` gives `#keep ≥ θ^β #S ≥ δ^β #S`.
* An `r`-cap around any `u` meeting `keep` lies in a `2r`-cap around a direction of `S`;
  rounding `r` up to `2^{-k'} ∈ [r, 2r)` (`k' ≤ K`) and maximality at `k'` gives
  `#(keep ∩ cap) ≤ (2^{-k'}/θ)^β #keep ≤ 2 (r/θ)^β #keep`; for `r ≥ θ` the bound is trivial.

Finally pigeonhole the scale label `k ∈ {0, …, K}` by incidence mass, losing a factor
`K + 1 ≤ δ^{-β}` once `δ ≤ exp(-4/β²)`.
-/

namespace WangZahlLot.Obl.wz_measurable_angular_selection

open MeasureTheory

/-- The projective distance `min ‖x - y‖ ‖x + y‖`. -/
def pd {E : Type*} [NormedAddCommGroup E] (x y : E) : ℝ := min ‖x - y‖ ‖x + y‖

section pd

variable {E : Type*} [NormedAddCommGroup E]

lemma pd_comm (x y : E) : pd x y = pd y x := by
  unfold pd
  rw [norm_sub_rev, add_comm]

lemma pd_triangle (x y z : E) : pd x z ≤ pd x y + pd y z := by
  unfold pd
  have h1 : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub x y z
  have h2 : ‖x + z‖ ≤ ‖x - y‖ + ‖y + z‖ := by
    have : x + z = (x - y) + (y + z) := by abel
    rw [this]; exact norm_add_le _ _
  have h3 : ‖x - z‖ ≤ ‖x + y‖ + ‖y + z‖ := by
    have : x - z = (x + y) - (y + z) := by abel
    rw [this]; exact norm_sub_le _ _
  have h4 : ‖x + z‖ ≤ ‖x + y‖ + ‖y - z‖ := by
    have : x + z = (x + y) - (y - z) := by abel
    rw [this]; exact norm_sub_le _ _
  rcases le_total ‖x - y‖ ‖x + y‖ with ha | ha <;>
    rcases le_total ‖y - z‖ ‖y + z‖ with hb | hb
  · rw [min_eq_left ha, min_eq_left hb]; exact min_le_of_left_le h1
  · rw [min_eq_left ha, min_eq_right hb]; exact min_le_of_right_le h2
  · rw [min_eq_right ha, min_eq_left hb]; exact min_le_of_right_le h4
  · rw [min_eq_right ha, min_eq_right hb]; exact min_le_of_left_le h3

lemma pd_le_two {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : pd x y ≤ 2 := by
  unfold pd
  refine min_le_of_left_le ?_
  calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    _ = 2 := by rw [hx, hy]; norm_num

end pd

section counting

variable {E : Type*} [NormedAddCommGroup E] {n : ℕ} (v : Fin n → E)

/-- The number of directions of `S` within projective distance `ρ` of `v j`. -/
noncomputable def cnt (S : Finset (Fin n)) (j : Fin n) (ρ : ℝ) : ℕ :=
  (S.filter (fun i => pd (v i) (v j) ≤ ρ)).card

/-- The largest number of directions of `S` in a `ρ`-cap centered at a direction of `S`. -/
noncomputable def G (S : Finset (Fin n)) (ρ : ℝ) : ℕ := S.sup (fun j => cnt v S j ρ)

lemma G_mono (S : Finset (Fin n)) {ρ ρ' : ℝ} (h : ρ ≤ ρ') : G v S ρ ≤ G v S ρ' := by
  unfold G
  apply Finset.sup_mono_fun
  intro j _
  unfold cnt
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.trans h⟩

lemma card_le_G (hv : ∀ i, ‖v i‖ = 1) (S : Finset (Fin n)) : S.card ≤ G v S 2 := by
  rcases S.eq_empty_or_nonempty with h | ⟨j, hj⟩
  · simp [h]
  · calc S.card = cnt v S j 2 := by
          unfold cnt
          congr 1
          symm
          apply Finset.filter_true_of_mem
          intro i _
          exact pd_le_two (hv i) (hv j)
      _ ≤ G v S 2 := Finset.le_sup (f := fun j => cnt v S j 2) hj

lemma cap_le_G (S T : Finset (Fin n)) (hTS : T ⊆ S) (u : E) (r : ℝ) :
    (T.filter (fun i => pd (v i) u ≤ r)).card ≤ G v S (2 * r) := by
  rcases (T.filter (fun i => pd (v i) u ≤ r)).eq_empty_or_nonempty with h | ⟨i₁, hi₁⟩
  · rw [h]; simp
  · rw [Finset.mem_filter] at hi₁
    calc (T.filter (fun i => pd (v i) u ≤ r)).card ≤ cnt v S i₁ (2 * r) := by
          unfold cnt
          apply Finset.card_le_card
          intro i hi
          rw [Finset.mem_filter] at hi ⊢
          refine ⟨hTS hi.1, ?_⟩
          calc pd (v i) (v i₁) ≤ pd (v i) u + pd u (v i₁) := pd_triangle _ _ _
            _ = pd (v i) u + pd (v i₁) u := by rw [pd_comm u]
            _ ≤ r + r := add_le_add hi.2 hi₁.2
            _ = 2 * r := by ring
      _ ≤ G v S (2 * r) := Finset.le_sup (f := fun j => cnt v S j (2 * r)) (hTS hi₁.1)

/-- The selection for one incidence pattern `S`: a dyadic scale `θ = (1/2)^k`, `k ≤ K`, and a
center `j` whose `2θ`-cap keeps a `δ^β` fraction of `S` and is robust at all scales `r ≥ δ`. -/
lemma local_select (hv : ∀ i, ‖v i‖ = 1) {β δ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hδ : 0 < δ)
    {K : ℕ} (hK1 : δ ≤ (1 / 2 : ℝ) ^ K) (hK2 : (1 / 2 : ℝ) ^ K < 2 * δ) (j₀ : Fin n)
    (S : Finset (Fin n)) : ∃ (k : ℕ) (j : Fin n), k ≤ K ∧
      δ ^ β * (S.card : ℝ) ≤
        ((S.filter (fun i => pd (v i) (v j) ≤ 2 * (1 / 2 : ℝ) ^ k)).card : ℝ) ∧
      ∀ (u : E) (r : ℝ), δ ≤ r →
        (((S.filter (fun i => pd (v i) (v j) ≤ 2 * (1 / 2 : ℝ) ^ k)).filter
            (fun i => pd (v i) u ≤ r)).card : ℝ)
          ≤ 2 * (r / (1 / 2 : ℝ) ^ k) ^ β *
            ((S.filter (fun i => pd (v i) (v j) ≤ 2 * (1 / 2 : ℝ) ^ k)).card : ℝ) := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨0, j₀, Nat.zero_le _, ?_, ?_⟩
    · simp [hS]
    · intro u r _
      simp [hS]
  -- the quantity maximized over the scales
  set h : ℕ → ℝ := fun k => (G v S (2 * (1 / 2 : ℝ) ^ k) : ℝ) / ((1 / 2 : ℝ) ^ k) ^ β with hh
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image (Finset.range (K + 1)) h
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩
  have hk₀K : k₀ ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₀)
  obtain ⟨j, hjS, hj⟩ :=
    Finset.exists_mem_eq_sup S hS (fun j => cnt v S j (2 * (1 / 2 : ℝ) ^ k₀))
  refine ⟨k₀, j, hk₀K, ?_, ?_⟩
  all_goals
    set θ : ℝ := (1 / 2 : ℝ) ^ k₀ with hθ
    set keep := S.filter (fun i => pd (v i) (v j) ≤ 2 * θ) with hkeep
    have hG : G v S (2 * θ) = keep.card := hj
    have hθpos : 0 < θ := by positivity
    have hθβ : 0 < θ ^ β := Real.rpow_pos_of_pos hθpos β
    have hhk₀ : h k₀ = (keep.card : ℝ) / θ ^ β := by
      simp only [hh, hθ] at hG ⊢
      rw [hG]
  · -- mass
    have h0 := hmax 0 (Finset.mem_range.mpr (Nat.succ_pos K))
    rw [hhk₀] at h0
    simp only [hh, pow_zero, mul_one, Real.one_rpow, div_one] at h0
    rw [le_div_iff₀ hθβ] at h0
    have hδθ : δ ≤ θ := hK1.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk₀K)
    have hδβ : δ ^ β ≤ θ ^ β := Real.rpow_le_rpow hδ.le hδθ hβ.le
    have hS2 : (S.card : ℝ) ≤ (G v S 2 : ℝ) := by exact_mod_cast card_le_G v hv S
    calc δ ^ β * (S.card : ℝ) ≤ θ ^ β * (G v S 2 : ℝ) :=
          mul_le_mul hδβ hS2 (Nat.cast_nonneg _) hθβ.le
      _ = (G v S 2 : ℝ) * θ ^ β := mul_comm _ _
      _ ≤ keep.card := h0
  · -- robustness
    intro u r hr
    have hrpos : 0 < r := hδ.trans_le hr
    have hM1 : (keep.filter (fun i => pd (v i) u ≤ r)).card ≤ keep.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hM2 : (keep.filter (fun i => pd (v i) u ≤ r)).card ≤ G v S (2 * r) :=
      cap_le_G v S keep (Finset.filter_subset _ _) u r
    have hkeep0 : (0 : ℝ) ≤ keep.card := Nat.cast_nonneg _
    by_cases hrθ : θ ≤ r
    · have h1 : 1 ≤ (r / θ) ^ β :=
        Real.one_le_rpow (by rw [le_div_iff₀ hθpos]; linarith) hβ.le
      calc ((keep.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤ keep.card := by
            exact_mod_cast hM1
        _ ≤ 2 * (r / θ) ^ β * keep.card := by nlinarith
    · push Not at hrθ
      have hθ1 : θ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hr1 : r ≤ 1 := hrθ.le.trans hθ1
      obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (x := 1 / r) (y := (2 : ℝ))
        (by rw [le_div_iff₀ hrpos]; linarith) (by norm_num)
      -- the dyadic scale `k` with `r ≤ (1/2)^k < 2r`
      set k := min m K with hk
      have hkK : k ∈ Finset.range (K + 1) := by
        rw [Finset.mem_range]; omega
      have hkm : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (min_le_left _ _)
      have hm1' : r ≤ (1 / 2 : ℝ) ^ m := by
        rw [one_div_pow, le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ hrpos] at hm1
        linarith
      have hk1 : r ≤ (1 / 2 : ℝ) ^ k := hm1'.trans hkm
      have hk2 : (1 / 2 : ℝ) ^ k < 2 * r := by
        rcases le_total m K with hmK | hmK
        · have : k = m := min_eq_left hmK
          rw [this, one_div_pow, div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hrpos, pow_succ] at hm2
          nlinarith
        · have : k = K := min_eq_right hmK
          rw [this]
          linarith
      have hkpos : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
      -- maximality at the scale `k`
      have hGk : (G v S (2 * (1 / 2 : ℝ) ^ k) : ℝ) ≤ keep.card * ((1 / 2 : ℝ) ^ k / θ) ^ β := by
        have := hmax k hkK
        rw [hhk₀] at this
        simp only [hh] at this
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hkpos β)] at this
        rw [Real.div_rpow hkpos.le hθpos.le]
        calc (G v S (2 * (1 / 2 : ℝ) ^ k) : ℝ) ≤ keep.card / θ ^ β * ((1 / 2 : ℝ) ^ k) ^ β :=
              this
          _ = keep.card * (((1 / 2 : ℝ) ^ k) ^ β / θ ^ β) := by ring
      have h2β : (2 : ℝ) ^ β ≤ 2 := by
        calc (2 : ℝ) ^ β ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
          _ = 2 := Real.rpow_one 2
      calc ((keep.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤ (G v S (2 * r) : ℝ) := by
            exact_mod_cast hM2
        _ ≤ (G v S (2 * (1 / 2 : ℝ) ^ k) : ℝ) := by
            exact_mod_cast G_mono v S (by linarith)
        _ ≤ keep.card * ((1 / 2 : ℝ) ^ k / θ) ^ β := hGk
        _ ≤ keep.card * (2 * r / θ) ^ β := by
            gcongr
        _ = keep.card * (2 ^ β * (r / θ) ^ β) := by
            rw [mul_div_assoc, Real.mul_rpow (by norm_num) (by positivity)]
        _ ≤ keep.card * (2 * (r / θ) ^ β) := by
            gcongr
        _ = 2 * (r / θ) ^ β * keep.card := by ring

end counting

/-- Every set of points defined through the incidence pattern is measurable. -/
lemma measurableSet_pattern {E : Type*} [MeasurableSpace E] {n : ℕ} {Y : Fin n → Set E}
    (hY : ∀ i, MeasurableSet (Y i)) (S : E → Finset (Fin n)) (hS : ∀ p i, i ∈ S p ↔ p ∈ Y i)
    (P : Finset (Fin n) → Prop) : MeasurableSet {p | P (S p)} := by
  have hfib : ∀ T : Finset (Fin n), MeasurableSet {p | S p = T} := by
    intro T
    have : {p | S p = T} = ⋂ i, {p | p ∈ Y i ↔ i ∈ T} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.ext_iff, hS]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hi : i ∈ T
    · have : {p | p ∈ Y i ↔ i ∈ T} = Y i := by ext p; simp [hi]
      rw [this]; exact hY i
    · have : {p | p ∈ Y i ↔ i ∈ T} = (Y i)ᶜ := by ext p; simp [hi]
      rw [this]; exact (hY i).compl
  have : {p | P (S p)} = ⋃ T ∈ {T | P T}, {p | S p = T} := by
    ext p; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) (fun T _ => hfib T)

/-- `K + 1 ≤ δ^{-β}` when `δ ≤ 2^{-K}` and `δ ≤ exp(-4/β²)`. -/
lemma log_count_bound {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hδd : δ ≤ Real.exp (-(4 / β ^ 2)))
    {K : ℕ} (hK : δ ≤ (1 / 2 : ℝ) ^ K) : ((K : ℝ) + 1) * δ ^ β ≤ 1 := by
  set L := -Real.log δ with hL
  have hL4 : 4 / β ^ 2 ≤ L := by
    have := Real.log_le_log hδ hδd
    rw [Real.log_exp] at this
    linarith
  have hL0 : 0 ≤ L := le_trans (by positivity) hL4
  have hKL : (K : ℝ) * Real.log 2 ≤ L := by
    have := Real.log_le_log hδ hK
    rw [Real.log_pow, one_div, Real.log_inv] at this
    linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hK2L : (K : ℝ) ≤ 2 * L := by nlinarith
  have hβL : 4 ≤ β ^ 2 * L := by
    rw [div_le_iff₀ (by positivity)] at hL4
    linarith
  have hexp : (K : ℝ) + 1 ≤ Real.exp (β * L) := by
    have := Real.quadratic_le_exp_of_nonneg (x := β * L) (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hβL) hL0, mul_nonneg hβ.le hL0]
  have hδβ : δ ^ β = Real.exp (-(β * L)) := by
    rw [Real.rpow_def_of_pos hδ, hL]
    ring_nf
  rw [hδβ]
  calc ((K : ℝ) + 1) * Real.exp (-(β * L)) ≤ Real.exp (β * L) * Real.exp (-(β * L)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The statement, for any measure and with `D` the projective distance `pd`. -/
theorem main_general {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (μ : Measure E) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ d : ℝ, 0 < d ∧ d ≤ (1 / 100 : ℝ) ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ (n : ℕ) (v : Fin n → E) (Y : Fin n → Set E), 0 < n →
    (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) → (∀ i, μ (Y i) ≠ ⊤) →
    ∃ θ : ℝ, δ ≤ θ ∧ θ ≤ 1 ∧ ∃ (Z : Fin n → Set E) (a : E → Fin n),
    (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧ (∀ i, MeasurableSet {p : E | a p = i}) ∧
    (∀ p i, p ∈ Z i → pd (v i) (v (a p)) ≤ A * θ) ∧
    (∀ p u r, ‖u‖ = 1 → δ ≤ r → (Set.ncard {i : Fin n | p ∈ Z i ∧ pd (v i) u ≤ r} : ℝ) ≤
      A * (r / θ) ^ β * (Set.ncard {i : Fin n | p ∈ Z i} : ℝ)) ∧
    ENNReal.ofReal (δ ^ (A * β)) * Finset.sum Finset.univ (fun i : Fin n => μ (Y i)) ≤
      Finset.sum Finset.univ (fun i : Fin n => μ (Z i)) := by
  refine ⟨2, by norm_num, fun β hβ hβ1 => ?_⟩
  refine ⟨min (1 / 100) (Real.exp (-(4 / β ^ 2))), by positivity, min_le_left _ _, ?_⟩
  intro δ hδ hδd n v Y hn hv hY hYfin
  classical
  have hδ1 : δ ≤ 1 := hδd.trans ((min_le_left _ _).trans (by norm_num))
  -- the dyadic bottom scale
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℕ, δ ≤ (1 / 2 : ℝ) ^ K ∧ (1 / 2 : ℝ) ^ K < 2 * δ := by
    obtain ⟨K, h1, h2⟩ := exists_nat_pow_near (x := 1 / δ) (y := (2 : ℝ))
      (by rw [le_div_iff₀ hδ]; linarith) (by norm_num)
    refine ⟨K, ?_, ?_⟩
    · rw [one_div_pow, le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ hδ] at h1
      linarith
    · rw [one_div_pow, div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ, pow_succ] at h2
      nlinarith
  have hlog : ((K : ℝ) + 1) * δ ^ β ≤ 1 :=
    log_count_bound hβ hδ (hδd.trans (min_le_right _ _)) hK1
  -- the selection on every incidence pattern
  choose k₀ j₀ hk₀ hmass hrob using
    fun S => local_select v hv hβ hβ1 hδ hK1 hK2 ⟨0, hn⟩ S
  set S : E → Finset (Fin n) := fun p => Finset.univ.filter (fun i => p ∈ Y i) with hSdef
  have hS : ∀ p i, i ∈ S p ↔ p ∈ Y i := by
    intro p i; simp [hSdef]
  set keep : Finset (Fin n) → Finset (Fin n) :=
    fun T => T.filter (fun i => pd (v i) (v (j₀ T)) ≤ 2 * (1 / 2 : ℝ) ^ (k₀ T)) with hkeep
  -- the refinement at the scale label `k`
  set Z : ℕ → Fin n → Set E := fun k i => {p | i ∈ keep (S p) ∧ k₀ (S p) = k} with hZdef
  have hZmeas : ∀ k i, MeasurableSet (Z k i) := fun k i =>
    measurableSet_pattern hY S hS (fun T => i ∈ keep T ∧ k₀ T = k)
  -- incidence masses as integrals
  have hYsum : ∑ i, μ (Y i) = ∫⁻ p, ∑ i, (Y i).indicator (1 : E → ENNReal) p ∂μ := by
    rw [lintegral_finsetSum _ (fun i _ => measurable_one.indicator (hY i))]
    exact Finset.sum_congr rfl (fun i _ => (lintegral_indicator_one (hY i)).symm)
  have hZsum : ∑ k ∈ Finset.range (K + 1), ∑ i, μ (Z k i) =
      ∫⁻ p, ∑ k ∈ Finset.range (K + 1), ∑ i, (Z k i).indicator (1 : E → ENNReal) p ∂μ := by
    rw [lintegral_finsetSum _ (fun k _ => Finset.measurable_sum _
      (fun i _ => measurable_one.indicator (hZmeas k i)))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [lintegral_finsetSum _ (fun i _ => measurable_one.indicator (hZmeas k i))]
    exact Finset.sum_congr rfl (fun i _ => (lintegral_indicator_one (hZmeas k i)).symm)
  have hpt : ∀ p, ENNReal.ofReal (δ ^ β) * ∑ i, (Y i).indicator (1 : E → ENNReal) p ≤
      ∑ k ∈ Finset.range (K + 1), ∑ i, (Z k i).indicator (1 : E → ENNReal) p := by
    intro p
    have e1 : ∑ i, (Y i).indicator (1 : E → ENNReal) p = ((S p).card : ENNReal) := by
      simp only [Set.indicator_apply, Pi.one_apply]
      rw [Finset.sum_boole]
    have e2 : ∑ i, (Z (k₀ (S p)) i).indicator (1 : E → ENNReal) p =
        ((keep (S p)).card : ENNReal) := by
      simp only [Set.indicator_apply, Pi.one_apply]
      rw [Finset.sum_boole]
      congr 2
      ext i
      simp [hZdef]
    calc ENNReal.ofReal (δ ^ β) * ∑ i, (Y i).indicator (1 : E → ENNReal) p
        = ENNReal.ofReal (δ ^ β) * ((S p).card : ENNReal) := by rw [e1]
      _ = ENNReal.ofReal (δ ^ β * (S p).card) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((keep (S p)).card) := ENNReal.ofReal_le_ofReal (hmass (S p))
      _ = ((keep (S p)).card : ENNReal) := ENNReal.ofReal_natCast _
      _ = ∑ i, (Z (k₀ (S p)) i).indicator (1 : E → ENNReal) p := e2.symm
      _ ≤ ∑ k ∈ Finset.range (K + 1), ∑ i, (Z k i).indicator (1 : E → ENNReal) p :=
          Finset.single_le_sum (f := fun k => ∑ i, (Z k i).indicator (1 : E → ENNReal) p)
            (fun k _ => zero_le)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le (hk₀ (S p))))
  have hmassTot : ENNReal.ofReal (δ ^ β) * ∑ i, μ (Y i) ≤
      ∑ k ∈ Finset.range (K + 1), ∑ i, μ (Z k i) := by
    rw [hYsum, hZsum]
    calc ENNReal.ofReal (δ ^ β) * ∫⁻ p, ∑ i, (Y i).indicator (1 : E → ENNReal) p ∂μ
        ≤ ∫⁻ p, ENNReal.ofReal (δ ^ β) * ∑ i, (Y i).indicator (1 : E → ENNReal) p ∂μ :=
          lintegral_const_mul_le _ _
      _ ≤ _ := lintegral_mono hpt
  -- pigeonhole the scale label
  obtain ⟨k, hkK, hk⟩ : ∃ k ∈ Finset.range (K + 1),
      ENNReal.ofReal (δ ^ (2 * β)) * ∑ i, μ (Y i) ≤ ∑ i, μ (Z k i) := by
    by_contra hcon
    push Not at hcon
    have hlt := ENNReal.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩ hcon
    rw [Finset.sum_const, Finset.card_range] at hlt
    have hle : (K + 1) • (ENNReal.ofReal (δ ^ (2 * β)) * ∑ i, μ (Y i)) ≤
        ENNReal.ofReal (δ ^ β) * ∑ i, μ (Y i) := by
      rw [nsmul_eq_mul, ← mul_assoc]
      gcongr
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [show 2 * β = β + β by ring, Real.rpow_add hδ]
      push_cast
      have := Real.rpow_pos_of_pos hδ β
      nlinarith
    exact lt_irrefl _ ((hlt.trans_le hle).trans_le hmassTot)
  have hkK' : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkK)
  refine ⟨(1 / 2 : ℝ) ^ k, hK1.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkK'),
    pow_le_one₀ (by norm_num) (by norm_num), Z k, fun p => j₀ (S p), hZmeas k, ?_, ?_, ?_, ?_, hk⟩
  · -- `Z ⊆ Y`
    intro i p hp
    have : i ∈ S p := Finset.mem_of_mem_filter _ hp.1
    exact (hS p i).mp this
  · -- the center has measurable fibers
    intro i
    exact measurableSet_pattern hY S hS (fun T => j₀ T = i)
  · -- the selected directions lie in the cap around the center
    intro p i hp
    have := (Finset.mem_filter.mp hp.1).2
    rw [hp.2] at this
    exact this
  · -- robustness
    intro p u r hu hr
    by_cases hp : k₀ (S p) = k
    · have h1 : {i : Fin n | p ∈ Z k i} = ↑(keep (S p)) := by
        ext i; simp [hZdef, hp]
      have h2 : {i : Fin n | p ∈ Z k i ∧ pd (v i) u ≤ r} =
          ↑((keep (S p)).filter (fun i => pd (v i) u ≤ r)) := by
        ext i; simp [hZdef, hp]
      rw [h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset, ← hp]
      exact hrob (S p) u r hr
    · have h1 : {i : Fin n | p ∈ Z k i} = ∅ := by
        ext i; simp [hZdef, hp]
      have h2 : {i : Fin n | p ∈ Z k i ∧ pd (v i) u ≤ r} = ∅ := by
        ext i; simp [hZdef, hp]
      rw [h1, h2]
      simp

end WangZahlLot.Obl.wz_measurable_angular_selection

theorem WangZahlLot.wz_measurable_angular_selection : (fun (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) (D:(EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ) => ∃ A:ℝ, 1 ≤ A ∧ ∀ β:ℝ, 0 < β → β ≤ 1 → ∃ d:ℝ, 0 < d ∧ d ≤ (1 / 100:ℝ) ∧ ∀ δ:ℝ, 0 < δ → δ ≤ d → ∀ (n:ℕ) (v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))), 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) → (∀ i, μ (Y i) ≠ ⊤) → ∃ θ:ℝ, δ ≤ θ ∧ θ ≤ 1 ∧ ∃ (Z:Fin n → Set (EuclideanSpace ℝ (Fin 3))) (a:(EuclideanSpace ℝ (Fin 3)) → Fin n), (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧ (∀ i, MeasurableSet {p:(EuclideanSpace ℝ (Fin 3)) | a p = i}) ∧ (∀ p i, p ∈ Z i → D (v i) (v (a p)) ≤ A * θ) ∧ (∀ p u r, ‖u‖ = 1 → δ ≤ r → (Set.ncard {i:Fin n | p ∈ Z i ∧ D (v i) (u) ≤ r}:ℝ) ≤ A * (r / θ) ^ β * (Set.ncard {i:Fin n | p ∈ Z i}:ℝ)) ∧ ENNReal.ofReal (δ ^ (A * β)) * Finset.sum Finset.univ (fun i:Fin n => μ (Y i)) ≤ Finset.sum Finset.univ (fun i:Fin n => μ (Z i))) MeasureTheory.volume (fun (v w:(EuclideanSpace ℝ (Fin 3))) => min ‖v - w‖ ‖v + w‖) :=
  WangZahlLot.Obl.wz_measurable_angular_selection.main_general MeasureTheory.volume
