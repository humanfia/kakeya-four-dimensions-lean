-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Seed.Kakeya.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Seed for `wang_zahl_kakeya_dimH`: the easy half and the reduction to a lower bound

Everything here is elementary bookkeeping around the challenge statement
`dimH K = 3` for a Kakeya set `K ⊆ ℝ³` (`LeanEval.Analysis.WangZahlKakeya.IsKakeya`):

* `dimH_le_three`: the upper bound `dimH K ≤ 3` holds for every subset of `ℝ³`.
* `dimH_eq_three_iff`, `dimH_eq_three_of_le`: the challenge is equivalent to `3 ≤ dimH K`.
* `three_le_dimH_iff`: `3 ≤ dimH K` iff `μH[d] K ≠ 0` for every `d < 3` (the form used by the
  discretization argument: assume `μH[d] K = 0` for some `d < 3` and derive a contradiction).
* `exists_cover_of_hausdorffMeasure_eq_zero` (and the positive-exponent variant `'`): a null
  set for `μH[d]` has countable covers of arbitrarily small mesh and arbitrarily small
  `d`-dimensional sum.
* `exists_finite_ball_cover_of_hausdorffMeasure_eq_zero`: for a compact null set the cover can be
  taken to be finitely many open balls `ball (c n) (ρ n)` with `0 < ρ n ≤ r` and
  `∑ ρ n ^ s < η`. This is step 1 of the classical "tube estimate ⇒ Hausdorff dimension"
  reduction (child `kakeya_three_le_dimH_of_tube_estimate` of the proposed split).
* `exists_le_of_le_tsum` (with `tsum_inv_succ_sq_le_two`): the polynomially weighted pigeonhole
  `w ≤ ∑ f k ⇒ ∃ k, f k ≥ w / (4 (k+1)²)`, used for the dyadic-scale pigeonholing in that
  reduction.
* `IsKakeya.*`: compactness, nonemptiness, the unit segment in each direction written with
  Mathlib's `segment`, and the trivial bound `1 ≤ dimH K`.
* `dimH_eq_three_of_lower_bound`: the root follows from the lower bound for all Kakeya sets.

Nothing here touches the hard part (Wang-Zahl's tube estimate); see `NOTES.md`.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace WangZahlLot.Seed.Kakeya

open LeanEval.Analysis.WangZahlKakeya

/-- The ambient space of the challenge has dimension `3`. -/
theorem finrank_space : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin

/-- The Hausdorff dimension of the whole space `ℝ³` is `3`. -/
theorem dimH_univ_space : dimH (univ : Set Space) = 3 := by
  rw [Real.dimH_univ_eq_finrank Space, finrank_space]
  rfl

/-- **Upper bound.** Every subset of `ℝ³` has Hausdorff dimension at most `3`. -/
theorem dimH_le_three (K : Set Space) : dimH K ≤ 3 :=
  (dimH_mono (subset_univ K)).trans_eq dimH_univ_space

/-- The challenge `dimH K = 3` is equivalent to the lower bound `3 ≤ dimH K`. -/
theorem dimH_eq_three_iff (K : Set Space) : dimH K = 3 ↔ 3 ≤ dimH K :=
  ⟨fun h => h.ge, fun h => le_antisymm (dimH_le_three K) h⟩

theorem dimH_eq_three_of_le {K : Set Space} (h : 3 ≤ dimH K) : dimH K = 3 :=
  (dimH_eq_three_iff K).2 h

/-- `3 ≤ dimH K` iff no `d`-dimensional Hausdorff measure with `d < 3` vanishes on `K`. -/
theorem three_le_dimH_iff (K : Set Space) :
    3 ≤ dimH K ↔ ∀ d : ℝ≥0, d < 3 → μH[d] K ≠ 0 := by
  constructor
  · intro h d hd
    have hlt : (d : ℝ≥0∞) < dimH K := by
      refine lt_of_lt_of_le ?_ h
      exact_mod_cast hd
    rw [hausdorffMeasure_of_lt_dimH hlt]
    exact ENNReal.top_ne_zero
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨d, hKd, hd3⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    have hd3' : d < 3 := by exact_mod_cast hd3
    exact h d hd3' (hausdorffMeasure_of_dimH_lt hKd)

/-- Real-exponent form of `three_le_dimH_iff` (the direction used in a proof by contradiction):
if `μH[s] K ≠ 0` for every real `0 ≤ s < 3`, then `3 ≤ dimH K`. -/
theorem three_le_dimH_of_forall_real (K : Set Space)
    (h : ∀ s : ℝ, 0 ≤ s → s < 3 → μH[s] K ≠ 0) : 3 ≤ dimH K := by
  refine (three_le_dimH_iff K).2 fun d hd => ?_
  exact h d d.2 (by exact_mod_cast hd)

section Cover

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Covers of a `μH[d]`-null set.** If `μH[d] s = 0`, then for every mesh `r > 0` and every
`η > 0` there is a countable cover of `s` by sets of diameter at most `r` whose `d`-dimensional
sum (empty pieces contributing `0`) is `< η`. -/
theorem exists_cover_of_hausdorffMeasure_eq_zero {d : ℝ} {s : Set X} (h : μH[d] s = 0)
    {r η : ℝ≥0∞} (hr : 0 < r) (hη : 0 < η) :
    ∃ t : ℕ → Set X, s ⊆ ⋃ n, t n ∧ (∀ n, ediam (t n) ≤ r) ∧
      ∑' n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ d) < η := by
  rw [Measure.hausdorffMeasure_apply] at h
  have h0 := (iSup₂_eq_bot.1 h) r hr
  rw [← bot_eq_zero, ← h0] at hη
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 hη
  obtain ⟨hst, ht⟩ := iInf_lt_iff.1 ht
  obtain ⟨htr, ht⟩ := iInf_lt_iff.1 ht
  exact ⟨t, hst, htr, ht⟩

/-- Variant of `exists_cover_of_hausdorffMeasure_eq_zero` for a positive exponent: empty pieces
then contribute `0` automatically, so the sum is the plain `∑' n, ediam (t n) ^ d`. -/
theorem exists_cover_of_hausdorffMeasure_eq_zero' {d : ℝ} (hd : 0 < d) {s : Set X}
    (h : μH[d] s = 0) {r η : ℝ≥0∞} (hr : 0 < r) (hη : 0 < η) :
    ∃ t : ℕ → Set X, s ⊆ ⋃ n, t n ∧ (∀ n, ediam (t n) ≤ r) ∧
      ∑' n, ediam (t n) ^ d < η := by
  obtain ⟨t, hst, htr, ht⟩ := exists_cover_of_hausdorffMeasure_eq_zero h hr hη
  refine ⟨t, hst, htr, lt_of_le_of_lt (le_of_eq ?_) ht⟩
  congr 1
  funext n
  rcases (t n).eq_empty_or_nonempty with hn | hn
  · simp [hn, ENNReal.zero_rpow_of_pos hd]
  · simp [hn]

/-- `(a + b)^s ≤ 2^s (a^s + b^s)` for `a, b ≥ 0`, `s ≥ 0`. -/
theorem add_rpow_le_two_rpow_mul {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    (a + b) ^ s ≤ 2 ^ s * (a ^ s + b ^ s) := by
  have hm : 0 ≤ max a b := le_max_of_le_left ha
  have h1 : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  calc (a + b) ^ s ≤ (2 * max a b) ^ s :=
        Real.rpow_le_rpow (add_nonneg ha hb) h1 hs
    _ = 2 ^ s * (max a b) ^ s := Real.mul_rpow (by norm_num) hm
    _ ≤ 2 ^ s * (a ^ s + b ^ s) := by
        gcongr
        rcases le_total a b with hab | hab
        · rw [max_eq_right hab]
          have : 0 ≤ a ^ s := Real.rpow_nonneg ha s
          linarith
        · rw [max_eq_left hab]
          have : 0 ≤ b ^ s := Real.rpow_nonneg hb s
          linarith

/-- **Finite ball covers of a compact `μH[s]`-null set.** If `E` is compact, `0 < s` and
`μH[s] E = 0`, then for every `r > 0` and `η > 0` there are finitely many open balls
`ball (c n) (ρ n)`, `n ∈ F`, with `0 < ρ n ≤ r`, covering `E`, and `∑ n ∈ F, ρ n ^ s < η`.
This is the usual starting point of the "tube estimate ⇒ Hausdorff dimension" reduction. -/
theorem exists_finite_ball_cover_of_hausdorffMeasure_eq_zero {X : Type*} [MetricSpace X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X] {s : ℝ} (hs : 0 < s) {E : Set X} (hE : IsCompact E)
    (h : μH[s] E = 0) {r η : ℝ} (hr : 0 < r) (hη : 0 < η) :
    ∃ (F : Finset ℕ) (c : ℕ → X) (ρ : ℕ → ℝ), (∀ n ∈ F, 0 < ρ n ∧ ρ n ≤ r) ∧
      E ⊆ ⋃ n ∈ F, Metric.ball (c n) (ρ n) ∧ ∑ n ∈ F, ρ n ^ s < η := by
  rcases E.eq_empty_or_nonempty with hE0 | ⟨x₀, -⟩
  · exact ⟨∅, fun _ => Classical.arbitrary _, fun _ => r, by simp, by simp [hE0], by simpa⟩
  -- the budget for the cover and for the padding of the radii
  set η' : ℝ := η / (4 * 2 ^ s) with hη'
  have h2s : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hη'pos : 0 < η' := div_pos hη (by positivity)
  set θ : ℝ := min η' ((r / 2) ^ s) with hθ
  have hθpos : 0 < θ := lt_min hη'pos (Real.rpow_pos_of_pos (by positivity) s)
  -- a countable cover with small mesh and small `s`-sum
  obtain ⟨t, hEt, htr, hsum⟩ := exists_cover_of_hausdorffMeasure_eq_zero' hs h
    (r := ENNReal.ofReal (r / 2)) (η := ENNReal.ofReal η') (by simp; positivity)
    (by simpa using hη'pos)
  have hfin : ∀ n, ediam (t n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (htr n)
  set a : ℕ → ℝ := fun n => (ediam (t n)).toReal with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => ENNReal.toReal_nonneg
  have har : ∀ n, a n ≤ r / 2 := fun n =>
    ENNReal.toReal_le_of_le_ofReal (by positivity) (htr n)
  have hdiam : ∀ n, ediam (t n) = ENNReal.ofReal (a n) := fun n =>
    (ENNReal.ofReal_toReal (hfin n)).symm
  -- padding radii `ε n` with `ε n ^ s = θ / 2 ^ (n + 1)`
  set ε : ℕ → ℝ := fun n => (θ * (1 / 2) ^ (n + 1)) ^ s⁻¹ with hε
  have hεpos : ∀ n, 0 < ε n := fun n => Real.rpow_pos_of_pos (by positivity) _
  have hεs : ∀ n, ε n ^ s = θ * (1 / 2) ^ (n + 1) := fun n =>
    Real.rpow_inv_rpow (by positivity) hs.ne'
  have hεr : ∀ n, ε n ≤ r / 2 := by
    intro n
    have hle : θ * (1 / 2) ^ (n + 1) ≤ (r / 2) ^ s := by
      have h1 : θ ≤ (r / 2) ^ s := min_le_right _ _
      have h2 : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      calc θ * (1 / 2) ^ (n + 1) ≤ θ * 1 := by gcongr
        _ ≤ (r / 2) ^ s := by simpa using h1
    calc ε n ≤ ((r / 2) ^ s) ^ s⁻¹ :=
          Real.rpow_le_rpow (by positivity) hle (inv_nonneg.2 hs.le)
      _ = r / 2 := Real.rpow_rpow_inv (by positivity) hs.ne'
  -- centres and radii
  classical
  set c : ℕ → X := fun n => if hn : (t n).Nonempty then hn.some else x₀ with hc
  set ρ : ℕ → ℝ := fun n => a n + ε n with hρ
  have hcover : E ⊆ ⋃ n, Metric.ball (c n) (ρ n) := by
    intro z hz
    obtain ⟨n, hzn⟩ := mem_iUnion.1 (hEt hz)
    have hn : (t n).Nonempty := ⟨z, hzn⟩
    refine mem_iUnion.2 ⟨n, ?_⟩
    have hcn : c n ∈ t n := by simp only [hc, hn]; exact hn.some_mem
    have hed : edist z (c n) ≤ ENNReal.ofReal (a n) := hdiam n ▸ edist_le_ediam_of_mem hzn hcn
    have hd : dist z (c n) ≤ a n := by
      rw [edist_dist] at hed
      exact (ENNReal.ofReal_le_ofReal_iff (ha0 n)).1 hed
    rw [Metric.mem_ball]
    simp only [hρ]
    linarith [hεpos n]
  obtain ⟨F, hF⟩ := hE.elim_finite_subcover (fun n => Metric.ball (c n) (ρ n))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨F, c, ρ, fun n _ => ⟨by simp only [hρ]; linarith [ha0 n, hεpos n], ?_⟩, hF, ?_⟩
  · simp only [hρ]; linarith [har n, hεr n]
  -- the `s`-sum of the finite family
  have hsumA : ∑ n ∈ F, a n ^ s < η' := by
    have h1 : ∑ n ∈ F, ediam (t n) ^ s ≤ ∑' n, ediam (t n) ^ s := ENNReal.sum_le_tsum F
    have h2 : ∑ n ∈ F, ediam (t n) ^ s = ENNReal.ofReal (∑ n ∈ F, a n ^ s) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (ha0 n) s)]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hdiam n, ENNReal.ofReal_rpow_of_nonneg (ha0 n) hs.le]
    have h3 : ENNReal.ofReal (∑ n ∈ F, a n ^ s) < ENNReal.ofReal η' := h2 ▸ h1.trans_lt hsum
    exact (ENNReal.ofReal_lt_ofReal_iff hη'pos).1 h3
  have hsumE : ∑ n ∈ F, ε n ^ s ≤ θ := by
    simp only [hεs]
    rw [← Finset.mul_sum]
    have hgeo : ∑ n ∈ F, (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := by
      have hs' : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) := by
        simpa [pow_succ] using summable_geometric_two.mul_right (1 / 2 : ℝ)
      calc ∑ n ∈ F, (1 / 2 : ℝ) ^ (n + 1) ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) :=
            hs'.sum_le_tsum F (fun n _ => by positivity)
        _ = 1 := by
            rw [show (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) =
              fun n : ℕ => (1 / 2 : ℝ) * (1 / 2) ^ n from funext fun n => by ring,
              tsum_mul_left, tsum_geometric_two]
            norm_num
    calc θ * ∑ n ∈ F, (1 / 2 : ℝ) ^ (n + 1) ≤ θ * 1 := by gcongr
      _ = θ := mul_one θ
  have hθη : θ ≤ η' := min_le_left _ _
  calc ∑ n ∈ F, ρ n ^ s ≤ ∑ n ∈ F, 2 ^ s * (a n ^ s + ε n ^ s) :=
        Finset.sum_le_sum fun n _ =>
          add_rpow_le_two_rpow_mul (ha0 n) (hεpos n).le hs.le
    _ = 2 ^ s * (∑ n ∈ F, a n ^ s + ∑ n ∈ F, ε n ^ s) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ < 2 ^ s * (η' + η') :=
        mul_lt_mul_of_pos_left (add_lt_add_of_lt_of_le hsumA (hsumE.trans hθη)) h2s
    _ = η / 2 := by rw [hη']; field_simp; ring
    _ < η := by linarith

end Cover

section Pigeonhole

/-- `∑_{k ≥ 0} 1/(k+1)² ≤ 2` in `ℝ≥0∞`. -/
theorem tsum_inv_succ_sq_le_two : ∑' k : ℕ, (((k : ℝ≥0∞) + 1) ^ 2)⁻¹ ≤ 2 := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  have hR : ∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
    have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1)
    have hI : Finset.Ioo 0 (n + 1) = Finset.Ico 1 (n + 1) := by
      ext i; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range] at h
    simpa [add_comm] using h
  have hterm : ∀ k : ℕ, (((k : ℝ≥0∞) + 1) ^ 2)⁻¹ = ENNReal.ofReal ((((k : ℝ) + 1) ^ 2)⁻¹) := by
    intro k
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  calc ENNReal.ofReal (∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹) ≤ ENNReal.ofReal 2 :=
        ENNReal.ofReal_le_ofReal hR
    _ = 2 := by simp

/-- **Polynomially weighted pigeonhole.** If `0 < w < ∞` and `w ≤ ∑' k, f k`, then some term
satisfies `f k ≥ w / (4 (k+1)²)`. Used twice in the discretization: to find, for each direction, a
dyadic scale at which the cover meets the unit segment in length `≳ 1/k²`, and then to find one
scale shared by many directions (the loss `1/k²` is polynomial in `log(1/δ)`, which the factor
`δ^ε` of the tube estimate absorbs). -/
theorem exists_le_of_le_tsum {f : ℕ → ℝ≥0∞} {w : ℝ≥0∞} (hw0 : w ≠ 0) (hw : w ≠ ⊤)
    (h : w ≤ ∑' k, f k) : ∃ k : ℕ, w / (4 * ((k : ℝ≥0∞) + 1) ^ 2) ≤ f k := by
  by_contra H
  simp only [not_exists, not_le] at H
  have h1 : ∑' k, f k ≤ ∑' k : ℕ, w / (4 * ((k : ℝ≥0∞) + 1) ^ 2) :=
    ENNReal.tsum_le_tsum fun k => (H k).le
  have h2 : ∑' k : ℕ, w / (4 * ((k : ℝ≥0∞) + 1) ^ 2) =
      w / 4 * ∑' k : ℕ, (((k : ℝ≥0∞) + 1) ^ 2)⁻¹ := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp), mul_assoc]
  have h3 : w / 4 * ∑' k : ℕ, (((k : ℝ≥0∞) + 1) ^ 2)⁻¹ ≤ w / 4 * 2 := by
    gcongr
    exact tsum_inv_succ_sq_le_two
  have h4 : w / 4 * 2 < w := by
    have hw' : w / 4 * 2 = w / 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      congr 1
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
        ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    rw [hw']
    exact ENNReal.half_lt_self hw0 hw
  exact absurd (h.trans (h1.trans (h2 ▸ h3))) (not_le.2 h4)

end Pigeonhole

namespace IsKakeya

variable {K : Set Space}

theorem isCompact (hK : IsKakeya K) : IsCompact K := hK.1

theorem isClosed (hK : IsKakeya K) : IsClosed K := hK.1.isClosed

theorem isBounded (hK : IsKakeya K) : Bornology.IsBounded K := hK.1.isBounded

theorem measurableSet (hK : IsKakeya K) : MeasurableSet K := (isClosed hK).measurableSet

/-- A unit vector of `ℝ³` (the first basis vector). -/
theorem exists_unit : ∃ v : Space, ‖v‖ = 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The unit segment of a Kakeya set in direction `v`, written with Mathlib's `segment`. -/
theorem exists_segment_subset (hK : IsKakeya K) {v : Space} (hv : ‖v‖ = 1) :
    ∃ x : Space, segment ℝ x (x + v) ⊆ K := by
  obtain ⟨x, hx⟩ := hK.2 v hv
  refine ⟨x, ?_⟩
  rw [segment_eq_image']
  rintro _ ⟨t, ht, rfl⟩
  simpa using hx t ht

theorem nonempty (hK : IsKakeya K) : K.Nonempty := by
  obtain ⟨v, hv⟩ := exists_unit
  obtain ⟨x, hx⟩ := exists_segment_subset hK hv
  exact ⟨x, hx (left_mem_segment ℝ x (x + v))⟩

/-- The trivial lower bound: a Kakeya set contains a nondegenerate segment. -/
theorem one_le_dimH (hK : IsKakeya K) : 1 ≤ dimH K := by
  obtain ⟨v, hv⟩ := exists_unit
  obtain ⟨x, hx⟩ := exists_segment_subset hK hv
  have hne : x ≠ x + v := by
    intro h
    have : v = 0 := by
      have := congrArg (fun y => y - x) h
      simpa using this.symm
    simp [this] at hv
  rw [← Real.dimH_segment hne]
  exact dimH_mono hx

end IsKakeya

/-- **Root from the lower bound.** If every Kakeya set satisfies `3 ≤ dimH K`, the challenge
holds. -/
theorem dimH_eq_three_of_lower_bound
    (h : ∀ K : Set Space, IsKakeya K → 3 ≤ dimH K) {K : Set Space} (hK : IsKakeya K) :
    dimH K = 3 :=
  dimH_eq_three_of_le (h K hK)

end WangZahlLot.Seed.Kakeya
