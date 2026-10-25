/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/SheetComparison.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetJets
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetGroupMatching

/-!
# Comparison of two lists of algebraic sheets

The core of the paper's Lemma 8.3 (comparison of true and projected labels on common stable
domains), as an abstract theorem about two lists of bounded-degree algebraic sheets on one
comparison ball.

Hypotheses: reference weights `T` (of arbitrary totals), a finite pair law whose index-base
marginals are at most `CT * T` times Lebesgue measure, values of the paired sheets agreeing to
`a` at the pair events (which lie in the real ball of radius `1/4`), and a list-size bound: at
most `L * (M / a) ^ d₀` sheets of either list lie within `M` of a sheet of the first list on the
real ball of radius `1/2`.

Conclusion: the pairs whose sheets differ by at least `Λ * a` somewhere on the real ball of
radius `1/4` carry mass at most `C * CT * Λ ^ (-ε)` times the total reference weight, once
`Λ ≥ C * L ^ (1 / ε)`.

Proof (paper, "Matching with separate reference weights"): split the bad pairs by dyadic jet
discrepancy scales; at each scale group the pairs by the jet bin of the first sheet, the second
sheet lying in one of the `5 ^ m` neighbouring bins; apply `group_matching` to each group, and
sum the geometric series over the scales.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set Filter
open scoped ENNReal

noncomputable section

/-- Equal floors are within one bin width. -/
theorem abs_sub_lt_of_floor_eq {u v δ : ℝ} (hδ : 0 < δ) (h : ⌊u / δ⌋ = ⌊v / δ⌋) :
    |u - v| < δ := by
  have hu := Int.floor_le (u / δ)
  have hu' := Int.lt_floor_add_one (u / δ)
  have hv := Int.floor_le (v / δ)
  have hv' := Int.lt_floor_add_one (v / δ)
  rw [h] at hu hu'
  have : |u / δ - v / δ| < 1 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at this
  exact this

/-- Values within two bin widths have floors within two bins. -/
theorem abs_floor_sub_le_two {u v δ : ℝ} (hδ : 0 < δ) (h : |u - v| < 2 * δ) :
    |⌊u / δ⌋ - ⌊v / δ⌋| ≤ 2 := by
  have hu := Int.floor_le (u / δ)
  have hu' := Int.lt_floor_add_one (u / δ)
  have hv := Int.floor_le (v / δ)
  have hv' := Int.lt_floor_add_one (v / δ)
  have hd : |u / δ - v / δ| < 2 := by
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_iff₀ hδ]
    linarith
  rw [abs_lt] at hd
  have h1 : ((⌊u / δ⌋ - ⌊v / δ⌋ : ℤ) : ℝ) < 3 := by push_cast; linarith
  have h2 : (-3 : ℝ) < ((⌊u / δ⌋ - ⌊v / δ⌋ : ℤ) : ℝ) := by push_cast; linarith
  have h1' : ⌊u / δ⌋ - ⌊v / δ⌋ < 3 := by exact_mod_cast h1
  have h2' : -3 < ⌊u / δ⌋ - ⌊v / δ⌋ := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> omega

/-- Floors within two bins come from values within three bin widths. -/
theorem abs_sub_lt_of_abs_floor_sub_le_two {u v δ : ℝ} (hδ : 0 < δ)
    (h : |⌊u / δ⌋ - ⌊v / δ⌋| ≤ 2) : |u - v| < 3 * δ := by
  have hu := Int.floor_le (u / δ)
  have hu' := Int.lt_floor_add_one (u / δ)
  have hv := Int.floor_le (v / δ)
  have hv' := Int.lt_floor_add_one (v / δ)
  rw [abs_le] at h
  have h1 : ((⌊u / δ⌋ - ⌊v / δ⌋ : ℤ) : ℝ) ≤ 2 := by exact_mod_cast h.2
  have h2 : (-2 : ℝ) ≤ ((⌊u / δ⌋ - ⌊v / δ⌋ : ℤ) : ℝ) := by exact_mod_cast h.1
  push_cast at h1 h2
  have : |u / δ - v / δ| < 3 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_iff₀ hδ] at this
  linarith

/-- A point of `ℤ ^ m` has at most `5 ^ m` points within sup-distance two. -/
theorem card_filter_near_le {m : ℕ} (S : Finset (Fin m → ℤ)) (c : Fin m → ℤ) :
    (S.filter fun b => ∀ l, |c l - b l| ≤ 2).card ≤ 5 ^ m := by
  classical
  calc (S.filter fun b => ∀ l, |c l - b l| ≤ 2).card
      ≤ (Fintype.piFinset fun l => Finset.Icc (c l - 2) (c l + 2)).card := by
        apply Finset.card_le_card
        intro b hb
        rw [Finset.mem_filter] at hb
        rw [Fintype.mem_piFinset]
        intro l
        have := hb.2 l
        rw [abs_le] at this
        rw [Finset.mem_Icc]
        constructor <;> linarith
    _ = 5 ^ m := by
        rw [Fintype.card_piFinset]
        simp only [Int.card_Icc]
        have : ∀ l : Fin m, (c l + 2 + 1 - (c l - 2)).toNat = 5 := by
          intro l
          have : c l + 2 + 1 - (c l - 2) = 5 := by ring
          rw [this]; rfl
        simp [this]

/-- Every value at least `δ₀ > 0` lies in a dyadic scale `[2 ^ k δ₀, 2 ^ (k+1) δ₀)`. -/
theorem exists_dyadic_scale {s δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hs : δ₀ ≤ s) :
    ∃ k : ℕ, 2 ^ k * δ₀ ≤ s ∧ s < 2 ^ (k + 1) * δ₀ := by
  have h1 : 1 ≤ s / δ₀ := by rw [le_div_iff₀ hδ₀]; linarith
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_, ?_⟩
  · rw [le_div_iff₀ hδ₀] at hk1; exact hk1
  · rw [div_lt_iff₀ hδ₀] at hk2; exact hk2

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **Comparison of two lists of algebraic sheets.** -/
theorem sheet_comparison (hTC : Submission.Lib.K4QuadSheetMatching.TwoColorStatement)
    (D : ℕ) (hD : 1 ≤ D) (d₀ : ℝ) (hd0 : 0 ≤ d₀) (hd1 : d₀ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ (a L CT Λ : ℝ), 0 < a → 1 ≤ L → 0 < CT →
    C * L ^ (1 / ε) ≤ Λ →
    ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
      (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) (T₁ : Fin n₁ → ℝ) (T₂ : Fin n₂ → ℝ)
      (μ : Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))),
    IsFiniteMeasure μ →
    (∀ i, IsSheet D (f₁ i)) → (∀ j, IsSheet D (f₂ j)) →
    (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
    (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
      μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (CT * T₁ i) * volume U) →
    (∀ (j : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
      μ {p | p.1.2 = j ∧ p.2 ∈ U} ≤ ENNReal.ofReal (CT * T₂ j) * volume U) →
    (∀ᵐ p ∂μ, ‖p.2‖ ≤ 1 / 4 ∧ ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ a) →
    (∀ (i₀ : Fin n₁) (M : ℝ), a ≤ M →
      ((Finset.univ.filter fun i : Fin n₁ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
          ‖f₁ i (emb x) - f₁ i₀ (emb x)‖ ≤ M).card : ℝ) ≤ L * (M / a) ^ d₀ ∧
      ((Finset.univ.filter fun j : Fin n₂ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
          ‖f₂ j (emb x) - f₁ i₀ (emb x)‖ ≤ M).card : ℝ) ≤ L * (M / a) ^ d₀) →
    μ {p | ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 ∧
        Λ * a ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖} ≤
      ENNReal.ofReal (C * CT * Λ ^ (-ε) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
  obtain ⟨m, J, c₁, c₂, hc₁, hc₂, hup, hlow⟩ := exists_sheet_jets D hD
  obtain ⟨ε₀, hε₀, R₀, hR₀, HG⟩ := group_matching hTC D hD d₀ hd0 hd1
  set K₁ : ℝ := 6 * c₁ * c₂ * ((m : ℝ) + 1) ^ 2 with hK₁
  have hK₁pos : 0 < K₁ := by positivity
  set r : ℝ := (2 : ℝ) ^ (-ε₀) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set Cthr : ℝ := max R₀ (max (K₁ ^ (1 / (2 * ε₀))) 1) with hCthr
  set Cfin : ℝ := (5 : ℝ) ^ m / (1 - r) with hCfin
  have hCthr1 : 1 ≤ Cthr := le_max_of_le_right (le_max_right _ _)
  refine ⟨ε₀, hε₀, max Cthr Cfin, le_max_of_le_left hCthr1, ?_⟩
  intro a L CT Λ ha hL hCT hΛ n₁ n₂ f₁ f₂ T₁ T₂ μ hfin hs₁ hs₂ hT₁ hT₂ hmar₁ hmar₂ hae hlist
  -- consequences of the size of `Λ`
  have hLe : 1 ≤ L ^ (1 / ε₀) := Real.one_le_rpow hL (by positivity)
  have hΛthr : Cthr ≤ Λ := by
    calc Cthr = Cthr * 1 := (mul_one _).symm
      _ ≤ max Cthr Cfin * L ^ (1 / ε₀) :=
          mul_le_mul (le_max_left _ _) hLe zero_le_one (by positivity)
      _ ≤ Λ := hΛ
  have hΛ1 : 1 ≤ Λ := hCthr1.trans hΛthr
  have hΛpos : 0 < Λ := by linarith
  have hΛR₀ : R₀ ≤ Λ := (le_max_left _ _).trans hΛthr
  have hΛK : K₁ ^ (1 / (2 * ε₀)) ≤ Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans hΛthr
  have hΛL : L ^ (1 / ε₀) ≤ Λ := by
    calc L ^ (1 / ε₀) = 1 * L ^ (1 / ε₀) := (one_mul _).symm
      _ ≤ max Cthr Cfin * L ^ (1 / ε₀) :=
          mul_le_mul_of_nonneg_right (hCthr1.trans (le_max_left _ _)) (by positivity)
      _ ≤ Λ := hΛ
  -- sizes of a scale `R ≥ Λ`
  have hRsize : ∀ R : ℝ, Λ ≤ R → R₀ ≤ R ∧ L ≤ R ^ ε₀ ∧ K₁ ≤ R ^ (2 * ε₀) := by
    intro R hR
    have hRpos : 0 < R := by linarith
    refine ⟨hΛR₀.trans hR, ?_, ?_⟩
    · have h1 : L ^ (1 / ε₀) ≤ R := hΛL.trans hR
      calc L = (L ^ (1 / ε₀)) ^ ε₀ := by
            rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hε₀.ne', Real.rpow_one]
        _ ≤ R ^ ε₀ := Real.rpow_le_rpow (by positivity) h1 hε₀.le
    · have h1 : K₁ ^ (1 / (2 * ε₀)) ≤ R := hΛK.trans hR
      calc K₁ = (K₁ ^ (1 / (2 * ε₀))) ^ (2 * ε₀) := by
            rw [← Real.rpow_mul hK₁pos.le, one_div_mul_cancel (by positivity), Real.rpow_one]
        _ ≤ R ^ (2 * ε₀) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  -- jet discrepancies and dyadic scales
  classical
  set Wt : ℝ := ∑ i, T₁ i + ∑ j, T₂ j with hWt
  have hWtnn : 0 ≤ Wt := add_nonneg (Finset.sum_nonneg fun i _ => hT₁ i)
    (Finset.sum_nonneg fun j _ => hT₂ j)
  let sJ : Fin n₁ × Fin n₂ → ℝ := fun ij => ∑ l, |J (f₁ ij.1) l - J (f₂ ij.2) l|
  set δ₀ : ℝ := Λ * a / c₁ with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  let badK : ℕ → Set ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3)) := fun k =>
    {p | 2 ^ k * δ₀ ≤ sJ p.1 ∧ sJ p.1 < 2 ^ (k + 1) * δ₀}
  -- the bad pairs lie in the dyadic scales
  have hcover : {p : (Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3) |
      ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 ∧
        Λ * a ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖} ⊆ ⋃ k, badK k := by
    rintro p ⟨x, hx, hxbad⟩
    have hsJ : δ₀ ≤ sJ p.1 := by
      have := hup (f₁ p.1.1) (f₂ p.1.2) (hs₁ _) (hs₂ _) x (by linarith)
      rw [hδ₀, div_le_iff₀ hc₁]
      calc Λ * a ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖ := hxbad
        _ ≤ c₁ * sJ p.1 := this
        _ = sJ p.1 * c₁ := mul_comm _ _
    obtain ⟨k, hk1, hk2⟩ := exists_dyadic_scale hδ₀pos hsJ
    exact Set.mem_iUnion.mpr ⟨k, hk1, hk2⟩
  -- the bound at one scale
  have hscale : ∀ k : ℕ, μ (badK k) ≤
      ENNReal.ofReal (CT * (3 * ((m : ℝ) + 1) * 2 ^ k * Λ) ^ (-ε₀) * (5 ^ m * Wt)) := by
    intro k
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    set δk : ℝ := 2 ^ k * δ₀ with hδkdef
    have hδk : 0 < δk := by positivity
    set Rk : ℝ := 3 * ((m : ℝ) + 1) * 2 ^ k * Λ with hRkdef
    have hRkΛ : Λ ≤ Rk := by
      have h1 : (1 : ℝ) ≤ 3 * ((m : ℝ) + 1) * 2 ^ k := by
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      nlinarith
    have hRkpos : 0 < Rk := by linarith
    have hRkeq : 3 * c₁ * ((m : ℝ) + 1) * δk / a = Rk := by
      rw [hRkdef, hδkdef, hδ₀]
      field_simp
    obtain ⟨hRkR₀, hRkL, hRkK⟩ := hRsize Rk hRkΛ
    set Mk : ℝ := 3 * c₁ * ((m : ℝ) + 1) * δk * Rk ^ (-ε₀) with hMkdef
    have hMkpos : 0 < Mk := by positivity
    have hRRneg : Rk ^ (-ε₀) * Rk ^ ε₀ = 1 := by
      rw [← Real.rpow_add hRkpos]; simp
    have hMkR : Mk * Rk ^ ε₀ = 3 * c₁ * ((m : ℝ) + 1) * δk := by
      rw [hMkdef, mul_assoc, hRRneg, mul_one]
    have hMkval : Mk * Rk ^ (-1 + ε₀) = a := by
      have h1 : Rk ^ (-ε₀) * Rk ^ (-1 + ε₀) = Rk⁻¹ := by
        rw [← Real.rpow_add hRkpos, show -ε₀ + (-1 + ε₀) = -1 by ring, Real.rpow_neg_one]
      rw [hMkdef, mul_assoc, h1, ← div_eq_mul_inv, ← hRkeq]
      field_simp
    have hMkdisc : (m : ℝ) * (c₂ * (Mk * Rk ^ (-ε₀))) < δk := by
      have h1 : Rk ^ (-ε₀) * Rk ^ (-ε₀) = (Rk ^ (2 * ε₀))⁻¹ := by
        rw [← Real.rpow_add hRkpos, ← Real.rpow_neg hRkpos.le]; ring_nf
      have h2 : (m : ℝ) * (c₂ * (Mk * Rk ^ (-ε₀))) =
          3 * c₁ * c₂ * (m : ℝ) * ((m : ℝ) + 1) * δk * (Rk ^ (2 * ε₀))⁻¹ := by
        rw [hMkdef, ← h1]; ring
      rw [h2]
      have hK : 3 * c₁ * c₂ * (m : ℝ) * ((m : ℝ) + 1) < Rk ^ (2 * ε₀) := by
        have e : K₁ - 3 * c₁ * c₂ * (m : ℝ) * ((m : ℝ) + 1) =
            3 * (c₁ * c₂) * ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
          rw [hK₁]; ring
        have hpos : 0 < 3 * (c₁ * c₂) * ((m : ℝ) + 1) * ((m : ℝ) + 2) := by positivity
        linarith
      have hRpow : 0 < Rk ^ (2 * ε₀) := by positivity
      rw [← div_eq_mul_inv, div_lt_iff₀ hRpow]
      calc 3 * c₁ * c₂ * (m : ℝ) * ((m : ℝ) + 1) * δk
          = (3 * c₁ * c₂ * (m : ℝ) * ((m : ℝ) + 1)) * δk := by ring
        _ < Rk ^ (2 * ε₀) * δk := mul_lt_mul_of_pos_right hK hδk
        _ = δk * Rk ^ (2 * ε₀) := mul_comm _ _
    -- jet bins at this scale
    let bin : (EuclideanSpace ℂ (Fin 3) → ℂ) → Fin m → ℤ := fun f l => ⌊J f l / δk⌋
    let Bk : Finset (Fin m → ℤ) := Finset.univ.image fun i => bin (f₁ i)
    let G₁ : (Fin m → ℤ) → Finset (Fin n₁) := fun b => Finset.univ.filter fun i => bin (f₁ i) = b
    let G₂ : (Fin m → ℤ) → Finset (Fin n₂) := fun b =>
      Finset.univ.filter fun j => ∀ l, |bin (f₂ j) l - b l| ≤ 2
    let S : (Fin m → ℤ) → Set ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3)) := fun b =>
      {p | bin (f₁ p.1.1) = b ∧ p ∈ badK k}
    have hSmeas : ∀ b, MeasurableSet (S b) := fun b =>
      (MeasurableSet.of_discrete (s := {ij : Fin n₁ × Fin n₂ | bin (f₁ ij.1) = b ∧
        2 ^ k * δ₀ ≤ sJ ij ∧ sJ ij < 2 ^ (k + 1) * δ₀})).preimage measurable_fst
    have hcov : badK k ⊆ ⋃ b ∈ Bk, S b := fun p hp =>
      Set.mem_biUnion (Finset.mem_image_of_mem _ (Finset.mem_univ p.1.1)) ⟨rfl, hp⟩
    have hsumle : ∀ (u : Fin m → ℝ) (c : ℝ), (∀ l, u l ≤ c) → ∑ l, u l ≤ (m : ℝ) * c := by
      intro u c hu
      calc ∑ l, u l ≤ ∑ _l : Fin m, c := Finset.sum_le_sum fun l _ => hu l
        _ = (m : ℝ) * c := by simp
    -- one group
    have hgroup : ∀ b ∈ Bk, μ (S b) ≤
        ENNReal.ofReal (CT * Rk ^ (-ε₀) * (∑ i ∈ G₁ b, T₁ i + ∑ j ∈ G₂ b, T₂ j)) := by
      intro b hb
      obtain ⟨i_b, -, hib⟩ := Finset.mem_image.mp hb
      have hclose₁' : ∀ i ∈ G₁ b, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
          ‖f₁ i (emb x) - f₁ i_b (emb x)‖ ≤ c₁ * ((m : ℝ) + 1) * δk := by
        intro i hi x hx
        have hi' : bin (f₁ i) = b := (Finset.mem_filter.mp hi).2
        calc ‖f₁ i (emb x) - f₁ i_b (emb x)‖
            ≤ c₁ * ∑ l, |J (f₁ i) l - J (f₁ i_b) l| := hup _ _ (hs₁ _) (hs₁ _) x hx
          _ ≤ c₁ * ((m : ℝ) * δk) := by
              gcongr
              apply hsumle
              intro l
              apply le_of_lt
              apply abs_sub_lt_of_floor_eq hδk
              have h1 := congrFun hi' l
              have h2 := congrFun hib l
              simp only [bin] at h1 h2
              rw [h1, h2]
          _ ≤ c₁ * ((m : ℝ) + 1) * δk := by nlinarith
      have hclose₂' : ∀ j ∈ G₂ b, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
          ‖f₂ j (emb x) - f₁ i_b (emb x)‖ ≤ 3 * c₁ * ((m : ℝ) + 1) * δk := by
        intro j hj x hx
        have hj' := (Finset.mem_filter.mp hj).2
        calc ‖f₂ j (emb x) - f₁ i_b (emb x)‖
            ≤ c₁ * ∑ l, |J (f₂ j) l - J (f₁ i_b) l| := hup _ _ (hs₂ _) (hs₁ _) x hx
          _ ≤ c₁ * ((m : ℝ) * (3 * δk)) := by
              gcongr
              apply hsumle
              intro l
              apply le_of_lt
              apply abs_sub_lt_of_abs_floor_sub_le_two hδk
              have h1 := hj' l
              have h2 := congrFun hib l
              simp only [bin] at h1 h2
              rw [h2]
              exact h1
          _ ≤ 3 * c₁ * ((m : ℝ) + 1) * δk := by nlinarith
      have hδka : a ≤ c₁ * ((m : ℝ) + 1) * δk := by
        have h1 : c₁ * δ₀ = Λ * a := by rw [hδ₀]; field_simp
        have h2 : δ₀ ≤ δk := by
          rw [hδkdef]
          have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
          nlinarith
        have h3 : Λ * a ≤ c₁ * δk := by nlinarith
        have h4 : 0 ≤ c₁ * δk := by positivity
        calc a = 1 * a := (one_mul a).symm
          _ ≤ Λ * a := mul_le_mul_of_nonneg_right hΛ1 ha.le
          _ ≤ c₁ * δk := h3
          _ ≤ ((m : ℝ) + 1) * (c₁ * δk) := le_mul_of_one_le_left h4 (by linarith)
          _ = c₁ * ((m : ℝ) + 1) * δk := by ring
      have hcard₁ : ((G₁ b).card : ℝ) ≤ Rk ^ (d₀ + ε₀) := by
        have hsub : G₁ b ⊆ Finset.univ.filter fun i : Fin n₁ =>
            ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
              ‖f₁ i (emb x) - f₁ i_b (emb x)‖ ≤ c₁ * ((m : ℝ) + 1) * δk := by
          intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclose₁' i hi⟩
        have hl := (hlist i_b _ hδka).1
        have hratio : c₁ * ((m : ℝ) + 1) * δk / a ≤ Rk := by
          rw [← hRkeq]
          gcongr
          linarith
        calc ((G₁ b).card : ℝ) ≤ _ := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ L * (c₁ * ((m : ℝ) + 1) * δk / a) ^ d₀ := hl
          _ ≤ Rk ^ ε₀ * Rk ^ d₀ := by
              gcongr
          _ = Rk ^ (d₀ + ε₀) := by rw [← Real.rpow_add hRkpos, add_comm]
      have hcard₂ : ((G₂ b).card : ℝ) ≤ Rk ^ (d₀ + ε₀) := by
        have hsub : G₂ b ⊆ Finset.univ.filter fun j : Fin n₂ =>
            ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
              ‖f₂ j (emb x) - f₁ i_b (emb x)‖ ≤ 3 * c₁ * ((m : ℝ) + 1) * δk := by
          intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclose₂' j hj⟩
        have hl := (hlist i_b (3 * c₁ * ((m : ℝ) + 1) * δk)
          (by linarith [hδka, (by positivity : 0 ≤ c₁ * ((m : ℝ) + 1) * δk)])).2
        calc ((G₂ b).card : ℝ) ≤ _ := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ L * (3 * c₁ * ((m : ℝ) + 1) * δk / a) ^ d₀ := hl
          _ = L * Rk ^ d₀ := by rw [hRkeq]
          _ ≤ Rk ^ ε₀ * Rk ^ d₀ := by gcongr
          _ = Rk ^ (d₀ + ε₀) := by rw [← Real.rpow_add hRkpos, add_comm]
      have hmar₁' : ∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
          (μ.restrict (S b)) {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (CT * T₁ i) * volume U :=
        fun i U hU => (Measure.restrict_apply_le _ _).trans (hmar₁ i U hU)
      have hmar₂' : ∀ (j : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
          (μ.restrict (S b)) {p | p.1.2 = j ∧ p.2 ∈ U} ≤ ENNReal.ofReal (CT * T₂ j) * volume U :=
        fun j U hU => (Measure.restrict_apply_le _ _).trans (hmar₂ j U hU)
      have hae' : ∀ᵐ p ∂(μ.restrict (S b)), p.1.1 ∈ G₁ b ∧ p.1.2 ∈ G₂ b ∧ ‖p.2‖ ≤ 1 / 4 ∧
          ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ Mk * Rk ^ (-1 + ε₀) ∧
          ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 ∧
            Mk * Rk ^ (-ε₀) ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖ := by
        rw [ae_restrict_iff' (hSmeas b)]
        filter_upwards [hae] with p hp hpS
        obtain ⟨hpb, hk1, hk2⟩ := hpS
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l => ?_⟩, hp.1, ?_, ?_⟩
        · rw [← hpb]
          apply abs_floor_sub_le_two hδk
          have hsingle := Finset.single_le_sum
            (f := fun l => |J (f₁ p.1.1) l - J (f₂ p.1.2) l|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ l)
          rw [abs_sub_comm]
          have : sJ p.1 < 2 * δk := by rw [hδkdef, ← mul_assoc, ← pow_succ']; exact hk2
          exact lt_of_le_of_lt hsingle this
        · rw [hMkval]; exact hp.2
        · by_contra hcon
          push_neg at hcon
          have hA' : 0 < Mk * Rk ^ (-ε₀) := by positivity
          have hJ := hlow (f₁ p.1.1) (f₂ p.1.2) (hs₁ _) (hs₂ _) (Mk * Rk ^ (-ε₀)) hA'
            (fun x hx => (hcon x hx).le)
          have hsum : sJ p.1 ≤ (m : ℝ) * (c₂ * (Mk * Rk ^ (-ε₀))) := hsumle _ _ hJ
          linarith
      rw [← Measure.restrict_apply_univ]
      exact HG Rk Mk CT hRkR₀ hMkpos hCT n₁ n₂ f₁ f₂ (fun x => f₁ i_b (emb x)) T₁ T₂ (G₁ b) (G₂ b)
        (μ.restrict (S b)) inferInstance hcard₁ hcard₂ (fun i _ => hs₁ i) (fun j _ => hs₂ j)
        (fun i hi x hx => (hclose₁' i hi x hx).trans (by rw [hMkR]; nlinarith))
        (fun j hj x hx => (hclose₂' j hj x hx).trans (by rw [hMkR]))
        hT₁ hT₂ hmar₁' hmar₂' hae'
    -- the reference totals of the groups
    have hsumW : ∑ b ∈ Bk, (∑ i ∈ G₁ b, T₁ i + ∑ j ∈ G₂ b, T₂ j) ≤ 5 ^ m * Wt := by
      rw [Finset.sum_add_distrib]
      have h1 : ∑ b ∈ Bk, ∑ i ∈ G₁ b, T₁ i = ∑ i, T₁ i :=
        Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))
          T₁
      have h2 : ∑ b ∈ Bk, ∑ j ∈ G₂ b, T₂ j =
          ∑ j, ∑ _b ∈ Bk.filter (fun b => ∀ l, |bin (f₂ j) l - b l| ≤ 2), T₂ j := by
        apply Finset.sum_comm'
        intro b j
        simp only [G₂, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      have h3 : ∑ j, ∑ _b ∈ Bk.filter (fun b => ∀ l, |bin (f₂ j) l - b l| ≤ 2), T₂ j ≤
          ∑ j, (5 : ℝ) ^ m * T₂ j := by
        apply Finset.sum_le_sum
        intro j _
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        · exact hT₂ j
        · exact_mod_cast card_filter_near_le Bk (bin (f₂ j))
      have h4 : ∑ i, T₁ i ≤ (5 : ℝ) ^ m * ∑ i, T₁ i := by
        have : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
        have h0 : 0 ≤ ∑ i, T₁ i := Finset.sum_nonneg fun i _ => hT₁ i
        nlinarith
      have h5 : ∑ j, (5 : ℝ) ^ m * T₂ j = 5 ^ m * ∑ j, T₂ j := (Finset.mul_sum _ _ _).symm
      rw [h1, h2, hWt, mul_add]
      linarith
    calc μ (badK k) ≤ μ (⋃ b ∈ Bk, S b) := measure_mono hcov
      _ ≤ ∑ b ∈ Bk, μ (S b) := measure_biUnion_finset_le _ _
      _ ≤ ∑ b ∈ Bk, ENNReal.ofReal (CT * Rk ^ (-ε₀) * (∑ i ∈ G₁ b, T₁ i + ∑ j ∈ G₂ b, T₂ j)) :=
          Finset.sum_le_sum hgroup
      _ = ENNReal.ofReal (CT * Rk ^ (-ε₀) *
            ∑ b ∈ Bk, (∑ i ∈ G₁ b, T₁ i + ∑ j ∈ G₂ b, T₂ j)) := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          intro b _
          exact mul_nonneg (by positivity) (add_nonneg (Finset.sum_nonneg fun i _ => hT₁ i)
            (Finset.sum_nonneg fun j _ => hT₂ j))
      _ ≤ ENNReal.ofReal (CT * Rk ^ (-ε₀) * (5 ^ m * Wt)) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left hsumW (by positivity)
  -- sum over the scales
  set A₀ : ℝ := CT * Λ ^ (-ε₀) * (5 ^ m * Wt) with hA₀
  have hA₀nn : 0 ≤ A₀ := mul_nonneg (mul_nonneg hCT.le (Real.rpow_nonneg hΛpos.le _))
    (mul_nonneg (by positivity) hWtnn)
  have hterm : ∀ k : ℕ, ENNReal.ofReal
      (CT * (3 * ((m : ℝ) + 1) * 2 ^ k * Λ) ^ (-ε₀) * (5 ^ m * Wt)) ≤
        ENNReal.ofReal A₀ * ENNReal.ofReal r ^ k := by
    intro k
    rw [← ENNReal.ofReal_pow hr0.le, ← ENNReal.ofReal_mul hA₀nn]
    apply ENNReal.ofReal_le_ofReal
    have h2k : (0 : ℝ) < 2 ^ k * Λ := by positivity
    have hle : 2 ^ k * Λ ≤ 3 * ((m : ℝ) + 1) * 2 ^ k * Λ := by
      have : (1 : ℝ) ≤ 3 * ((m : ℝ) + 1) := by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      nlinarith
    have hpow : (3 * ((m : ℝ) + 1) * 2 ^ k * Λ) ^ (-ε₀) ≤ r ^ k * Λ ^ (-ε₀) := by
      calc (3 * ((m : ℝ) + 1) * 2 ^ k * Λ) ^ (-ε₀) ≤ (2 ^ k * Λ) ^ (-ε₀) :=
            Real.rpow_le_rpow_of_nonpos h2k hle (by linarith)
        _ = ((2 : ℝ) ^ k) ^ (-ε₀) * Λ ^ (-ε₀) := Real.mul_rpow (by positivity) hΛpos.le
        _ = r ^ k * Λ ^ (-ε₀) := by
            have h2 : ((2 : ℝ) ^ k) ^ (-ε₀) = r ^ k := by
              rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
                Real.rpow_mul (by norm_num), Real.rpow_natCast]
            rw [h2]
    calc CT * (3 * ((m : ℝ) + 1) * 2 ^ k * Λ) ^ (-ε₀) * (5 ^ m * Wt)
        ≤ CT * (r ^ k * Λ ^ (-ε₀)) * (5 ^ m * Wt) := by gcongr
      _ = A₀ * r ^ k := by rw [hA₀]; ring
  have hgeom : ∑' k : ℕ, ENNReal.ofReal A₀ * ENNReal.ofReal r ^ k =
      ENNReal.ofReal (A₀ / (1 - r)) := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ hr0.le, ← ENNReal.ofReal_inv_of_pos (by linarith),
      ← ENNReal.ofReal_mul hA₀nn, div_eq_mul_inv]
  calc μ {p : (Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3) |
        ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 ∧
          Λ * a ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖}
      ≤ μ (⋃ k, badK k) := measure_mono hcover
    _ ≤ ∑' k, μ (badK k) := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal A₀ * ENNReal.ofReal r ^ k :=
        ENNReal.tsum_le_tsum fun k => (hscale k).trans (hterm k)
    _ = ENNReal.ofReal (A₀ / (1 - r)) := hgeom
    _ ≤ ENNReal.ofReal (max Cthr Cfin * CT * Λ ^ (-ε₀) * Wt) := by
        apply ENNReal.ofReal_le_ofReal
        have h1r : 0 < 1 - r := by linarith
        calc A₀ / (1 - r) = Cfin * CT * Λ ^ (-ε₀) * Wt := by
              rw [hA₀, hCfin]; field_simp
          _ ≤ max Cthr Cfin * CT * Λ ^ (-ε₀) * Wt := by
              gcongr
              exact le_max_right _ _

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set Filter

noncomputable section

/-- Agreement of two sheets on the real ball of radius `1/4` propagates to the ball of radius
`1/2`, with a constant depending only on the degree (accepted o149 through `exists_sheet_jets`). -/
theorem exists_agreement_transfer (D : ℕ) (hD : 1 ≤ D) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ f g, IsSheet D f → IsSheet D g → ∀ A : ℝ, 0 < A →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 → ‖f (emb x) - g (emb x)‖ ≤ A) →
      ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 → ‖f (emb y) - g (emb y)‖ ≤ C₀ * A := by
  obtain ⟨m, J, c₁, c₂, hc₁, hc₂, hup, hlow⟩ := exists_sheet_jets D hD
  refine ⟨max 1 (c₁ * m * c₂), le_max_left _ _, ?_⟩
  intro f g hf hg A hA hfg y hy
  have hJ := hlow f g hf hg A hA hfg
  calc ‖f (emb y) - g (emb y)‖ ≤ c₁ * ∑ i, |J f i - J g i| := hup f g hf hg y hy
    _ ≤ c₁ * ∑ _i : Fin m, c₂ * A := by
        gcongr with i
        exact hJ i
    _ = c₁ * m * c₂ * A := by simp; ring
    _ ≤ max 1 (c₁ * m * c₂) * A := by gcongr; exact le_max_right _ _

open scoped Classical in
/-- **List bounds from agreement.** Under the list-size hypothesis of `sheet_comparison`, a
first-list sheet has at most `L * (C₀ Λ) ^ d₀` second-list sheets agreeing with it to `Λ a`
on the ball of radius `1/4`, and a second-list sheet has at most `L * (2 C₀ Λ) ^ d₀` such
first-list partners. -/
theorem exists_pair_list_bounds (D : ℕ) (hD : 1 ≤ D) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (a L Λ d₀ : ℝ), 0 < a → 1 ≤ L → 1 ≤ Λ → 0 ≤ d₀ →
    ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
      (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ),
    (∀ i, IsSheet D (f₁ i)) → (∀ j, IsSheet D (f₂ j)) →
    (∀ (i₀ : Fin n₁) (M : ℝ), a ≤ M →
      ((Finset.univ.filter fun i : Fin n₁ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
          ‖f₁ i (emb x) - f₁ i₀ (emb x)‖ ≤ M).card : ℝ) ≤ L * (M / a) ^ d₀ ∧
      ((Finset.univ.filter fun j : Fin n₂ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
          ‖f₂ j (emb x) - f₁ i₀ (emb x)‖ ≤ M).card : ℝ) ≤ L * (M / a) ^ d₀) →
    (∀ i₀ : Fin n₁,
      ((Finset.univ.filter fun j : Fin n₂ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
          ‖f₁ i₀ (emb x) - f₂ j (emb x)‖ ≤ Λ * a).card : ℝ) ≤ L * (C₀ * Λ) ^ d₀) ∧
    (∀ j₀ : Fin n₂,
      ((Finset.univ.filter fun i : Fin n₁ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
          ‖f₁ i (emb x) - f₂ j₀ (emb x)‖ ≤ Λ * a).card : ℝ) ≤ L * (2 * C₀ * Λ) ^ d₀) := by
  obtain ⟨C₀, hC₀, htr⟩ := exists_agreement_transfer D hD
  refine ⟨C₀, hC₀, ?_⟩
  intro a L Λ d₀ ha hL hΛ hd₀ n₁ n₂ f₁ f₂ hs₁ hs₂ hlist
  have hΛa : 0 < Λ * a := by positivity
  constructor
  · intro i₀
    have hsub : (Finset.univ.filter fun j : Fin n₂ => ∀ x : EuclideanSpace ℝ (Fin 3),
        ‖x‖ ≤ 1 / 4 → ‖f₁ i₀ (emb x) - f₂ j (emb x)‖ ≤ Λ * a) ⊆
        Finset.univ.filter fun j : Fin n₂ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
          ‖f₂ j (emb x) - f₁ i₀ (emb x)‖ ≤ C₀ * (Λ * a) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, fun y hy => ?_⟩
      rw [norm_sub_rev]
      exact htr _ _ (hs₁ i₀) (hs₂ j) _ hΛa hj.2 y hy
    have hM : a ≤ C₀ * (Λ * a) := by nlinarith
    calc _ ≤ ((Finset.univ.filter fun j : Fin n₂ => ∀ x : EuclideanSpace ℝ (Fin 3),
          ‖x‖ ≤ 1 / 2 → ‖f₂ j (emb x) - f₁ i₀ (emb x)‖ ≤ C₀ * (Λ * a)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ L * (C₀ * (Λ * a) / a) ^ d₀ := (hlist i₀ _ hM).2
      _ = L * (C₀ * Λ) ^ d₀ := by congr 2; field_simp
  · intro j₀
    by_cases hne : (Finset.univ.filter fun i : Fin n₁ => ∀ x : EuclideanSpace ℝ (Fin 3),
        ‖x‖ ≤ 1 / 4 → ‖f₁ i (emb x) - f₂ j₀ (emb x)‖ ≤ Λ * a).Nonempty
    · obtain ⟨i₁, hi₁⟩ := hne
      rw [Finset.mem_filter] at hi₁
      have hsub : (Finset.univ.filter fun i : Fin n₁ => ∀ x : EuclideanSpace ℝ (Fin 3),
          ‖x‖ ≤ 1 / 4 → ‖f₁ i (emb x) - f₂ j₀ (emb x)‖ ≤ Λ * a) ⊆
          Finset.univ.filter fun i : Fin n₁ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
            ‖f₁ i (emb x) - f₁ i₁ (emb x)‖ ≤ 2 * C₀ * (Λ * a) := by
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        refine ⟨Finset.mem_univ _, fun y hy => ?_⟩
        have h1 := htr _ _ (hs₁ i) (hs₂ j₀) _ hΛa hi.2 y hy
        have h2 := htr _ _ (hs₁ i₁) (hs₂ j₀) _ hΛa hi₁.2 y hy
        calc ‖f₁ i (emb y) - f₁ i₁ (emb y)‖
            = ‖(f₁ i (emb y) - f₂ j₀ (emb y)) - (f₁ i₁ (emb y) - f₂ j₀ (emb y))‖ := by
              congr 1; ring
          _ ≤ ‖f₁ i (emb y) - f₂ j₀ (emb y)‖ + ‖f₁ i₁ (emb y) - f₂ j₀ (emb y)‖ := norm_sub_le _ _
          _ ≤ C₀ * (Λ * a) + C₀ * (Λ * a) := add_le_add h1 h2
          _ = 2 * C₀ * (Λ * a) := by ring
      have hM : a ≤ 2 * C₀ * (Λ * a) := by nlinarith
      calc _ ≤ ((Finset.univ.filter fun i : Fin n₁ => ∀ x : EuclideanSpace ℝ (Fin 3),
            ‖x‖ ≤ 1 / 2 → ‖f₁ i (emb x) - f₁ i₁ (emb x)‖ ≤ 2 * C₀ * (Λ * a)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ L * (2 * C₀ * (Λ * a) / a) ^ d₀ := (hlist i₁ _ hM).1
        _ = L * (2 * C₀ * Λ) ^ d₀ := by congr 2; field_simp
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.card_empty, Nat.cast_zero]
      have hL0 : 0 ≤ L := by linarith
      positivity

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
