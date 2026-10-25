import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphWorld

/-!
# Coarse row lists of the velocity graph

Palette-weighted pair counting: in a coarse cell, every row bin of the fine-cell graph owns a
witness fine cell whose occupied velocity bins carry palette mass at least `1 / H'`; two bins far
apart pin the row (slope and intercept) through the coefficient lists of the mid cells, so each
separated pair is occupied in few witness cells, and the row bins are few.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-- **Weighted pair counting.** If every element `v` of a finite family owns a set `P v` of pairs
of total `w ⊗ w`-weight at least `κ`, every pair is owned by at most `Λ` elements, and the weights
of the occurring first and second coordinates sum to at most one, then the family has at most
`Λ / κ` elements. -/
lemma card_mul_le_of_pairs {α : Type*} [DecidableEq α] (V : Finset α) (P : α → Finset (ℤ × ℤ))
    (w : ℤ → ℝ) (hw : ∀ c, 0 ≤ w c) {κ Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hlow : ∀ v ∈ V, κ ≤ ∑ x ∈ P v, w x.1 * w x.2)
    (hup : ∀ x, ((V.filter fun v => x ∈ P v).card : ℝ) ≤ Λ)
    (htot : ∀ S : Finset ℤ, ∑ c ∈ S, w c ≤ 1) :
    (V.card : ℝ) * κ ≤ Λ := by
  classical
  set U : Finset (ℤ × ℤ) := V.biUnion P with hU
  have hsum : (V.card : ℝ) * κ ≤ ∑ v ∈ V, ∑ x ∈ P v, w x.1 * w x.2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hlow
  have hswap : ∑ v ∈ V, ∑ x ∈ P v, w x.1 * w x.2 =
      ∑ x ∈ U, ((V.filter fun v => x ∈ P v).card : ℝ) * (w x.1 * w x.2) := by
    rw [Finset.sum_comm' (t' := U) (s' := fun x => V.filter fun v => x ∈ P v)]
    · apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_const, nsmul_eq_mul]
    · intro v x
      simp only [hU, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨hv, hx⟩; exact ⟨⟨hv, hx⟩, v, hv, hx⟩
      · rintro ⟨⟨hv, hx⟩, _⟩; exact ⟨hv, hx⟩
  have hprod : ∑ x ∈ U, w x.1 * w x.2 ≤ 1 := by
    calc ∑ x ∈ U, w x.1 * w x.2 ≤ ∑ x ∈ U.image Prod.fst ×ˢ U.image Prod.snd, w x.1 * w x.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
          · intro x _ _; exact mul_nonneg (hw _) (hw _)
      _ = (∑ c ∈ U.image Prod.fst, w c) * (∑ c ∈ U.image Prod.snd, w c) := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
      _ ≤ 1 * 1 := by
          apply mul_le_mul (htot _) (htot _) (Finset.sum_nonneg fun c _ => hw c) zero_le_one
      _ = 1 := one_mul 1
  calc (V.card : ℝ) * κ ≤ ∑ x ∈ U, ((V.filter fun v => x ∈ P v).card : ℝ) * (w x.1 * w x.2) := by
        rw [← hswap]; exact hsum
    _ ≤ ∑ x ∈ U, Λ * (w x.1 * w x.2) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_right (hup x) (mul_nonneg (hw _) (hw _))
    _ = Λ * ∑ x ∈ U, w x.1 * w x.2 := by rw [Finset.mul_sum]
    _ ≤ Λ * 1 := mul_le_mul_of_nonneg_left hprod hΛ
    _ = Λ := mul_one Λ

/-- Two points on a line `X = G₀ + G₁ V` (residual `res`), `δ` apart in `V`, approximated within
`eV`, `eX` by bin points: the slope is pinned to `(2 res + 2 eX + 2 Gb eV) / (δ - 2 eV)`. -/
lemma slope_close {V₁ V₂ X₁ X₂ G₀ G₁ Vh₁ Vh₂ Xh₁ Xh₂ res eV eX δ Gb : ℝ}
    (h₁ : |X₁ - G₀ - G₁ * V₁| ≤ res) (h₂ : |X₂ - G₀ - G₁ * V₂| ≤ res)
    (hsep : δ ≤ |V₁ - V₂|) (hgap : 2 * eV < δ)
    (hV₁ : |V₁ - Vh₁| ≤ eV) (hV₂ : |V₂ - Vh₂| ≤ eV) (hX₁ : |X₁ - Xh₁| ≤ eX)
    (hX₂ : |X₂ - Xh₂| ≤ eX) (hG₁ : |G₁| ≤ Gb) :
    |G₁ - (Xh₁ - Xh₂) / (Vh₁ - Vh₂)| ≤ (2 * res + 2 * eX + 2 * Gb * eV) / (δ - 2 * eV) := by
  have heV : 0 ≤ eV := le_trans (abs_nonneg _) hV₁
  have hden : δ - 2 * eV ≤ |Vh₁ - Vh₂| := by
    have : |V₁ - V₂| ≤ |Vh₁ - Vh₂| + 2 * eV := by
      calc |V₁ - V₂| = |(Vh₁ - Vh₂) + (V₁ - Vh₁) - (V₂ - Vh₂)| := by ring_nf
        _ ≤ |Vh₁ - Vh₂| + |V₁ - Vh₁| + |V₂ - Vh₂| := by
            have := abs_sub (Vh₁ - Vh₂ + (V₁ - Vh₁)) (V₂ - Vh₂)
            have := abs_add_le (Vh₁ - Vh₂) (V₁ - Vh₁)
            linarith
        _ ≤ |Vh₁ - Vh₂| + 2 * eV := by linarith
    linarith
  have hdpos : 0 < δ - 2 * eV := by linarith
  have hDpos : 0 < |Vh₁ - Vh₂| := lt_of_lt_of_le hdpos hden
  have hD : Vh₁ - Vh₂ ≠ 0 := abs_pos.mp hDpos
  have hnum : |G₁ * (Vh₁ - Vh₂) - (Xh₁ - Xh₂)| ≤ 2 * res + 2 * eX + 2 * Gb * eV := by
    have e : G₁ * (Vh₁ - Vh₂) - (Xh₁ - Xh₂) =
        -(X₁ - G₀ - G₁ * V₁) + (X₂ - G₀ - G₁ * V₂) + (X₁ - Xh₁) - (X₂ - Xh₂)
          - G₁ * (V₁ - Vh₁) + G₁ * (V₂ - Vh₂) := by ring
    rw [e]
    have t1 := abs_mul G₁ (V₁ - Vh₁); have t2 := abs_mul G₁ (V₂ - Vh₂)
    have b1 : |G₁ * (V₁ - Vh₁)| ≤ Gb * eV := by
      rw [t1]; exact mul_le_mul hG₁ hV₁ (abs_nonneg _) (le_trans (abs_nonneg _) hG₁)
    have b2 : |G₁ * (V₂ - Vh₂)| ≤ Gb * eV := by
      rw [t2]; exact mul_le_mul hG₁ hV₂ (abs_nonneg _) (le_trans (abs_nonneg _) hG₁)
    calc |-(X₁ - G₀ - G₁ * V₁) + (X₂ - G₀ - G₁ * V₂) + (X₁ - Xh₁) - (X₂ - Xh₂)
          - G₁ * (V₁ - Vh₁) + G₁ * (V₂ - Vh₂)|
        ≤ |X₁ - G₀ - G₁ * V₁| + |X₂ - G₀ - G₁ * V₂| + |X₁ - Xh₁| + |X₂ - Xh₂|
          + |G₁ * (V₁ - Vh₁)| + |G₁ * (V₂ - Vh₂)| := by
          have a1 := abs_add_le (-(X₁ - G₀ - G₁ * V₁) + (X₂ - G₀ - G₁ * V₂) + (X₁ - Xh₁)
            - (X₂ - Xh₂) - G₁ * (V₁ - Vh₁)) (G₁ * (V₂ - Vh₂))
          have a2 := abs_sub (-(X₁ - G₀ - G₁ * V₁) + (X₂ - G₀ - G₁ * V₂) + (X₁ - Xh₁)
            - (X₂ - Xh₂)) (G₁ * (V₁ - Vh₁))
          have a3 := abs_sub (-(X₁ - G₀ - G₁ * V₁) + (X₂ - G₀ - G₁ * V₂) + (X₁ - Xh₁)) (X₂ - Xh₂)
          have a4 := abs_add_le (-(X₁ - G₀ - G₁ * V₁) + (X₂ - G₀ - G₁ * V₂)) (X₁ - Xh₁)
          have a5 := abs_add_le (-(X₁ - G₀ - G₁ * V₁)) (X₂ - G₀ - G₁ * V₂)
          rw [abs_neg] at a5
          linarith
      _ ≤ 2 * res + 2 * eX + 2 * Gb * eV := by linarith
  have : G₁ - (Xh₁ - Xh₂) / (Vh₁ - Vh₂) = (G₁ * (Vh₁ - Vh₂) - (Xh₁ - Xh₂)) / (Vh₁ - Vh₂) := by
    field_simp
  rw [this, abs_div]
  calc |G₁ * (Vh₁ - Vh₂) - (Xh₁ - Xh₂)| / |Vh₁ - Vh₂|
      ≤ (2 * res + 2 * eX + 2 * Gb * eV) / |Vh₁ - Vh₂| := by gcongr
    _ ≤ (2 * res + 2 * eX + 2 * Gb * eV) / (δ - 2 * eV) := by
        apply div_le_div_of_nonneg_left (by
          have := abs_nonneg (G₁ * (Vh₁ - Vh₂) - (Xh₁ - Xh₂)); linarith) hdpos hden

/-- The integers `⌊y / w⌋` for `y` within `e` of a point `yh` lie in an interval of
`⌊2 e / w⌋ + 2` integers. -/
lemma floor_mem_Icc_of_close {y yh e w : ℝ} (hw : 0 < w) (h : |y - yh| ≤ e) :
    ⌊y / w⌋ ∈ Finset.Icc ⌊(yh - e) / w⌋ ⌊(yh + e) / w⌋ := by
  rw [Finset.mem_Icc, abs_le] at *
  constructor
  · apply Int.floor_mono; apply div_le_div_of_nonneg_right _ hw.le; linarith [h.1]
  · apply Int.floor_mono; apply div_le_div_of_nonneg_right _ hw.le; linarith [h.2]

lemma card_Icc_floor_le {yh e w : ℝ} (hw : 0 < w) (he : 0 ≤ e) :
    ((Finset.Icc ⌊(yh - e) / w⌋ ⌊(yh + e) / w⌋).card : ℝ) ≤ 2 * e / w + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le ((yh + e) / w)
  have h2 := Int.lt_floor_add_one ((yh - e) / w)
  have hdiff : ((⌊(yh + e) / w⌋ : ℝ)) + 1 - ⌊(yh - e) / w⌋ ≤ 2 * e / w + 2 := by
    have : (yh + e) / w - (yh - e) / w = 2 * e / w := by field_simp; ring
    linarith
  by_cases hle : ⌊(yh - e) / w⌋ ≤ ⌊(yh + e) / w⌋ + 1
  · have hnn : 0 ≤ ⌊(yh + e) / w⌋ + 1 - ⌊(yh - e) / w⌋ := by omega
    have hcast : (((⌊(yh + e) / w⌋ + 1 - ⌊(yh - e) / w⌋).toNat : ℕ) : ℝ) =
        ((⌊(yh + e) / w⌋ + 1 - ⌊(yh - e) / w⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnn
    rw [hcast]
    push_cast
    linarith
  · have : (⌊(yh + e) / w⌋ + 1 - ⌊(yh - e) / w⌋).toNat = 0 := by omega
    rw [this]; simp; positivity

/-- The predicted hidden velocity of a coefficient bin `b` at time index `j` (both width `w`). -/
def predX (w : ℝ) (j : ℤ) (b : Fin 5 → ℤ) : ℝ := (b 3 : ℝ) * w + 2 * ((j : ℝ) * w) * ((b 4 : ℝ) * w)

/-- The coefficient bins (width `w`) of an incidence. -/
def cbin (w : ℝ) (p : Inc) : Fin 5 → ℤ := fun e => ⌊p.1.2 e / w⌋

lemma abs_sub_predX_le {w H : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) {p : Inc}
    (hH : ∀ e, |p.1.2 e| ≤ H) (ht : p.2 ∈ Set.Icc (0 : ℝ) 1) :
    |(p.1.2 3 + 2 * p.1.2 4 * p.2) - predX w ⌊p.2 / w⌋ (cbin w p)| ≤ (5 + 2 * H) * w := by
  unfold predX cbin
  set j := ⌊p.2 / w⌋
  have hj1 := Int.floor_le (p.2 / w); have hj2 := Int.lt_floor_add_one (p.2 / w)
  rw [le_div_iff₀ hw] at hj1
  rw [div_lt_iff₀ hw] at hj2
  have h3a := Int.floor_le (p.1.2 3 / w); have h3b := Int.lt_floor_add_one (p.1.2 3 / w)
  rw [le_div_iff₀ hw] at h3a
  rw [div_lt_iff₀ hw] at h3b
  have h4a := Int.floor_le (p.1.2 4 / w); have h4b := Int.lt_floor_add_one (p.1.2 4 / w)
  rw [le_div_iff₀ hw] at h4a
  rw [div_lt_iff₀ hw] at h4b
  have hH4 := hH 4
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) hH4
  rw [abs_le] at hH4 ⊢
  have ht0 := ht.1; have ht1 := ht.2
  -- write the error as a sum of three small terms
  set a := (⌊p.1.2 3 / w⌋ : ℝ) * w
  set c4 := (⌊p.1.2 4 / w⌋ : ℝ) * w
  set tj := (j : ℝ) * w
  have e1 : |p.1.2 3 - a| ≤ w := by rw [abs_le]; constructor <;> linarith
  have e2 : |p.1.2 4 - c4| ≤ w := by rw [abs_le]; constructor <;> linarith
  have e3 : |p.2 - tj| ≤ w := by rw [abs_le]; constructor <;> linarith
  have htj : |tj| ≤ 2 := by rw [abs_le]; constructor <;> nlinarith
  have hc4 : |c4| ≤ H + 1 := by
    have := abs_sub_abs_le_abs_sub c4 (p.1.2 4)
    rw [abs_sub_comm] at this
    have : |p.1.2 4| ≤ H := by rw [abs_le]; exact hH4
    linarith
  have key : (p.1.2 3 + 2 * p.1.2 4 * p.2) - (a + 2 * tj * c4) =
      (p.1.2 3 - a) + 2 * p.1.2 4 * (p.2 - tj) + 2 * tj * (p.1.2 4 - c4) := by ring
  have hbound : |(p.1.2 3 + 2 * p.1.2 4 * p.2) - (a + 2 * tj * c4)| ≤ (5 + 2 * H) * w := by
    rw [key]
    have b1 := abs_add_three (p.1.2 3 - a) (2 * p.1.2 4 * (p.2 - tj)) (2 * tj * (p.1.2 4 - c4))
    have b2 : |2 * p.1.2 4 * (p.2 - tj)| ≤ 2 * H * w := by
      rw [abs_mul, abs_mul, abs_two]
      have : |p.1.2 4| ≤ H := by rw [abs_le]; exact hH4
      nlinarith [abs_nonneg (p.1.2 4), abs_nonneg (p.2 - tj)]
    have b3 : |2 * tj * (p.1.2 4 - c4)| ≤ 4 * w := by
      rw [abs_mul, abs_mul, abs_two]
      nlinarith [abs_nonneg tj, abs_nonneg (p.1.2 4 - c4)]
    linarith
  rw [abs_le] at hbound
  exact hbound

/-- Separated pairs of occupied bins carry at least half of the squared palette mass, when every
window of `2 m + 1` bins carries at most half of it. -/
lemma separated_pairs_lower (Occ : Finset ℤ) (w : ℤ → ℝ) (hw : ∀ c, 0 ≤ w c)
    (htot : ∀ S : Finset ℤ, ∑ c ∈ S, w c ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    (hocc : a ≤ ∑ c ∈ Occ, w c) (m : ℕ)
    (hwin : ∀ c : ℤ, ∑ c' ∈ Finset.Icc (c - m) (c + m), w c' ≤ a ^ 2 / 2) :
    a ^ 2 / 2 ≤ ∑ x ∈ (Occ ×ˢ Occ).filter (fun x => (m : ℤ) < |x.1 - x.2|), w x.1 * w x.2 := by
  classical
  have htotal : ∑ x ∈ Occ ×ˢ Occ, w x.1 * w x.2 = (∑ c ∈ Occ, w c) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Occ ×ˢ Occ)
    (fun x => (m : ℤ) < |x.1 - x.2|) (fun x => w x.1 * w x.2)
  have hnear : ∑ x ∈ (Occ ×ˢ Occ).filter (fun x => ¬ (m : ℤ) < |x.1 - x.2|), w x.1 * w x.2 ≤
      a ^ 2 / 2 := by
    have hre : ∑ x ∈ (Occ ×ˢ Occ).filter (fun x => ¬ (m : ℤ) < |x.1 - x.2|), w x.1 * w x.2 =
        ∑ c ∈ Occ, w c * ∑ c' ∈ Occ.filter (fun c' => ¬ (m : ℤ) < |c - c'|), w c' := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c' _
      split_ifs <;> simp
    rw [hre]
    calc ∑ c ∈ Occ, w c * ∑ c' ∈ Occ.filter (fun c' => ¬ (m : ℤ) < |c - c'|), w c'
        ≤ ∑ c ∈ Occ, w c * (a ^ 2 / 2) := by
          apply Finset.sum_le_sum
          intro c _
          apply mul_le_mul_of_nonneg_left _ (hw c)
          refine le_trans ?_ (hwin c)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro c' hc'
            rw [Finset.mem_filter, not_lt] at hc'
            rw [Finset.mem_Icc]
            have h1 := neg_abs_le (c - c'); have h2 := le_abs_self (c - c')
            constructor <;> linarith [hc'.2]
          · intro c' _ _; exact hw c'
      _ = (∑ c ∈ Occ, w c) * (a ^ 2 / 2) := by rw [Finset.sum_mul]
      _ ≤ 1 * (a ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_right (htot Occ); positivity
      _ = a ^ 2 / 2 := one_mul _
  have hsq : a ^ 2 ≤ (∑ c ∈ Occ, w c) ^ 2 := by
    exact pow_le_pow_left₀ ha hocc 2
  linarith

/-- **Coarse row count, combinatorial core.** Rowbins `v ∈ V` whose witness cells occupy bins
`Occ v` of palette weight at least `a` (windows of `2 m + 1` bins carrying at most `a² / 2`),
when every separated pair of bins is occupied in at most `Λ` witness cells, number at most
`2 Λ / a²`. -/
lemma rowbins_card_mul_le {α : Type*} [DecidableEq α] (V : Finset α) (Occ : α → Finset ℤ)
    (w : ℤ → ℝ) (hw : ∀ c, 0 ≤ w c) (htot : ∀ S : Finset ℤ, ∑ c ∈ S, w c ≤ 1) {a : ℝ}
    (ha : 0 ≤ a) (hocc : ∀ v ∈ V, a ≤ ∑ c ∈ Occ v, w c) (m : ℕ)
    (hwin : ∀ c : ℤ, ∑ c' ∈ Finset.Icc (c - m) (c + m), w c' ≤ a ^ 2 / 2) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpair : ∀ c₁ c₂ : ℤ, (m : ℤ) < |c₁ - c₂| →
      ((V.filter fun v => c₁ ∈ Occ v ∧ c₂ ∈ Occ v).card : ℝ) ≤ Λ) :
    (V.card : ℝ) * (a ^ 2 / 2) ≤ Λ := by
  classical
  apply card_mul_le_of_pairs V (fun v => (Occ v ×ˢ Occ v).filter
    (fun x => (m : ℤ) < |x.1 - x.2|)) w hw hΛ
  · intro v hv
    exact separated_pairs_lower (Occ v) w hw htot ha (hocc v hv) m hwin
  · intro x
    by_cases hx : (m : ℤ) < |x.1 - x.2|
    · calc ((V.filter fun v => x ∈ (Occ v ×ˢ Occ v).filter
            (fun x => (m : ℤ) < |x.1 - x.2|)).card : ℝ)
          = ((V.filter fun v => x.1 ∈ Occ v ∧ x.2 ∈ Occ v).card : ℝ) := by
            congr 2
            apply Finset.filter_congr
            intro v _
            simp [Finset.mem_filter, Finset.mem_product, hx]
        _ ≤ Λ := hpair x.1 x.2 hx
    · have : (V.filter fun v => x ∈ (Occ v ×ˢ Occ v).filter
          (fun x => (m : ℤ) < |x.1 - x.2|)) = ∅ := by
        apply Finset.filter_false_of_mem
        intro v _ h
        exact hx (Finset.mem_filter.mp h).2
      rw [this]; simpa using hΛ
  · exact htot

/-- Slope error of the pair bound. -/
def slopeErr (res eX Gb w' : ℝ) (m : ℕ) : ℝ := (2 * res + 2 * eX + 2 * Gb * w') / ((m : ℝ) * w' - 2 * w')

/-- Intercept error of the pair bound. -/
def interErr (res eX Gb Hc w' : ℝ) (m : ℕ) : ℝ :=
  res + eX + slopeErr res eX Gb w' m * Hc + (Gb + slopeErr res eX Gb w' m) * w'

/-- **Rowbins of one separated pair.** Rowbins `v = (⌊G₀ / wr⌋, ⌊G₁ / wr⌋)` of rows `(G₀, G₁)`
fitting two witnesses with velocities in bins `c₁`, `c₂` (width `w'`, more than `m ≥ 3` bins
apart) and hidden velocities within `eX` of lists `P₁`, `P₂` number at most
`|P₁| |P₂| (2 e₀ / wr + 2) (2 e₁ / wr + 2)`. -/
lemma pair_rowbins_card_le (S : Finset (ℤ × ℤ)) {wr w' res eX Gb Hc : ℝ} (hwr : 0 < wr)
    (hw' : 0 < w') {c₁ c₂ : ℤ} {m : ℕ} (hm : 3 ≤ m) (hsep : (m : ℤ) < |c₁ - c₂|)
    (P₁ P₂ : Finset ℝ) (hres : 0 ≤ res) (heX : 0 ≤ eX) (hGb : 0 ≤ Gb) (hHc : 0 ≤ Hc)
    (hS : ∀ v ∈ S, ∃ G₀ G₁ V₁ V₂ X₁ X₂ : ℝ, v = (⌊G₀ / wr⌋, ⌊G₁ / wr⌋) ∧ |G₁| ≤ Gb ∧
      |X₁ - G₀ - G₁ * V₁| ≤ res ∧ |X₂ - G₀ - G₁ * V₂| ≤ res ∧
      ⌊V₁ / w'⌋ = c₁ ∧ ⌊V₂ / w'⌋ = c₂ ∧ |V₁| ≤ Hc ∧
      (∃ x ∈ P₁, |X₁ - x| ≤ eX) ∧ (∃ x ∈ P₂, |X₂ - x| ≤ eX)) :
    (S.card : ℝ) ≤ P₁.card * P₂.card *
      ((2 * interErr res eX Gb Hc w' m / wr + 2) * (2 * slopeErr res eX Gb w' m / wr + 2)) := by
  classical
  set e₁ : ℝ := slopeErr res eX Gb w' m with he₁'
  have he₁ : e₁ = (2 * res + 2 * eX + 2 * Gb * w') / ((m : ℝ) * w' - 2 * w') := rfl
  set e₀ : ℝ := interErr res eX Gb Hc w' m with he₀'
  have he₀ : e₀ = res + eX + e₁ * Hc + (Gb + e₁) * w' := rfl
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (m : ℝ) * w' - 2 * w' := by nlinarith
  have he₁0 : 0 ≤ e₁ := by rw [he₁]; apply div_nonneg _ hden.le; positivity
  have he₀0 : 0 ≤ e₀ := by rw [he₀]; positivity
  let g₁ : ℝ × ℝ → ℝ := fun x => (x.1 - x.2) / ((c₁ : ℝ) * w' - (c₂ : ℝ) * w')
  let g₀ : ℝ × ℝ → ℝ := fun x => x.1 - g₁ x * ((c₁ : ℝ) * w')
  let box : ℝ × ℝ → Finset (ℤ × ℤ) := fun x =>
    Finset.Icc ⌊(g₀ x - e₀) / wr⌋ ⌊(g₀ x + e₀) / wr⌋ ×ˢ Finset.Icc ⌊(g₁ x - e₁) / wr⌋ ⌊(g₁ x + e₁) / wr⌋
  have hsub : S ⊆ (P₁ ×ˢ P₂).biUnion box := by
    intro v hv
    obtain ⟨G₀, G₁, V₁, V₂, X₁, X₂, rfl, hG₁, hr₁, hr₂, hb₁, hb₂, hV₁, ⟨x₁, hx₁, hX₁⟩,
      ⟨x₂, hx₂, hX₂⟩⟩ := hS v hv
    rw [Finset.mem_biUnion]
    refine ⟨(x₁, x₂), Finset.mem_product.mpr ⟨hx₁, hx₂⟩, ?_⟩
    -- bin facts
    have hb₁a := Int.floor_le (V₁ / w'); have hb₁b := Int.lt_floor_add_one (V₁ / w')
    have hb₂a := Int.floor_le (V₂ / w'); have hb₂b := Int.lt_floor_add_one (V₂ / w')
    rw [hb₁, le_div_iff₀ hw'] at hb₁a
    rw [hb₁, div_lt_iff₀ hw'] at hb₁b
    rw [hb₂, le_div_iff₀ hw'] at hb₂a
    rw [hb₂, div_lt_iff₀ hw'] at hb₂b
    have hcV₁ : |V₁ - (c₁ : ℝ) * w'| ≤ w' := by rw [abs_le]; constructor <;> nlinarith
    have hcV₂ : |V₂ - (c₂ : ℝ) * w'| ≤ w' := by rw [abs_le]; constructor <;> nlinarith
    have hsepV : (m : ℝ) * w' ≤ |V₁ - V₂| := by
      rcases lt_abs.mp hsep with h | h
      · have h' : (m : ℝ) + 1 ≤ (c₁ : ℝ) - c₂ := by exact_mod_cast (show (m : ℤ) + 1 ≤ c₁ - c₂ by omega)
        have : (m : ℝ) * w' ≤ V₁ - V₂ := by nlinarith
        exact le_trans this (le_abs_self _)
      · have h' : (m : ℝ) + 1 ≤ (c₂ : ℝ) - c₁ := by exact_mod_cast (show (m : ℤ) + 1 ≤ c₂ - c₁ by omega)
        have : (m : ℝ) * w' ≤ V₂ - V₁ := by nlinarith
        rw [abs_sub_comm]; exact le_trans this (le_abs_self _)
    have hslope : |G₁ - g₁ (x₁, x₂)| ≤ e₁ := by
      have := slope_close hr₁ hr₂ hsepV (by nlinarith) hcV₁ hcV₂ hX₁ hX₂ hG₁
      rw [he₁]; simpa [g₁] using this
    have hg₁b : |g₁ (x₁, x₂)| ≤ Gb + e₁ := by
      have := abs_sub_abs_le_abs_sub (g₁ (x₁, x₂)) G₁
      rw [abs_sub_comm] at this
      linarith
    have hint : |G₀ - g₀ (x₁, x₂)| ≤ e₀ := by
      have e : G₀ - g₀ (x₁, x₂) = -(X₁ - G₀ - G₁ * V₁) + (X₁ - x₁) - (G₁ - g₁ (x₁, x₂)) * V₁
          - g₁ (x₁, x₂) * (V₁ - (c₁ : ℝ) * w') := by simp only [g₀]; ring
      rw [e]
      have t1 : |(G₁ - g₁ (x₁, x₂)) * V₁| ≤ e₁ * Hc := by
        rw [abs_mul]; exact mul_le_mul hslope hV₁ (abs_nonneg _) he₁0
      have t2 : |g₁ (x₁, x₂) * (V₁ - (c₁ : ℝ) * w')| ≤ (Gb + e₁) * w' := by
        rw [abs_mul]; exact mul_le_mul hg₁b hcV₁ (abs_nonneg _) (by linarith)
      have a1 := abs_sub (-(X₁ - G₀ - G₁ * V₁) + (X₁ - x₁) - (G₁ - g₁ (x₁, x₂)) * V₁)
        (g₁ (x₁, x₂) * (V₁ - (c₁ : ℝ) * w'))
      have a2 := abs_sub (-(X₁ - G₀ - G₁ * V₁) + (X₁ - x₁)) ((G₁ - g₁ (x₁, x₂)) * V₁)
      have a3 := abs_add_le (-(X₁ - G₀ - G₁ * V₁)) (X₁ - x₁)
      rw [abs_neg] at a3
      rw [he₀]; linarith
    exact Finset.mem_product.mpr ⟨floor_mem_Icc_of_close hwr hint,
      floor_mem_Icc_of_close hwr hslope⟩
  have hbox : ∀ x, ((box x).card : ℝ) ≤ (2 * e₀ / wr + 2) * (2 * e₁ / wr + 2) := by
    intro x
    simp only [box, Finset.card_product, Nat.cast_mul]
    exact mul_le_mul (card_Icc_floor_le hwr he₀0) (card_Icc_floor_le hwr he₁0)
      (Nat.cast_nonneg _) (by positivity)
  calc (S.card : ℝ) ≤ (((P₁ ×ˢ P₂).biUnion box).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ x ∈ P₁ ×ˢ P₂, ((box x).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ x ∈ P₁ ×ˢ P₂, (2 * e₀ / wr + 2) * (2 * e₁ / wr + 2) :=
        Finset.sum_le_sum fun x _ => hbox x
    _ = P₁.card * P₂.card * ((2 * e₀ / wr + 2) * (2 * e₁ / wr + 2)) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; ring

/-- The row bin (width `w`) of a row. -/
def rowPair (w : ℝ) (g : ℝ × ℝ) : ℤ × ℤ := (⌊g.1 / w⌋, ⌊g.2 / w⌋)

lemma exists_mem_of_restrict_ne_zero {ρ : Measure Inc} {E A : Set Inc} (hE : MeasurableSet E)
    (h : ρ.restrict E A ≠ 0) : ∃ p ∈ A, p ∈ E := by
  rw [Measure.restrict_apply' hE] at h
  obtain ⟨p, hpA, hpE⟩ := nonempty_of_measure_ne_zero h
  exact ⟨p, hpA, hpE⟩

lemma restrict_eq_zero_of_disjoint {ρ : Measure Inc} {E A : Set Inc} (hE : MeasurableSet E)
    (h : ∀ p ∈ A, p ∉ E) : ρ.restrict E A = 0 := by
  rw [Measure.restrict_apply' hE]
  have : A ∩ E = ∅ := by
    ext p; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact h p
  rw [this, measure_empty]

/-- A non-null event splits into mid cells and coefficient bins, one of which is non-null. -/
lemma exists_piece_ne_zero (μ : Measure Inc) (w' : ℝ) {A : Set Inc} (h : μ A ≠ 0) :
    ∃ (q' : Fin 3 → ℤ) (β : Fin 5 → ℤ),
      μ (A ∩ {p | cellIdx w' (physOf p) = q' ∧ cbin w' p = β}) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply h
  have hsub : A ⊆ ⋃ x : (Fin 3 → ℤ) × (Fin 5 → ℤ),
      (A ∩ {p | cellIdx w' (physOf p) = x.1 ∧ cbin w' p = x.2}) := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨(cellIdx w' (physOf p), cbin w' p), hp, rfl, rfl⟩
  exact measure_mono_null hsub (measure_iUnion_null fun x => hcon x.1 x.2)

/-- Bins of points with `|V| ≤ Hc`. -/
lemma floor_mem_bins {V Hc w : ℝ} (hw : 0 < w) (hV : |V| ≤ Hc) :
    ⌊V / w⌋ ∈ Finset.Icc ⌊-Hc / w⌋ ⌊Hc / w⌋ := by
  rw [abs_le] at hV
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hV.1 hw.le),
    Int.floor_mono (div_le_div_of_nonneg_right hV.2 hw.le)⟩

/-- The palette bins carry total mass at most one. -/
lemma sum_bins_toReal_le_one (π : Measure ℝ) [IsProbabilityMeasure π] (w : ℝ) (S : Finset ℤ) :
    ∑ c ∈ S, (π {v : ℝ | ⌊v / w⌋ = c}).toReal ≤ 1 := by
  have hm : ∀ c : ℤ, MeasurableSet {v : ℝ | ⌊v / w⌋ = c} := fun c =>
    (measurable_id.div_const w).floor (measurableSet_singleton c)
  have hdisj : Set.PairwiseDisjoint (↑S) (fun c : ℤ => {v : ℝ | ⌊v / w⌋ = c}) := by
    intro c _ c' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro v h1 h2
    exact hne (h1.symm.trans h2)
  rw [← ENNReal.toReal_sum (fun c _ => measure_ne_top π _),
    ← measure_biUnion_finset hdisj (fun c _ => hm c)]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    rw [ENNReal.ofReal_one]; exact prob_le_one)

/-- The coarse row-count bound. -/
def rowBound (b wr w' Hc res Gb H' Hl : ℝ) (m : ℕ) : ℝ :=
  2 * H' ^ 2 * ((((wr + 2 * b) / w' + 2) ^ 3 * Hl) ^ 2 *
    ((2 * interErr res ((5 + 2 * Hc) * w') Gb Hc w' m / wr + 2) *
      (2 * slopeErr res ((5 + 2 * Hc) * w') Gb w' m / wr + 2)))

/-- Mid cells met by fine cells meeting the coarse cell `Q`. -/
def midNbhd (b wr w' : ℝ) (Q : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun e => Finset.Icc ⌊(((Q e : ℝ) + 1 / 2) * wr - (wr / 2 + b)) / w'⌋
    ⌊(((Q e : ℝ) + 1 / 2) * wr + (wr / 2 + b)) / w'⌋)

lemma card_midNbhd_le {b wr w' : ℝ} (hb : 0 < b) (hwr : 0 < wr) (hw' : 0 < w') (Q : Fin 3 → ℤ) :
    ((midNbhd b wr w' Q).card : ℝ) ≤ ((wr + 2 * b) / w' + 2) ^ 3 := by
  unfold midNbhd
  rw [Fintype.card_piFinset]
  push_cast
  rw [Fin.prod_univ_three]
  have h : ∀ e : Fin 3, ((Finset.Icc ⌊(((Q e : ℝ) + 1 / 2) * wr - (wr / 2 + b)) / w'⌋
      ⌊(((Q e : ℝ) + 1 / 2) * wr + (wr / 2 + b)) / w'⌋).card : ℝ) ≤ (wr + 2 * b) / w' + 2 := by
    intro e
    have := card_Icc_floor_le (yh := ((Q e : ℝ) + 1 / 2) * wr) hw' (by positivity : 0 ≤ wr / 2 + b)
    have e2 : 2 * (wr / 2 + b) / w' = (wr + 2 * b) / w' := by ring
    linarith
  have h0 : 0 ≤ (wr + 2 * b) / w' + 2 := by positivity
  calc _ ≤ ((wr + 2 * b) / w' + 2) * ((wr + 2 * b) / w' + 2) * ((wr + 2 * b) / w' + 2) := by
        apply mul_le_mul (mul_le_mul (h 0) (h 1) (Nat.cast_nonneg _) h0) (h 2) (Nat.cast_nonneg _)
          (mul_nonneg h0 h0)
    _ = _ := by ring

lemma mem_midNbhd {b wr w' : ℝ} (hb : 0 < b) (hwr : 0 < wr) (hw' : 0 < w') {Q f : Fin 3 → ℤ}
    {p p₀ : Inc} (hp : physOf p ∈ cellSet b f) (hp₀ : physOf p₀ ∈ cellSet b f)
    (hQ : cellIdx wr (physOf p₀) = Q) : cellIdx w' (physOf p) ∈ midNbhd b wr w' Q := by
  unfold midNbhd
  rw [Fintype.mem_piFinset]
  intro e
  have h1 := (mem_cellSet_iff hb).mp hp e
  have h2 := (mem_cellSet_iff hb).mp hp₀ e
  have h3 : physOf p₀ ∈ cellSet wr Q := hQ
  have h4 := (mem_cellSet_iff hwr).mp h3 e
  apply floor_mem_Icc_of_close hw'
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2]

/-- **Coarse row lists in one world.** On a retained set `E` whose incidences fit the rows `G` of
their fine cells (side `b`), with the fine-cell palette domination at velocity bins of width `w'`,
window bounds on the palette and coefficient lists at mid cells of side `w'`, every coarse cell of
side `wr` meets at most `rowBound` row bins. -/
theorem coarse_rows_card_le (ρ : Measure Inc) [IsFiniteMeasure ρ] {E : Set Inc}
    (hEm : MeasurableSet E) (π : Measure ℝ) [IsProbabilityMeasure π]
    {b wr w' Hc res Gb H' Hl : ℝ} (hb : 0 < b) (hwr : 0 < wr) (hw' : 0 < w') (hw'1 : w' ≤ 1)
    (hH' : 0 < H') (hHl : 0 ≤ Hl) (hres : 0 ≤ res) (hGb : 0 ≤ Gb) (hHc : 0 ≤ Hc)
    (G : (Fin 3 → ℤ) → ℝ × ℝ)
    (hE : ∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ (∀ e, |p.1.2 e| ≤ Hc) ∧
      |(G (cellIdx b (physOf p))).1| ≤ Gb ∧ |(G (cellIdx b (physOf p))).2| ≤ Gb ∧
      |(p.1.2 3 + 2 * p.1.2 4 * p.2) - (G (cellIdx b (physOf p))).1 -
        (G (cellIdx b (physOf p))).2 * p.1.2 1| ≤ res)
    (hpal : ∀ (f : Fin 3 → ℤ) (c : ℤ),
      ρ.restrict E (physOf ⁻¹' cellSet b f ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) ≤
        ENNReal.ofReal H' * ρ.restrict E (physOf ⁻¹' cellSet b f) * π {v : ℝ | ⌊v / w'⌋ = c})
    {m : ℕ} (hm : 3 ≤ m)
    (hwin : ∀ c : ℤ, ∑ c' ∈ Finset.Icc (c - m) (c + m), (π {v : ℝ | ⌊v / w'⌋ = c'}).toReal ≤
      H'⁻¹ ^ 2 / 2)
    (hlist : ∀ (q' : Fin 3 → ℤ) (c : ℤ), ∃ L : Finset (Fin 5 → ℤ), (L.card : ℝ) ≤ Hl ∧
      ∀ β, ρ.restrict E {p | cellIdx w' (physOf p) = q' ∧ ⌊p.1.2 1 / w'⌋ = c ∧ cbin w' p = β} ≠ 0 →
        β ∈ L)
    (Q : Fin 3 → ℤ) :
    ({v : ℤ × ℤ | ρ.restrict E {p | cellIdx wr (physOf p) = Q ∧
        rowPair wr (G (cellIdx b (physOf p))) = v} ≠ 0}.ncard : ℝ) ≤
      rowBound b wr w' Hc res Gb H' Hl m := by
  classical
  set eX : ℝ := (5 + 2 * Hc) * w' with heX
  have heX0 : 0 ≤ eX := by positivity
  set ρE : Measure Inc := ρ.restrict E with hρE
  -- the occurring row bins
  set bx : Finset (ℤ × ℤ) := Finset.Icc ⌊-Gb / wr⌋ ⌊Gb / wr⌋ ×ˢ Finset.Icc ⌊-Gb / wr⌋ ⌊Gb / wr⌋
    with hbx
  set V : Finset (ℤ × ℤ) := bx.filter (fun v => ρE {p | cellIdx wr (physOf p) = Q ∧
    rowPair wr (G (cellIdx b (physOf p))) = v} ≠ 0) with hV
  have hVset : {v : ℤ × ℤ | ρE {p | cellIdx wr (physOf p) = Q ∧
      rowPair wr (G (cellIdx b (physOf p))) = v} ≠ 0} = ↑V := by
    ext v
    simp only [Set.mem_ofPred_eq, hV, Finset.coe_filter]
    constructor
    · intro h
      refine ⟨?_, h⟩
      obtain ⟨p, ⟨_, hpv⟩, hpE⟩ := exists_mem_of_restrict_ne_zero hEm h
      obtain ⟨_, _, hG1, hG2, _⟩ := hE p hpE
      rw [← hpv, hbx, Finset.mem_product]
      exact ⟨floor_mem_bins hwr hG1, floor_mem_bins hwr hG2⟩
    · exact fun h => h.2
  rw [hVset, Set.ncard_coe_finset]
  -- a witness fine cell for every occurring row bin
  have hf : ∀ v : ℤ × ℤ, ∃ f : Fin 3 → ℤ, v ∈ V →
      ρE {p | cellIdx wr (physOf p) = Q ∧ cellIdx b (physOf p) = f} ≠ 0 ∧ rowPair wr (G f) = v := by
    intro v
    by_cases hv : v ∈ V
    · have hne := (Finset.mem_filter.mp hv).2
      by_contra hcon
      push_neg at hcon
      apply hne
      have hsub : {p | cellIdx wr (physOf p) = Q ∧ rowPair wr (G (cellIdx b (physOf p))) = v} ⊆
          ⋃ f : Fin 3 → ℤ, ({p | cellIdx wr (physOf p) = Q ∧ cellIdx b (physOf p) = f} ∩
            {_p | rowPair wr (G f) = v}) := by
        intro p hp
        exact Set.mem_iUnion.mpr ⟨cellIdx b (physOf p), ⟨hp.1, rfl⟩, hp.2⟩
      refine measure_mono_null hsub (measure_iUnion_null fun f => ?_)
      obtain ⟨_, hf2⟩ := hcon f
      by_cases hfv : rowPair wr (G f) = v
      · have h0 : ρE {p | cellIdx wr (physOf p) = Q ∧ cellIdx b (physOf p) = f} = 0 := by
          by_contra h0; exact hf2 h0 hfv
        exact measure_mono_null Set.inter_subset_left h0
      · have : ({p | cellIdx wr (physOf p) = Q ∧ cellIdx b (physOf p) = f} ∩
            {_p : Inc | rowPair wr (G f) = v}) = ∅ := by
          ext p; simp [hfv]
        rw [this, measure_empty]
    · exact ⟨0, fun h => absurd h hv⟩
  choose f hf using hf
  -- a point of each witness cell in the coarse cell
  have hp₀ : ∀ v ∈ V, ∃ p₀ ∈ E, cellIdx wr (physOf p₀) = Q ∧ cellIdx b (physOf p₀) = f v := by
    intro v hv
    obtain ⟨p, ⟨h1, h2⟩, hpE⟩ := exists_mem_of_restrict_ne_zero hEm (hf v hv).1
    exact ⟨p, hpE, h1, h2⟩
  -- occupied velocity bins of the witness cells
  set Cb : Finset ℤ := Finset.Icc ⌊-Hc / w'⌋ ⌊Hc / w'⌋ with hCb
  set Occ : ℤ × ℤ → Finset ℤ := fun v => Cb.filter (fun c =>
    ρE (physOf ⁻¹' cellSet b (f v) ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) ≠ 0) with hOcc
  set wt : ℤ → ℝ := fun c => (π {x : ℝ | ⌊x / w'⌋ = c}).toReal with hwt
  have hwt0 : ∀ c, 0 ≤ wt c := fun c => ENNReal.toReal_nonneg
  have hocc : ∀ v ∈ V, H'⁻¹ ≤ ∑ c ∈ Occ v, wt c := by
    intro v hv
    set F : Set Inc := physOf ⁻¹' cellSet b (f v) with hF
    have hFpos : ρE F ≠ 0 := by
      intro h0
      apply (hf v hv).1
      apply measure_mono_null _ h0
      intro p hp; exact hp.2
    have hFtop : ρE F ≠ ⊤ := measure_ne_top _ _
    have hcover : ρE F ≤ ∑ c ∈ Cb, ρE (F ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) := by
      have hsub : F ⊆ (⋃ c ∈ Cb, F ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) ∪
          {p : Inc | ⌊p.1.2 1 / w'⌋ ∉ Cb} := by
        intro p hp
        by_cases hc : ⌊p.1.2 1 / w'⌋ ∈ Cb
        · left; exact Set.mem_biUnion hc ⟨hp, rfl⟩
        · right; exact hc
      have hnull : ρE {p : Inc | ⌊p.1.2 1 / w'⌋ ∉ Cb} = 0 := by
        apply restrict_eq_zero_of_disjoint hEm
        intro p hp hpE
        exact hp (floor_mem_bins hw' ((hE p hpE).2.1 1))
      calc ρE F ≤ ρE ((⋃ c ∈ Cb, F ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) ∪
            {p : Inc | ⌊p.1.2 1 / w'⌋ ∉ Cb}) := measure_mono hsub
        _ ≤ ρE (⋃ c ∈ Cb, F ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) + ρE {p : Inc | ⌊p.1.2 1 / w'⌋ ∉ Cb} :=
            measure_union_le _ _
        _ = ρE (⋃ c ∈ Cb, F ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) := by rw [hnull, add_zero]
        _ ≤ ∑ c ∈ Cb, ρE (F ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) := measure_biUnion_finset_le _ _
    have hsumOcc : ∑ c ∈ Cb, ρE (F ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) =
        ∑ c ∈ Occ v, ρE (F ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) := by
      rw [hOcc]; exact (Finset.sum_filter_ne_zero _).symm
    have hdom : ρE F ≤ ENNReal.ofReal H' * ρE F * ∑ c ∈ Occ v, π {x : ℝ | ⌊x / w'⌋ = c} := by
      calc ρE F ≤ ∑ c ∈ Occ v, ρE (F ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) := hsumOcc ▸ hcover
        _ ≤ ∑ c ∈ Occ v, ENNReal.ofReal H' * ρE F * π {x : ℝ | ⌊x / w'⌋ = c} :=
            Finset.sum_le_sum fun c _ => hpal (f v) c
        _ = _ := by rw [Finset.mul_sum]
    have h1 : 1 ≤ ENNReal.ofReal H' * ∑ c ∈ Occ v, π {x : ℝ | ⌊x / w'⌋ = c} := by
      have : ρE F * 1 ≤ ρE F * (ENNReal.ofReal H' * ∑ c ∈ Occ v, π {x : ℝ | ⌊x / w'⌋ = c}) := by
        rw [mul_one]
        calc ρE F ≤ _ := hdom
          _ = _ := by ring
      exact (ENNReal.mul_le_mul_iff_right hFpos hFtop).mp this
    have hfin : ∑ c ∈ Occ v, π {x : ℝ | ⌊x / w'⌋ = c} ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun c _ => measure_ne_top _ _
    have h2 : (1 : ℝ) ≤ H' * ∑ c ∈ Occ v, wt c := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hH'.le, ENNReal.toReal_sum
        (fun c _ => measure_ne_top _ _)] at this
      simpa [hwt] using this
    calc H'⁻¹ = H'⁻¹ * 1 := (mul_one _).symm
      _ ≤ H'⁻¹ * (H' * ∑ c ∈ Occ v, wt c) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hH'.le)
      _ = ∑ c ∈ Occ v, wt c := by field_simp
  -- coefficient lists and predicted hidden velocities
  choose L hLcard hL using hlist
  set nbhd : Finset (Fin 3 → ℤ) := midNbhd b wr w' Q with hnbhd
  set P : ℤ → Finset ℝ := fun c => nbhd.biUnion (fun q' => (L q' c).image (predX w' (q' 0)))
    with hP
  set nb : ℝ := ((wr + 2 * b) / w' + 2) ^ 3 with hnb
  have hPcard : ∀ c, ((P c).card : ℝ) ≤ nb * Hl := by
    intro c
    calc ((P c).card : ℝ) ≤ ∑ q' ∈ nbhd, (((L q' c).image (predX w' (q' 0))).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q' ∈ nbhd, Hl := by
          apply Finset.sum_le_sum; intro q' _
          exact le_trans (by exact_mod_cast Finset.card_image_le) (hLcard q' c)
      _ = nbhd.card * Hl := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ nb * Hl := mul_le_mul_of_nonneg_right (card_midNbhd_le hb hwr hw' Q) hHl
  -- witnesses of occupied bins
  have hwit : ∀ v ∈ V, ∀ c ∈ Occ v, ∃ p ∈ E, cellIdx b (physOf p) = f v ∧
      ⌊p.1.2 1 / w'⌋ = c ∧ ∃ x ∈ P c, |(p.1.2 3 + 2 * p.1.2 4 * p.2) - x| ≤ eX := by
    intro v hv c hc
    have hne : ρE (physOf ⁻¹' cellSet b (f v) ∩ {p | ⌊p.1.2 1 / w'⌋ = c}) ≠ 0 :=
      (Finset.mem_filter.mp hc).2
    obtain ⟨q', β, hqβ⟩ := exists_piece_ne_zero ρE w' hne
    have hβ : β ∈ L q' c := by
      apply hL q' c β
      intro h0
      apply hqβ (measure_mono_null _ h0)
      rintro p ⟨⟨_, hp2⟩, hp3, hp4⟩
      exact ⟨hp3, hp2, hp4⟩
    obtain ⟨p, ⟨⟨hp1, hp2⟩, hp3, hp4⟩, hpE⟩ := exists_mem_of_restrict_ne_zero hEm hqβ
    obtain ⟨p₀, hp₀E, hp₀Q, hp₀f⟩ := hp₀ v hv
    refine ⟨p, hpE, hp1, hp2, predX w' (q' 0) β, ?_, ?_⟩
    · simp only [hP, Finset.mem_biUnion, Finset.mem_image]
      refine ⟨q', ?_, β, hβ, rfl⟩
      rw [← hp3]
      exact mem_midNbhd hb hwr hw' hp1 hp₀f hp₀Q
    · have h := abs_sub_predX_le hw' hw'1 (hE p hpE).2.1 (hE p hpE).1
      have hq0 : q' 0 = ⌊p.2 / w'⌋ := by
        rw [← hp3]; simp [cellIdx, physOf_apply]
      rw [hq0, ← hp4]
      exact h
  -- every separated pair is occupied in few witness cells
  set Λ : ℝ := (nb * Hl) ^ 2 * ((2 * interErr res eX Gb Hc w' m / wr + 2) *
      (2 * slopeErr res eX Gb w' m / wr + 2)) with hΛ
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (m : ℝ) * w' - 2 * w' := by nlinarith
  have hsl0 : 0 ≤ slopeErr res eX Gb w' m := by
    unfold slopeErr; apply div_nonneg _ hden.le; positivity
  have hin0 : 0 ≤ interErr res eX Gb Hc w' m := by unfold interErr; positivity
  have hΛ0 : 0 ≤ Λ := by positivity
  have hpair : ∀ c₁ c₂ : ℤ, (m : ℤ) < |c₁ - c₂| →
      ((V.filter fun v => c₁ ∈ Occ v ∧ c₂ ∈ Occ v).card : ℝ) ≤ Λ := by
    intro c₁ c₂ hsep
    have := pair_rowbins_card_le (V.filter fun v => c₁ ∈ Occ v ∧ c₂ ∈ Occ v) hwr hw' hm hsep
      (P c₁) (P c₂) hres heX0 hGb hHc (by
        intro v hv
        obtain ⟨hvV, hc₁, hc₂⟩ := Finset.mem_filter.mp hv
        obtain ⟨p₁, hp₁E, hp₁f, hp₁c, x₁, hx₁, hX₁⟩ := hwit v hvV c₁ hc₁
        obtain ⟨p₂, hp₂E, hp₂f, hp₂c, x₂, hx₂, hX₂⟩ := hwit v hvV c₂ hc₂
        obtain ⟨_, hH₁, _, hG₁, hr₁⟩ := hE p₁ hp₁E
        obtain ⟨_, _, _, _, hr₂⟩ := hE p₂ hp₂E
        rw [hp₁f] at hG₁ hr₁
        rw [hp₂f] at hr₂
        refine ⟨(G (f v)).1, (G (f v)).2, p₁.1.2 1, p₂.1.2 1, p₁.1.2 3 + 2 * p₁.1.2 4 * p₁.2,
          p₂.1.2 3 + 2 * p₂.1.2 4 * p₂.2, ?_, hG₁, hr₁, hr₂, hp₁c, hp₂c, hH₁ 1, ⟨x₁, hx₁, hX₁⟩,
          ⟨x₂, hx₂, hX₂⟩⟩
        exact (hf v hvV).2.symm)
    calc _ ≤ _ := this
      _ ≤ (nb * Hl) * (nb * Hl) * ((2 * interErr res eX Gb Hc w' m / wr + 2) *
            (2 * slopeErr res eX Gb w' m / wr + 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (hPcard c₁) (hPcard c₂) (Nat.cast_nonneg _) (by positivity)
      _ = Λ := by rw [hΛ]; ring
  have hmain := rowbins_card_mul_le V Occ wt hwt0 (sum_bins_toReal_le_one π w')
    (inv_nonneg.mpr hH'.le) hocc m hwin hΛ0 hpair
  -- conclude
  unfold rowBound
  have hH'2 : 0 < H' ^ 2 := by positivity
  have : (V.card : ℝ) = (V.card : ℝ) * (H'⁻¹ ^ 2 / 2) * (2 * H' ^ 2) := by
    field_simp
  rw [this]
  calc (V.card : ℝ) * (H'⁻¹ ^ 2 / 2) * (2 * H' ^ 2) ≤ Λ * (2 * H' ^ 2) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = _ := by rw [hΛ]; ring

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
