import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Spread
import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Measure

/-!
# The Cantor-type hidden coordinate of the synthetic model

`hid e e₁ G i u = (spread e e₁ G i + u) / 2^(e G)`. Its generation-`g` cell is fixed by the
prefix `i / 2^(e₁ (G - g))` of the index, and an interval of length at most `2^(-e g)` meets at
most two such cells, so it carries mass at most `2 · 2^(-e₁ g)`. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

/-- The hidden coordinate of the synthetic model. -/
def hid (e e₁ G : ℕ) (i : ℕ) (u : ℝ) : ℝ := ((spread e e₁ G i : ℝ) + u) / 2 ^ (e * G)

theorem measurable_hid (e e₁ G : ℕ) : Measurable (fun p : ℕ × ℝ => hid e e₁ G p.1 p.2) := by
  unfold hid
  have h1 : Measurable (fun p : ℕ × ℝ => (spread e e₁ G p.1 : ℝ)) :=
    (measurable_from_nat (f := fun i : ℕ => (spread e e₁ G i : ℝ))).comp measurable_fst
  exact (h1.add measurable_snd).div_const _

/-- The prefix of an index at generation `g`. -/
def pre (e₁ G g i : ℕ) : ℕ := i / 2 ^ (e₁ * (G - g))

/-- The generation-`g` cell of a hidden value. -/
theorem hid_mem_cell {e e₁ : ℕ} (h : e₁ ≤ e) {G g : ℕ} (hg : g ≤ G) (i : ℕ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    (spread e e₁ g (pre e₁ G g i) : ℝ) / 2 ^ (e * g) ≤ hid e e₁ G i u ∧
      hid e e₁ G i u ≤ ((spread e e₁ g (pre e₁ G g i) : ℝ) + 1) / 2 ^ (e * g) := by
  obtain ⟨m, rfl⟩ : ∃ m, G = g + m := ⟨G - g, by omega⟩
  have hd := spread_div h g m i
  have hpre : pre e₁ (g + m) g i = i / 2 ^ (e₁ * m) := by simp [pre]
  rw [hpre, ← hd]
  set X := spread e e₁ (g + m) i with hX
  set D := 2 ^ (e * m) with hD
  have hDpos : (0 : ℝ) < D := by positivity
  have hlo : (X / D : ℕ) * D ≤ X := Nat.div_mul_le_self X D
  have hhi : X < (X / D + 1) * D := by
    have := Nat.lt_div_mul_add (a := X) (b := D) (by positivity)
    linarith
  have hlo' : ((X / D : ℕ) : ℝ) * D ≤ X := by exact_mod_cast hlo
  have hhi' : (X : ℝ) + 1 ≤ ((X / D : ℕ) + 1 : ℝ) * D := by
    have : X + 1 ≤ (X / D + 1) * D := hhi
    exact_mod_cast this
  have hpow : (2 : ℝ) ^ (e * (g + m)) = 2 ^ (e * g) * D := by
    rw [hD, Nat.cast_pow, Nat.cast_ofNat, ← pow_add, ← mul_add]
  unfold hid
  rw [hpow]
  have hEg : (0 : ℝ) < 2 ^ (e * g) := by positivity
  constructor
  · rw [div_le_div_iff₀ hEg (by positivity)]
    nlinarith [hu.1]
  · rw [div_le_div_iff₀ (by positivity) hEg]
    nlinarith [hu.2]

/-- At most two naturals lie in a half-open interval of length two. -/
theorem card_int_window (y : ℝ) (Z : Set ℕ) (hZ : ∀ p ∈ Z, y - 1 ≤ p ∧ (p : ℝ) < y + 1) :
    Z.encard ≤ 2 := by
  by_contra hc
  push Not at hc
  have hne : Z.Nonempty := by
    rw [← Set.encard_pos]
    exact lt_of_le_of_lt (zero_le) hc
  obtain ⟨a, ha⟩ := hne
  have h2' : 1 < (Z \ {a}).encard := by
    have := Set.encard_sdiff_singleton_add_one ha
    by_contra hle
    push Not at hle
    have : Z.encard ≤ 2 := by
      rw [← this]
      calc (Z \ {a}).encard + 1 ≤ 1 + 1 := by gcongr
        _ = 2 := by norm_num
    exact absurd hc (not_lt.mpr this)
  obtain ⟨b, c, hb, hc', hbc⟩ := Set.one_lt_encard_iff.mp h2'
  have hab : a ≠ b := fun h => hb.2 (by simp [h])
  have hac : a ≠ c := fun h => hc'.2 (by simp [h])
  replace hb := hb.1
  replace hc' := hc'.1
  have h1 := hZ a ha
  have h2 := hZ b hb
  have h3 := hZ c hc'
  have k1 : a < b + 2 := by
    have : (a : ℝ) < b + 2 := by linarith
    exact_mod_cast this
  have k2 : b < a + 2 := by
    have : (b : ℝ) < a + 2 := by linarith
    exact_mod_cast this
  have k3 : a < c + 2 := by
    have : (a : ℝ) < c + 2 := by linarith
    exact_mod_cast this
  have k4 : c < a + 2 := by
    have : (c : ℝ) < a + 2 := by linarith
    exact_mod_cast this
  have k5 : b < c + 2 := by
    have : (b : ℝ) < c + 2 := by linarith
    exact_mod_cast this
  have k6 : c < b + 2 := by
    have : (c : ℝ) < b + 2 := by linarith
    exact_mod_cast this
  omega

theorem pre_lt {e₁ G g i : ℕ} (hg : g ≤ G) (hi : i < 2 ^ (e₁ * G)) : pre e₁ G g i < 2 ^ (e₁ * g) := by
  unfold pre
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  calc i < 2 ^ (e₁ * G) := hi
    _ = 2 ^ (e₁ * g + e₁ * (G - g)) := by congr 1; rw [← mul_add]; congr 1; omega

/-- **Hidden cap.** An interval of length at most `2^(-e g)` has hidden mass at most
`2 · 2^(-e₁ g)`. -/
theorem hid_cap {e e₁ : ℕ} (h : e₁ ≤ e) {G g : ℕ} (hg : g ≤ G) (x w : ℝ)
    (hw : w ≤ 1 / 2 ^ (e * g)) :
    ((idx (2 ^ (e₁ * G))).prod U) {p | hid e e₁ G p.1 p.2 ∈ Ico x (x + w)} ≤
      2 * ((2 : ENNReal) ^ (e₁ * g))⁻¹ := by
  classical
  set M := 2 ^ (e₁ * G) with hM
  set D := 2 ^ (e₁ * (G - g)) with hD
  set y := x * 2 ^ (e * g) with hy
  have hEg : (0 : ℝ) < 2 ^ (e * g) := by positivity
  -- the indices whose cell can meet the interval
  set S : Finset ℕ := (Finset.range M).filter
    (fun i => y - 1 ≤ (spread e e₁ g (pre e₁ G g i) : ℝ) ∧
      (spread e e₁ g (pre e₁ G g i) : ℝ) < y + 1) with hS
  have hsub : {p : ℕ × ℝ | hid e e₁ G p.1 p.2 ∈ Ico x (x + w)} ⊆
      ((↑S : Set ℕ) ∪ (Iio M)ᶜ) ×ˢ univ ∪ univ ×ˢ (Icc (0 : ℝ) 1)ᶜ := by
    intro p hp
    by_cases hu : p.2 ∈ Icc (0 : ℝ) 1
    · by_cases hi : p.1 < M
      · left
        refine ⟨Or.inl ?_, trivial⟩
        simp only [hS, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
        refine ⟨hi, ?_⟩
        obtain ⟨hlo, hhi⟩ := hid_mem_cell h hg p.1 hu
        obtain ⟨hx1, hx2⟩ := hp
        set c := (spread e e₁ g (pre e₁ G g p.1) : ℝ)
        constructor
        · -- (c + 1) / 2^(eg) ≥ hid ≥ x
          have : x ≤ (c + 1) / 2 ^ (e * g) := hx1.trans hhi
          rw [le_div_iff₀ hEg] at this
          rw [hy]; linarith
        · have h1 : c / 2 ^ (e * g) < x + w := lt_of_le_of_lt hlo hx2
          have h2 : x + w ≤ x + 1 / 2 ^ (e * g) := by linarith
          have h3 : c / 2 ^ (e * g) < x + 1 / 2 ^ (e * g) := lt_of_lt_of_le h1 h2
          rw [div_lt_iff₀ hEg, add_mul, one_div, inv_mul_cancel₀ hEg.ne'] at h3
          rw [hy]; linarith
      · left
        exact ⟨Or.inr (by simpa using hi), trivial⟩
    · right
      exact ⟨trivial, hu⟩
  have hcard : S.card ≤ D * 2 := by
    -- the cell values form a window of at most two naturals
    have himg : (S.image (fun i => spread e e₁ g (pre e₁ G g i))).card ≤ 2 := by
      have hw2 := card_int_window y (↑(S.image (fun i => spread e e₁ g (pre e₁ G g i))))
        (by
          intro k hk
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hk
          obtain ⟨i, hi, rfl⟩ := hk
          simp only [hS, Finset.mem_filter] at hi
          exact hi.2)
      rw [Set.encard_coe_eq_coe_finsetCard] at hw2
      exact_mod_cast hw2
    have hfib : ∀ k ∈ S.image (fun i => spread e e₁ g (pre e₁ G g i)),
        (S.filter (fun i => spread e e₁ g (pre e₁ G g i) = k)).card ≤ D := by
      intro k hk
      simp only [Finset.mem_image] at hk
      obtain ⟨i₀, hi₀, rfl⟩ := hk
      have hi₀M : i₀ < M := by
        simp only [hS, Finset.mem_filter, Finset.mem_range] at hi₀; exact hi₀.1
      calc (S.filter (fun i => spread e e₁ g (pre e₁ G g i) =
              spread e e₁ g (pre e₁ G g i₀))).card
          ≤ (Finset.Ico (pre e₁ G g i₀ * D) (pre e₁ G g i₀ * D + D)).card := by
            refine Finset.card_le_card fun i hi => ?_
            simp only [Finset.mem_filter, hS, Finset.mem_range] at hi
            have hpre : pre e₁ G g i = pre e₁ G g i₀ :=
              spread_injective h g (pre_lt hg hi.1.1) (pre_lt hg hi₀M) hi.2
            have hdiv : i / D = pre e₁ G g i₀ := by rw [← hpre]; rfl
            simp only [Finset.mem_Ico]
            have hDpos : 0 < D := by positivity
            constructor
            · rw [← hdiv]; exact Nat.div_mul_le_self i D
            · rw [← hdiv]
              have := Nat.lt_div_mul_add (a := i) hDpos
              linarith
        _ = D := by simp
    have := Finset.card_le_mul_card_image S D hfib
    calc S.card ≤ D * (S.image _).card := this
      _ ≤ D * 2 := Nat.mul_le_mul_left _ himg
  calc ((idx M).prod U) {p | hid e e₁ G p.1 p.2 ∈ Ico x (x + w)}
      ≤ ((idx M).prod U) (((↑S : Set ℕ) ∪ (Iio M)ᶜ) ×ˢ univ ∪ univ ×ˢ (Icc (0 : ℝ) 1)ᶜ) :=
        measure_mono hsub
    _ ≤ ((idx M).prod U) (((↑S : Set ℕ) ∪ (Iio M)ᶜ) ×ˢ univ) +
          ((idx M).prod U) (univ ×ˢ (Icc (0 : ℝ) 1)ᶜ) := measure_union_le _ _
    _ = idx M ((↑S : Set ℕ) ∪ (Iio M)ᶜ) := by
        rw [Measure.prod_prod, Measure.prod_prod]
        simp [U]
    _ ≤ (M : ENNReal)⁻¹ * (D * 2 : ℕ) := by
        apply idx_le_of_card
        calc (((↑S : Set ℕ) ∪ (Iio M)ᶜ) ∩ Iio M).encard ≤ (↑S : Set ℕ).encard := by
              apply Set.encard_le_encard
              intro i hi
              rcases hi with ⟨hi1 | hi1, hi2⟩
              · exact hi1
              · exact absurd hi2 hi1
          _ = S.card := Set.encard_coe_eq_coe_finsetCard S
          _ ≤ (D * 2 : ℕ) := by exact_mod_cast hcard
    _ = 2 * ((2 : ENNReal) ^ (e₁ * g))⁻¹ := by
        rw [hM, hD]
        push_cast
        have hsplit : (2 : ENNReal) ^ (e₁ * G) = 2 ^ (e₁ * g) * 2 ^ (e₁ * (G - g)) := by
          rw [← pow_add, ← mul_add, Nat.add_sub_cancel' hg]
        rw [hsplit, ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp))]
        have h2 : (2 : ENNReal) ^ (e₁ * (G - g)) ≠ 0 := by positivity
        have h3 : (2 : ENNReal) ^ (e₁ * (G - g)) ≠ ⊤ := by simp
        calc ((2 : ENNReal) ^ (e₁ * g))⁻¹ * ((2 : ENNReal) ^ (e₁ * (G - g)))⁻¹ *
              ((2 : ENNReal) ^ (e₁ * (G - g)) * 2)
            = ((2 : ENNReal) ^ (e₁ * g))⁻¹ * 2 *
              (((2 : ENNReal) ^ (e₁ * (G - g)))⁻¹ * (2 : ENNReal) ^ (e₁ * (G - g))) := by ring
          _ = 2 * ((2 : ENNReal) ^ (e₁ * g))⁻¹ := by
              rw [ENNReal.inv_mul_cancel h2 h3, mul_one, mul_comm]

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
