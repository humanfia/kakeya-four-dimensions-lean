-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.BushProfile.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/BushProfile.lean (95ffa93).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Profiles

/-!
# Profiles of sets of unit vectors

For a finite set `Q` of unit vectors (a bush), the profile `F i = cellProfile Q B i` counts
occupied grid squares of side `B ^ (-i)`.
* `cellCount_circle`: for `ρ' ≤ ρ`, `cellCount Q ρ' ≤ 12 (ρ / ρ' + 2) cellCount Q ρ`: on each
  of four arcs of the circle one coordinate is a `1`-Lipschitz function of the other, so a
  `ρ`-square holds at most `3 (ρ / ρ' + 2)` occupied `ρ'`-squares of each arc.
* `cellProfile_mono'`: `F i ≤ F j + log_B 4` for `i ≤ j`;
  `cellProfile_circle_lip`: `F j - F i ≤ (j - i) + log_B 36` for `i ≤ j`;
  `cellProfile_ge_of_balls`: `F t ≥ α - β` if `#Q ≥ B ^ α` and the `2 B ^ (-t)`-balls around
  the points of `Q` hold at most `B ^ β` points.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high

attribute [local instance] Classical.propDecidable

/-- The coordinates of a unit vector. -/
theorem unit_coords {e : E2} (he : ‖e‖ = 1) : e 0 ^ 2 + e 1 ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq e
  rw [he, Fin.sum_univ_two] at h
  linarith

/-- On the circle, where `|a| ≤ |b|` and `b` keeps its sign, `b` is a `1`-Lipschitz function
of `a`. -/
theorem coord_lip {a b a' b' : ℝ} (h : a ^ 2 + b ^ 2 = 1) (h' : a' ^ 2 + b' ^ 2 = 1)
    (h1 : |a| ≤ |b|) (h1' : |a'| ≤ |b'|) (hs : 0 < b * b') : |b - b'| ≤ |a - a'| := by
  have key : (b - b') * (b + b') = (a' - a) * (a' + a) := by nlinarith
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hs
  have hadd : |b + b'| = |b| + |b'| := by
    rw [abs_add_eq_add_abs_iff]
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hs with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · exact Or.inl ⟨hb1.le, hb2.le⟩
    · exact Or.inr ⟨hb1.le, hb2.le⟩
  have hpos : 0 < |b + b'| := by
    rw [hadd]
    have := abs_pos.mpr hb
    have := abs_nonneg b'
    linarith
  have hsum : |a' + a| ≤ |b + b'| := by
    calc |a' + a| ≤ |a'| + |a| := abs_add_le _ _
      _ ≤ |b| + |b'| := by linarith
      _ = |b + b'| := hadd.symm
  have habs := congrArg abs key
  rw [abs_mul, abs_mul] at habs
  have h2 : |b - b'| * |b + b'| ≤ |a - a'| * |b + b'| := by
    rw [habs, abs_sub_comm a' a]
    exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  exact le_of_mul_le_mul_right h2 hpos

/-- Points within `ρ` have floors within one. -/
theorem floor_le_floor_add_one_of_abs_lt {x y ρ : ℝ} (hρ : 0 < ρ) (h : |x - y| < ρ) :
    ⌊x / ρ⌋ ≤ ⌊y / ρ⌋ + 1 := by
  have h1 : x / ρ ≤ y / ρ + 1 := by
    rw [div_add_one hρ.ne', div_le_div_iff_of_pos_right hρ]
    linarith [(abs_lt.mp h).2]
  have := Int.floor_le_floor h1
  rwa [Int.floor_add_one] at this

/-- One arc: if `v` is a `1`-Lipschitz function of `u` on `Q`, a `ρ`-square of the
coordinates `(u, v)` holds at most `3 (ρ / ρ' + 2)` occupied `ρ'`-squares. -/
theorem piece_count (Q : Finset E2) (u v : E2 → ℝ)
    (hlip : ∀ e ∈ Q, ∀ e' ∈ Q, |v e - v e'| ≤ |u e - u e'|) {ρ ρ' : ℝ} (hρ' : 0 < ρ')
    (hρ : 0 < ρ) :
    ((Q.image (fun e => (⌊u e / ρ'⌋, ⌊v e / ρ'⌋))).card : ℝ) ≤
      3 * (ρ / ρ' + 2) * (Q.image (fun e => (⌊u e / ρ⌋, ⌊v e / ρ⌋))).card := by
  classical
  set f' : E2 → ℤ × ℤ := fun e => (⌊u e / ρ'⌋, ⌊v e / ρ'⌋) with hf'
  set f : E2 → ℤ × ℤ := fun e => (⌊u e / ρ⌋, ⌊v e / ρ⌋) with hf
  set g : E2 → (ℤ × ℤ) × ℤ := fun e => (f e, ⌊u e / ρ'⌋) with hg
  -- fine squares over a pair (coarse square, fine column): at most 3
  have h1 : ((Q.image f').card : ℝ) ≤ 3 * (Q.image g).card := by
    have hsub : Q.image f' ⊆
        (Q.image g).biUnion (fun w => (Q.filter (fun e => g e = w)).image f') := by
      intro t ht
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_biUnion.mpr ⟨g e, Finset.mem_image_of_mem g he,
        Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩⟩
    have hfib : ∀ w ∈ Q.image g, ((Q.filter (fun e => g e = w)).image f').card ≤ 3 := by
      intro w hw
      obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp hw
      have hsub2 : (Q.filter (fun e => g e = g e₀)).image f' ⊆
          ({⌊u e₀ / ρ'⌋} : Finset ℤ) ×ˢ Finset.Icc (⌊v e₀ / ρ'⌋ - 1) (⌊v e₀ / ρ'⌋ + 1) := by
        intro t ht
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨heQ, hge⟩ := Finset.mem_filter.mp he
        have hk : ⌊u e / ρ'⌋ = ⌊u e₀ / ρ'⌋ := (Prod.ext_iff.mp hge).2
        have hu : |u e - u e₀| < ρ' := abs_sub_lt_of_floor_eq hρ' hk
        have hv : |v e - v e₀| < ρ' := (hlip e heQ e₀ he₀).trans_lt hu
        have hv' : |v e₀ - v e| < ρ' := by rwa [abs_sub_comm]
        have b1 := floor_le_floor_add_one_of_abs_lt hρ' hv
        have b2 := floor_le_floor_add_one_of_abs_lt hρ' hv'
        refine Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hk,
          Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
        · show ⌊v e₀ / ρ'⌋ - 1 ≤ ⌊v e / ρ'⌋
          omega
        · show ⌊v e / ρ'⌋ ≤ ⌊v e₀ / ρ'⌋ + 1
          exact b1
      have hc := Finset.card_le_card hsub2
      rw [Finset.card_product, Finset.card_singleton, Int.card_Icc] at hc
      have h3 : (⌊v e₀ / ρ'⌋ + 1 + 1 - (⌊v e₀ / ρ'⌋ - 1)).toNat = 3 := by omega
      rw [h3] at hc
      simpa using hc
    calc ((Q.image f').card : ℝ)
        ≤ ((Q.image g).biUnion (fun w => (Q.filter (fun e => g e = w)).image f')).card := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ w ∈ Q.image g, (((Q.filter (fun e => g e = w)).image f').card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ Q.image g, (3 : ℝ) :=
          Finset.sum_le_sum (fun w hw => by exact_mod_cast hfib w hw)
      _ = 3 * (Q.image g).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- fine columns over a coarse square: at most `ρ / ρ' + 2`
  have h2 : ((Q.image g).card : ℝ) ≤ (ρ / ρ' + 2) * (Q.image f).card := by
    have hsub : Q.image g ⊆
        (Q.image f).biUnion (fun c => (Q.filter (fun e => f e = c)).image g) := by
      intro t ht
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_biUnion.mpr ⟨f e, Finset.mem_image_of_mem f he,
        Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩⟩
    have hfib : ∀ c ∈ Q.image f,
        (((Q.filter (fun e => f e = c)).image g).card : ℝ) ≤ ρ / ρ' + 2 := by
      intro c _
      have hsub2 : (Q.filter (fun e => f e = c)).image g ⊆
          ({c} : Finset (ℤ × ℤ)) ×ˢ
            Finset.Icc ⌊((c.1 : ℝ) * ρ) / ρ'⌋ ⌊((c.1 : ℝ) * ρ + ρ) / ρ'⌋ := by
        intro t ht
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨_, hfe⟩ := Finset.mem_filter.mp he
        have hc1 : ⌊u e / ρ⌋ = c.1 := by rw [← hfe]
        have l1 := Int.floor_le (u e / ρ)
        have l2 := Int.lt_floor_add_one (u e / ρ)
        rw [hc1] at l1 l2
        have hu1 : (c.1 : ℝ) * ρ ≤ u e := by rwa [le_div_iff₀ hρ] at l1
        have hu2 : u e ≤ (c.1 : ℝ) * ρ + ρ := by
          rw [div_lt_iff₀ hρ] at l2; linarith
        refine Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hfe, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
        · exact Int.floor_le_floor (div_le_div_of_nonneg_right hu1 hρ'.le)
        · exact Int.floor_le_floor (div_le_div_of_nonneg_right hu2 hρ'.le)
      have hc := Finset.card_le_card hsub2
      rw [Finset.card_product, Finset.card_singleton, one_mul] at hc
      have hr := floor_range_card (a := (c.1 : ℝ) * ρ) hρ' hρ
      calc (((Q.filter (fun e => f e = c)).image g).card : ℝ)
          ≤ ((Finset.Icc ⌊((c.1 : ℝ) * ρ) / ρ'⌋ ⌊((c.1 : ℝ) * ρ + ρ) / ρ'⌋).card : ℝ) := by
            exact_mod_cast hc
        _ ≤ ρ / ρ' + 2 := hr
    calc ((Q.image g).card : ℝ)
        ≤ ((Q.image f).biUnion (fun c => (Q.filter (fun e => f e = c)).image g)).card := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ c ∈ Q.image f, (((Q.filter (fun e => f e = c)).image g).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ Q.image f, (ρ / ρ' + 2) := Finset.sum_le_sum hfib
      _ = (ρ / ρ' + 2) * (Q.image f).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  calc ((Q.image f').card : ℝ) ≤ 3 * (Q.image g).card := h1
    _ ≤ 3 * ((ρ / ρ' + 2) * (Q.image f).card) := by linarith
    _ = 3 * (ρ / ρ' + 2) * (Q.image f).card := by ring

/-- Unit vectors: `cellCount Q ρ' ≤ 12 (ρ / ρ' + 2) cellCount Q ρ`. -/
theorem cellCount_circle (Q : Finset E2) (hQ : ∀ e ∈ Q, ‖e‖ = 1) {ρ ρ' : ℝ} (hρ' : 0 < ρ')
    (hρ : 0 < ρ) : (cellCount Q ρ' : ℝ) ≤ 12 * (ρ / ρ' + 2) * cellCount Q ρ := by
  classical
  set Q₁ := Q.filter (fun e => |e 0| ≤ |e 1| ∧ 0 < e 1) with hQ₁
  set Q₂ := Q.filter (fun e => |e 0| ≤ |e 1| ∧ e 1 < 0) with hQ₂
  set Q₃ := Q.filter (fun e => |e 1| ≤ |e 0| ∧ 0 < e 0) with hQ₃
  set Q₄ := Q.filter (fun e => |e 1| ≤ |e 0| ∧ e 0 < 0) with hQ₄
  have hcover : Q ⊆ Q₁ ∪ Q₂ ∪ Q₃ ∪ Q₄ := by
    intro e he
    have hu := unit_coords (hQ e he)
    simp only [hQ₁, hQ₂, hQ₃, hQ₄, Finset.mem_union, Finset.mem_filter]
    rcases le_total |e 0| |e 1| with h | h
    · rcases lt_trichotomy (e 1) 0 with h1 | h1 | h1
      · exact Or.inl (Or.inl (Or.inr ⟨he, h, h1⟩))
      · exfalso
        rw [h1, abs_zero] at h
        have h0 : e 0 = 0 := abs_nonpos_iff.mp h
        rw [h0, h1] at hu
        norm_num at hu
      · exact Or.inl (Or.inl (Or.inl ⟨he, h, h1⟩))
    · rcases lt_trichotomy (e 0) 0 with h1 | h1 | h1
      · exact Or.inr ⟨he, h, h1⟩
      · exfalso
        rw [h1, abs_zero] at h
        have h0 : e 1 = 0 := abs_nonpos_iff.mp h
        rw [h0, h1] at hu
        norm_num at hu
      · exact Or.inl (Or.inr ⟨he, h, h1⟩)
  -- each piece
  have hsteep : ∀ Q' : Finset E2, Q' ⊆ Q →
      (∀ e ∈ Q', ∀ e' ∈ Q', |e 1 - e' 1| ≤ |e 0 - e' 0|) →
      ((Q'.image (cellOf ρ')).card : ℝ) ≤ 3 * (ρ / ρ' + 2) * cellCount Q ρ := by
    intro Q' hQ' hlip
    have h := piece_count Q' (fun e => e 0) (fun e => e 1) hlip hρ' hρ
    have hsub : ((Q'.image (cellOf ρ)).card : ℝ) ≤ cellCount Q ρ := by
      unfold cellCount
      exact_mod_cast Finset.card_le_card (Finset.image_subset_image hQ')
    have hpos : 0 ≤ 3 * (ρ / ρ' + 2) := by positivity
    calc ((Q'.image (cellOf ρ')).card : ℝ)
        ≤ 3 * (ρ / ρ' + 2) * (Q'.image (cellOf ρ)).card := h
      _ ≤ 3 * (ρ / ρ' + 2) * cellCount Q ρ := mul_le_mul_of_nonneg_left hsub hpos
  have hflat : ∀ Q' : Finset E2, Q' ⊆ Q →
      (∀ e ∈ Q', ∀ e' ∈ Q', |e 0 - e' 0| ≤ |e 1 - e' 1|) →
      ((Q'.image (cellOf ρ')).card : ℝ) ≤ 3 * (ρ / ρ' + 2) * cellCount Q ρ := by
    intro Q' hQ' hlip
    have h := piece_count Q' (fun e => e 1) (fun e => e 0) hlip hρ' hρ
    have hswap : ∀ σ : ℝ, (Q'.image (fun e : E2 => (⌊e 1 / σ⌋, ⌊e 0 / σ⌋))).card =
        (Q'.image (cellOf σ)).card := by
      intro σ
      have : Q'.image (fun e : E2 => (⌊e 1 / σ⌋, ⌊e 0 / σ⌋)) =
          (Q'.image (cellOf σ)).image Prod.swap := by
        rw [Finset.image_image]; rfl
      rw [this, Finset.card_image_of_injective _ Prod.swap_injective]
    rw [hswap, hswap] at h
    have hsub : ((Q'.image (cellOf ρ)).card : ℝ) ≤ cellCount Q ρ := by
      unfold cellCount
      exact_mod_cast Finset.card_le_card (Finset.image_subset_image hQ')
    have hpos : 0 ≤ 3 * (ρ / ρ' + 2) := by positivity
    calc ((Q'.image (cellOf ρ')).card : ℝ)
        ≤ 3 * (ρ / ρ' + 2) * (Q'.image (cellOf ρ)).card := h
      _ ≤ 3 * (ρ / ρ' + 2) * cellCount Q ρ := mul_le_mul_of_nonneg_left hsub hpos
  have h1 := hsteep Q₁ (Finset.filter_subset _ _) (by
    intro e he e' he'
    obtain ⟨heQ, ha, hb⟩ := Finset.mem_filter.mp he
    obtain ⟨heQ', ha', hb'⟩ := Finset.mem_filter.mp he'
    exact coord_lip (unit_coords (hQ e heQ)) (unit_coords (hQ e' heQ')) ha ha'
      (mul_pos hb hb'))
  have h2 := hsteep Q₂ (Finset.filter_subset _ _) (by
    intro e he e' he'
    obtain ⟨heQ, ha, hb⟩ := Finset.mem_filter.mp he
    obtain ⟨heQ', ha', hb'⟩ := Finset.mem_filter.mp he'
    exact coord_lip (unit_coords (hQ e heQ)) (unit_coords (hQ e' heQ')) ha ha'
      (mul_pos_of_neg_of_neg hb hb'))
  have h3 := hflat Q₃ (Finset.filter_subset _ _) (by
    intro e he e' he'
    obtain ⟨heQ, ha, hb⟩ := Finset.mem_filter.mp he
    obtain ⟨heQ', ha', hb'⟩ := Finset.mem_filter.mp he'
    have hu := unit_coords (hQ e heQ)
    have hu' := unit_coords (hQ e' heQ')
    exact coord_lip (a := e 1) (b := e 0) (a' := e' 1) (b' := e' 0) (by linarith)
      (by linarith) ha ha' (mul_pos hb hb'))
  have h4 := hflat Q₄ (Finset.filter_subset _ _) (by
    intro e he e' he'
    obtain ⟨heQ, ha, hb⟩ := Finset.mem_filter.mp he
    obtain ⟨heQ', ha', hb'⟩ := Finset.mem_filter.mp he'
    have hu := unit_coords (hQ e heQ)
    have hu' := unit_coords (hQ e' heQ')
    exact coord_lip (a := e 1) (b := e 0) (a' := e' 1) (b' := e' 0) (by linarith)
      (by linarith) ha ha' (mul_pos_of_neg_of_neg hb hb'))
  have himg : Q.image (cellOf ρ') ⊆
      Q₁.image (cellOf ρ') ∪ Q₂.image (cellOf ρ') ∪ Q₃.image (cellOf ρ') ∪
        Q₄.image (cellOf ρ') := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
    have := hcover he
    simp only [Finset.mem_union] at this ⊢
    rcases this with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl (Finset.mem_image_of_mem _ h)))
    · exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ h)))
    · exact Or.inl (Or.inr (Finset.mem_image_of_mem _ h))
    · exact Or.inr (Finset.mem_image_of_mem _ h)
  have hcard : (cellCount Q ρ' : ℝ) ≤ (Q₁.image (cellOf ρ')).card +
      (Q₂.image (cellOf ρ')).card + (Q₃.image (cellOf ρ')).card +
        (Q₄.image (cellOf ρ')).card := by
    unfold cellCount
    have := Finset.card_le_card himg
    have u1 := Finset.card_union_le (Q₁.image (cellOf ρ') ∪ Q₂.image (cellOf ρ') ∪
      Q₃.image (cellOf ρ')) (Q₄.image (cellOf ρ'))
    have u2 := Finset.card_union_le (Q₁.image (cellOf ρ') ∪ Q₂.image (cellOf ρ'))
      (Q₃.image (cellOf ρ'))
    have u3 := Finset.card_union_le (Q₁.image (cellOf ρ')) (Q₂.image (cellOf ρ'))
    have : (Q.image (cellOf ρ')).card ≤ (Q₁.image (cellOf ρ')).card +
        (Q₂.image (cellOf ρ')).card + (Q₃.image (cellOf ρ')).card +
          (Q₄.image (cellOf ρ')).card := by omega
    exact_mod_cast this
  linarith

/-- `F i ≤ F j + log_B 4` for `i ≤ j`. -/
theorem cellProfile_mono' {Q : Finset E2} (hQ : Q.Nonempty) {B : ℝ} (hB : 1 < B) {i j : ℕ}
    (hij : i ≤ j) : cellProfile Q B i ≤ cellProfile Q B j + Real.logb B 4 := by
  have hB0 : 0 < B := by linarith
  have hρi : 0 < B ^ (-(i : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hρj : 0 < B ^ (-(j : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hle : B ^ (-(j : ℝ)) ≤ B ^ (-(i : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB.le (by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith)
  have h := cellCount_coarse_le Q hρj hle
  have hpos_i : (0 : ℝ) < cellCount Q (B ^ (-(i : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  have hpos_j : (0 : ℝ) < cellCount Q (B ^ (-(j : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  have h' : (cellCount Q (B ^ (-(i : ℝ))) : ℝ) ≤ 4 * B ^ (0 : ℝ) *
      cellCount Q (B ^ (-(j : ℝ))) := by rw [Real.rpow_zero, mul_one]; exact h
  have := logb_le_of_le_mul_rpow hB hpos_i hpos_j (by norm_num) h'
  unfold cellProfile
  linarith

/-- Unit vectors: `F j - F i ≤ (j - i) + log_B 36` for `i ≤ j`. -/
theorem cellProfile_circle_lip {Q : Finset E2} (hQ : Q.Nonempty) (hQ1 : ∀ e ∈ Q, ‖e‖ = 1)
    {B : ℝ} (hB : 1 < B) {i j : ℕ} (hij : i ≤ j) :
    cellProfile Q B j - cellProfile Q B i ≤ ((j : ℝ) - i) + Real.logb B 36 := by
  have hB0 : 0 < B := by linarith
  have hρi : 0 < B ^ (-(i : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hρj : 0 < B ^ (-(j : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have h := cellCount_circle Q hQ1 hρj hρi
  have hratio : B ^ (-(i : ℝ)) / B ^ (-(j : ℝ)) = B ^ ((j : ℝ) - i) := by
    rw [← Real.rpow_sub hB0]; ring_nf
  rw [hratio] at h
  have hge1 : 1 ≤ B ^ ((j : ℝ) - i) := Real.one_le_rpow hB.le (by
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith)
  have hpos_i : (0 : ℝ) < cellCount Q (B ^ (-(i : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  have hpos_j : (0 : ℝ) < cellCount Q (B ^ (-(j : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  have h' : (cellCount Q (B ^ (-(j : ℝ))) : ℝ) ≤ 36 * B ^ ((j : ℝ) - i) *
      cellCount Q (B ^ (-(i : ℝ))) := by
    refine h.trans ?_
    have : 12 * (B ^ ((j : ℝ) - i) + 2) ≤ 36 * B ^ ((j : ℝ) - i) := by linarith
    exact mul_le_mul_of_nonneg_right this hpos_i.le
  have := logb_le_of_le_mul_rpow hB hpos_j hpos_i (by norm_num) h'
  unfold cellProfile
  linarith

/-- `F t ≥ α - β` if `#Q ≥ B ^ α` and every `2 B ^ (-t)`-ball around a point of `Q` holds at
most `B ^ β` points. -/
theorem cellProfile_ge_of_balls {Q : Finset E2} (hQ : Q.Nonempty) {B : ℝ} (hB : 1 < B)
    (t : ℕ) {α β : ℝ} (hcard : B ^ α ≤ (Q.card : ℝ))
    (hball : ∀ x ∈ Q, ((Q.filter (fun z => dist z x ≤ 2 * B ^ (-(t : ℝ)))).card : ℝ) ≤
      B ^ β) :
    α - β ≤ cellProfile Q B t := by
  have hB0 : 0 < B := by linarith
  have hρ : 0 < B ^ (-(t : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hcnt := card_le_cellCount_mul Q hρ hball
  have hpos : (0 : ℝ) < cellCount Q (B ^ (-(t : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  have h' : B ^ α ≤ 1 * B ^ β * cellCount Q (B ^ (-(t : ℝ))) := by
    rw [one_mul]; exact hcard.trans hcnt
  have := logb_le_of_le_mul_rpow hB (Real.rpow_pos_of_pos hB0 α) hpos one_pos h'
  rw [Real.logb_rpow hB0 (by linarith), Real.logb_one] at this
  unfold cellProfile
  linarith

/-- `F t ≤ log_B #Q`. -/
theorem cellProfile_le_card {Q : Finset E2} (hQ : Q.Nonempty) {B : ℝ} (hB : 1 < B) (t : ℕ) :
    cellProfile Q B t ≤ Real.logb B Q.card := by
  have hpos : (0 : ℝ) < cellCount Q (B ^ (-(t : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  unfold cellProfile
  apply Real.logb_le_logb_of_le hB hpos
  unfold cellCount
  exact_mod_cast Finset.card_image_le

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
