-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.RichClass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.RichClassParts
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.RichNumerics

/-!
# A rich line class with 1/2-Frostman, well-joined pins (`half_rich_class`)

From `HalfData r ε₀ η P D` (a failed bush estimate at `s = 1/2`) and small `r`, with
`κ = ε₀ + η`: a line `ℓ₀` (through `p₀`, unit normal `n`) and pins `A ⊆ P` within `9 r` of
`ℓ₀`, along-`r`-separated, `1/2`-Frostman along `ℓ₀` with constant `r ^ (-100 κ)`, with
`#A ≥ r ^ (-1/2 + 100 κ)`, each joined (on a bush line, `26 r`) to at least
`r ^ (-1 + 100 κ)` pins at distance `≥ r ^ (20 κ)`.

Construction: the classes of `HalfData.classes`; far pairs (distance `≥ d₀ = r ^ (20 κ)`);
good points (many far pairs, hence by `HalfData.good_degree` large far degree); class weights
`w j` = good far pairs of the class; `class_selection` gives a class `j₀` with
`w j₀ ≥ W / (8 #J₀)` and per-scale close-pair bounds; its good pins `H` have
`(2 r ^ (-η) #H) ^ 2 ≥ w j₀` and pair counts `≲ (r 2 ^ k) ^ (1/2) #H ^ 2`; `two_ends_frostman`
and `along_separated_prune` finish.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open SP

theorem farPairs_mem {D : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {d₀ : ℝ}
    {qq : (E2 × E2) × (E2 × E2)} (h : qq ∈ farPairs D cls d₀) :
    qq.1 ∈ D ∧ qq.2 ∈ D ∧ cls qq.1 = cls qq.2 ∧ d₀ ≤ dist qq.1.1 qq.2.1 := by
  unfold farPairs sameClass at h
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

set_option maxHeartbeats 8000000 in
theorem half_rich_class (ε₀ η : ℝ) (hε₀ : 0 < ε₀) (hη : 0 < η) (hε₀1 : ε₀ ≤ 1 / 1000)
    (hη1 : η ≤ 1 / 1000) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r ≤ r₁ → ∀ (P : Finset E2) (D : Finset (E2 × E2)),
      HalfData r ε₀ η P D →
      ∃ (p₀ n : E2) (A : Finset E2), ‖n‖ = 1 ∧ ‖p₀‖ ≤ 4 ∧ A ⊆ P ∧
        (∀ p ∈ A, |SP.acrossCoord n p₀ p| ≤ 9 * r) ∧
        (∀ p ∈ A, ∀ p' ∈ A, p ≠ p' → r ≤ |SP.alongCoord n p₀ p - SP.alongCoord n p₀ p'|) ∧
        (∀ x ρ : ℝ, r ≤ ρ → ((A.filter (fun p => |SP.alongCoord n p₀ p - x| ≤ ρ)).card : ℝ) ≤
            r ^ (-(100 * (ε₀ + η))) * ρ ^ (1 / 2 : ℝ) * (A.card : ℝ)) ∧
        r ^ (-(1 / 2) + 100 * (ε₀ + η)) ≤ (A.card : ℝ) ∧
        ∀ p ∈ A, r ^ (-1 + 100 * (ε₀ + η)) ≤
          ((P.filter (fun q => r ^ (20 * (ε₀ + η)) ≤ dist q p ∧
            ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r)).card : ℝ) := by
  classical
  obtain ⟨r₁, hr₁, hnum⟩ := rich_numerics hε₀ hη hε₀1 hη1
  refine ⟨r₁, hr₁, ?_⟩
  intro r hr hrr P D h
  obtain ⟨hF1, hF2, hF3, hF4, hF5, hF6⟩ := hnum r hr hrr
  obtain ⟨J₀, cls, hJD, hJcard, hclsJ, hgeo, hsame, hclose⟩ := h.classes hF1 hη
  have hDP : ∀ q ∈ D, q.1 ∈ P := fun q hq => (h.D_mem q hq).1
  have hcls4 : ∀ q ∈ D, ‖(cls q).1‖ ≤ 4 ∧ ‖(cls q).2‖ = 1 := fun q hq =>
    ⟨h.P_norm _ (hDP _ (hJD (hclsJ q hq))), (h.D_mem _ (hJD (hclsJ q hq))).2⟩
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr h.P_ne
  -- the number of pins
  have hPup : (P.card : ℝ) ≤ r ^ (-η) * (8 / r) := by
    have hk := h.P_kt 0 8 (by linarith only [hF1])
    have hfull : P.filter (fun p => dist p 0 ≤ 8) = P := by
      apply Finset.filter_true_of_mem
      intro p hp
      rw [dist_zero_right]
      linarith only [h.P_norm p hp]
    rwa [hfull] at hk
  -- far pairs
  set d₀ := r ^ (20 * (ε₀ + η)) with hd₀
  have hd₀52 : 52 * r ≤ d₀ := hF2
  have hd₀r : r ≤ d₀ := by linarith only [hd₀52, hr]
  set F := farPairs D cls d₀ with hFdef
  have hFlow : 3 / 4 * r ^ (4 * η + ε₀ - 2) ≤ (F.card : ℝ) := by
    have heq : (sameClass D cls).filter (fun qq => ¬ d₀ ≤ dist qq.1.1 qq.2.1) =
        (sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < d₀) := by
      ext qq; simp only [Finset.mem_filter, not_le]
    have hsplit : ((sameClass D cls).filter (fun qq => d₀ ≤ dist qq.1.1 qq.2.1)).card +
        ((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < d₀)).card =
        (sameClass D cls).card := by
      rw [← heq]; exact Finset.card_filter_add_card_filter_not _
    have hcl := hclose d₀ hd₀r
    have hFeq : F = (sameClass D cls).filter (fun qq => d₀ ≤ dist qq.1.1 qq.2.1) := rfl
    have hsR : (F.card : ℝ) + (((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < d₀)).card : ℝ) =
        ((sameClass D cls).card : ℝ) := by
      rw [hFeq]; exact_mod_cast hsplit
    linarith only [hsR, hcl, hF3, hsame]
  have hFpos : (0 : ℝ) < F.card :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hr _)) hFlow
  -- good points and good far pairs
  set τ := (F.card : ℝ) / (4 * (P.card : ℝ)) with hτ
  set Good := P.filter (fun p => τ ≤ (farCount D cls d₀ p : ℝ)) with hGood
  set GF := F.filter (fun qq => qq.1.1 ∈ Good ∧ qq.2.1 ∈ Good) with hGFdef
  have hGF : (F.card : ℝ) / 2 ≤ (GF.card : ℝ) := far_good_pairs D cls d₀ P hDP h.P_ne
  have hGFmem : ∀ qq ∈ GF, qq.1 ∈ D ∧ qq.2 ∈ D ∧ cls qq.1 = cls qq.2 ∧ qq.1.1 ∈ Good ∧
      qq.2.1 ∈ Good := by
    intro qq hqq
    have hqq' := Finset.mem_filter.mp hqq
    have hf := farPairs_mem hqq'.1
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hqq'.2.1, hqq'.2.2⟩
  -- class weights
  set w : E2 × E2 → ℝ := fun j => ((GF.filter (fun qq => cls qq.1 = j)).card : ℝ) with hw
  set W : ℝ := (GF.card : ℝ) with hWdef
  have hWsum : W = ∑ j ∈ J₀, w j := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun qq => cls qq.1) (s := GF) (t := J₀)
      (fun qq hqq => hclsJ _ (hGFmem qq hqq).1)
    have h2 : ((GF.card : ℕ) : ℝ) =
        ∑ j ∈ J₀, (((GF.filter (fun qq => cls qq.1 = j)).card : ℕ) : ℝ) := by
      exact_mod_cast this
    exact h2
  have hWlow : 3 / 8 * r ^ (4 * η + ε₀ - 2) ≤ W := by rw [hWdef]; linarith only [hGF, hFlow]
  have hWpos : 0 < W :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hr _)) hWlow
  set n2 : E2 × E2 → ℝ := fun j => ((D.filter (fun q => cls q = j)).card : ℝ) ^ 2 with hn2
  have hn2sum : ∑ j ∈ J₀, n2 j = ((sameClass D cls).card : ℝ) := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := fun qq => cls qq.1) (s := sameClass D cls)
      (t := J₀) (fun qq hqq => by
        unfold sameClass at hqq
        exact hclsJ _ (Finset.mem_product.mp (Finset.mem_filter.mp hqq).1).1)
    have h2 : ∀ j ∈ J₀, ((sameClass D cls).filter (fun qq => cls qq.1 = j)).card =
        (D.filter (fun q => cls q = j)).card ^ 2 := by
      intro j _
      rw [sq, ← Finset.card_product]
      congr 1
      ext qq
      unfold sameClass
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h2, h3.symm.trans h4⟩
      · rintro ⟨⟨h1, h4⟩, h2, h5⟩; exact ⟨⟨⟨h1, h2⟩, h4.trans h5.symm⟩, h4⟩
    rw [Finset.sum_congr rfl h2] at h1
    rw [h1]; push_cast; rfl
  have hn2pos : 0 < ∑ j ∈ J₀, n2 j := by
    rw [hn2sum]; exact lt_of_lt_of_le (Real.rpow_pos_of_pos hr _) hsame
  have hJpos : (0 : ℝ) < J₀.card := by
    have hne : J₀.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty] at hn2pos
      exact lt_irrefl _ hn2pos
    exact_mod_cast Finset.card_pos.mpr hne
  set ρ₀ : ℝ := W / (8 * ∑ j ∈ J₀, n2 j) with hρ₀
  set c₀ : ℝ := (∑ j ∈ J₀, n2 j) / (J₀.card : ℝ) with hc₀
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀]; exact div_pos hWpos (mul_pos (by norm_num) hn2pos)
  have hρc : ρ₀ * c₀ = W / (8 * (J₀.card : ℝ)) := by
    rw [hρ₀, hc₀, div_mul_div_comm,
      div_eq_div_iff (mul_pos (mul_pos (by norm_num) hn2pos) hJpos).ne'
        (mul_pos (by norm_num) hJpos).ne']
    ring
  -- scales
  have hexL : ∃ L : ℕ, 64 ≤ r * 2 ^ L := by
    obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (64 / r) (by norm_num : (1 : ℝ) < 2)
    exact ⟨L, by rw [div_lt_iff₀ hr] at hL; linarith only [hL]⟩
  set L := Nat.find hexL with hLdef
  have hL64 : 64 ≤ r * 2 ^ L := Nat.find_spec hexL
  have hL128 : (2 : ℝ) ^ L ≤ 128 / r := by
    rw [le_div_iff₀ hr]
    by_cases hL0 : L = 0
    · rw [hL0]; norm_num; linarith only [hF1]
    · have hmin := Nat.find_min hexL (Nat.sub_lt (Nat.pos_of_ne_zero hL0) one_pos)
      rw [← hLdef] at hmin
      push Not at hmin
      have e : L - 1 + 1 = L := Nat.sub_add_cancel (Nat.pos_of_ne_zero hL0)
      have h2 : (2 : ℝ) ^ L = 2 * 2 ^ (L - 1) := by
        rw [← pow_succ']; rw [e]
      rw [h2]; linarith only [hmin]
  set cl : E2 × E2 → ℕ → ℝ := fun j k =>
    (((sameClass D cls).filter (fun qq => cls qq.1 = j ∧
      dist qq.1.1 qq.2.1 < 20 * (r * 2 ^ k))).card : ℝ) with hcl
  set X : ℕ → ℝ := fun k => 10 ^ 6 * r ^ (-2 - 4 * η) * (20 * (r * 2 ^ k)) ^ (1 / 2 : ℝ) with hX
  have hXsum : ∀ k ≤ L, ∑ j ∈ J₀, cl j k ≤ X k := by
    intro k _
    have h1 := Finset.card_eq_sum_card_fiberwise (f := fun qq => cls qq.1)
      (s := (sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < 20 * (r * 2 ^ k)))
      (t := J₀) (fun qq hqq => by
        have hqq' := Finset.mem_filter.mp hqq
        unfold sameClass at hqq'
        exact hclsJ _ (Finset.mem_product.mp (Finset.mem_filter.mp hqq'.1).1).1)
    have h2 : ∀ j ∈ J₀, (((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 <
        20 * (r * 2 ^ k))).filter (fun qq => cls qq.1 = j)).card =
        ((sameClass D cls).filter (fun qq => cls qq.1 = j ∧
          dist qq.1.1 qq.2.1 < 20 * (r * 2 ^ k))).card := by
      intro j _
      rw [Finset.filter_filter]
      congr 1
      ext qq
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
      · rintro ⟨h1, h3, h2⟩; exact ⟨h1, h2, h3⟩
    rw [Finset.sum_congr rfl h2] at h1
    have hd : r ≤ 20 * (r * 2 ^ k) := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hm := mul_le_mul_of_nonneg_left this hr.le
      linarith only [hm, hr]
    have h3 := hclose (20 * (r * 2 ^ k)) hd
    calc ∑ j ∈ J₀, cl j k = (((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 <
          20 * (r * 2 ^ k))).card : ℝ) := by
          simp only [hcl]; exact_mod_cast h1.symm
      _ ≤ X k := h3
  -- the selection
  have hsel := class_selection J₀ w (fun j => n2 j + c₀) cl X L (ρ := ρ₀) (W := W)
    (fun j _ => Nat.cast_nonneg _) (fun j _ k => Nat.cast_nonneg _) hWsum hWpos hXsum
    hρ₀pos.le (fun j _ => add_nonneg (sq_nonneg _) (div_nonneg hn2pos.le (Nat.cast_nonneg _)))
    (by
      have e : ∑ j ∈ J₀, (n2 j + c₀) = 2 * ∑ j ∈ J₀, n2 j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hc₀,
          mul_div_cancel₀ _ hJpos.ne']
        ring
      have e2 : ρ₀ * (2 * ∑ j ∈ J₀, n2 j) = W / 4 := by
        rw [hρ₀, div_mul_eq_mul_div, div_eq_div_iff (mul_pos (by norm_num) hn2pos).ne'
          (by norm_num)]
        ring
      show ρ₀ * ∑ j ∈ J₀, (n2 j + c₀) ≤ W / 4
      rw [e, e2])
  obtain ⟨j₀, hj₀, hwj₀pos, hρn2, hclj⟩ := hsel
  have hwrich : W / (8 * (J₀.card : ℝ)) ≤ w j₀ := by
    have hn2nn : 0 ≤ n2 j₀ := sq_nonneg _
    have h1 : ρ₀ * c₀ ≤ ρ₀ * (n2 j₀ + c₀) :=
      mul_le_mul_of_nonneg_left (by linarith only [hn2nn]) hρ₀pos.le
    have h2 : ρ₀ * (n2 j₀ + c₀) ≤ w j₀ := hρn2
    linarith only [h1, h2, hρc]
  -- the line and the good pins of the class
  have hj₀D : j₀ ∈ D := hJD hj₀
  have hnu : ‖j₀.2‖ = 1 := (h.D_mem j₀ hj₀D).2
  have hp₀4 : ‖j₀.1‖ ≤ 4 := h.P_norm _ (hDP _ hj₀D)
  set H := (pinsOf D cls j₀).filter (fun p => p ∈ Good) with hHdef
  have hHpins : H ⊆ pinsOf D cls j₀ := Finset.filter_subset _ _
  have hpinsP : pinsOf D cls j₀ ⊆ P := by
    intro p hp; obtain ⟨e, he, _⟩ := mem_pinsOf.mp hp; exact hDP _ he
  have hHP : H ⊆ P := hHpins.trans hpinsP
  have hnearH : ∀ p ∈ pinsOf D cls j₀, |acrossCoord j₀.2 j₀.1 p| < 9 * r := by
    intro p hp
    obtain ⟨e, he, hce⟩ := mem_pinsOf.mp hp
    have hg := (hgeo _ he).1
    rw [hce] at hg
    exact hg
  -- the weight of the class is at most the square of the labels at good pins
  have hwH : w j₀ ≤ (2 * r ^ (-η) * (H.card : ℝ)) ^ 2 := by
    set LH := D.filter (fun q => cls q = j₀ ∧ q.1 ∈ H) with hLH
    have hsub : GF.filter (fun qq => cls qq.1 = j₀) ⊆ LH ×ˢ LH := by
      intro qq hqq
      have hqq' := Finset.mem_filter.mp hqq
      have hm := hGFmem qq hqq'.1
      have h1H : qq.1.1 ∈ H := Finset.mem_filter.mpr
        ⟨mem_pinsOf.mpr ⟨qq.1.2, by simpa using hm.1, by simpa using hqq'.2⟩, hm.2.2.2.1⟩
      have h2H : qq.2.1 ∈ H := Finset.mem_filter.mpr
        ⟨mem_pinsOf.mpr ⟨qq.2.2, by simpa using hm.2.1, by
          have := hm.2.2.1; rw [hqq'.2] at this; simpa using this.symm⟩, hm.2.2.2.2⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hm.1, hqq'.2, h1H⟩,
        Finset.mem_filter.mpr ⟨hm.2.1, by rw [← hm.2.2.1]; exact hqq'.2, h2H⟩⟩
    have hLHc := class_labels_at_le hr h.D_kt hgeo hnu hHP
    have h1 : w j₀ ≤ ((LH ×ˢ LH).card : ℝ) := by
      simp only [hw]; exact_mod_cast Finset.card_le_card hsub
    rw [Finset.card_product] at h1
    push_cast at h1
    have hLH0 : (0 : ℝ) ≤ LH.card := Nat.cast_nonneg _
    calc w j₀ ≤ (LH.card : ℝ) * LH.card := h1
      _ ≤ (2 * r ^ (-η) * (H.card : ℝ)) * (2 * r ^ (-η) * (H.card : ℝ)) :=
          mul_le_mul hLHc hLHc hLH0 (hLH0.trans hLHc)
      _ = _ := by ring
  -- pair counts of `H` along the line
  set X₀ : E2 → ℝ := fun p => alongCoord j₀.2 j₀.1 p with hX₀
  have hlab : ∀ p ∈ pinsOf D cls j₀, ∃ e, (p, e) ∈ D ∧ cls (p, e) = j₀ :=
    fun p hp => mem_pinsOf.mp hp
  choose! lab hlabD hlabc using hlab
  set B : ℝ := 4 * ((L : ℝ) + 1) * (4 * r ^ (-(2 * η)) / W) * (10 ^ 6 * r ^ (-2 - 4 * η)) *
    (20 : ℝ) ^ (1 / 2 : ℝ) with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_add_one_pos L))
      (div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hr _)) hWpos))
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos hr _))) (Real.rpow_pos_of_pos (by norm_num) _)
  have hpairs : ∀ k ≤ L, (((H ×ˢ H).filter (fun q => |X₀ q.1 - X₀ q.2| ≤ r * 2 ^ k)).card : ℝ) ≤
      B * (r * 2 ^ k) ^ (1 / 2 : ℝ) * (H.card : ℝ) ^ 2 := by
    intro k hk
    have hsub : ((H ×ˢ H).filter (fun q => |X₀ q.1 - X₀ q.2| ≤ r * 2 ^ k)).image
        (fun pp => ((pp.1, lab pp.1), (pp.2, lab pp.2))) ⊆
        (sameClass D cls).filter (fun qq => cls qq.1 = j₀ ∧
          dist qq.1.1 qq.2.1 < 20 * (r * 2 ^ k)) := by
      intro qq hqq
      obtain ⟨pp, hpp, rfl⟩ := Finset.mem_image.mp hqq
      have hpp' := Finset.mem_filter.mp hpp
      have h1 := hHpins (Finset.mem_product.mp hpp'.1).1
      have h2 := hHpins (Finset.mem_product.mp hpp'.1).2
      refine Finset.mem_filter.mpr ⟨?_, hlabc _ h1, ?_⟩
      · unfold sameClass
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hlabD _ h1, hlabD _ h2⟩,
          by rw [hlabc _ h1, hlabc _ h2]⟩
      · show dist pp.1 pp.2 < 20 * (r * 2 ^ k)
        have halong : |inner ℝ (pp.1 - pp.2) (perp j₀.2)| ≤ r * 2 ^ k := by
          have := hpp'.2; simp only [hX₀] at this; rwa [alongCoord_sub] at this
        have hacross : |inner ℝ (pp.1 - pp.2) j₀.2| ≤ 18 * r := by
          rw [← acrossCoord_sub]
          calc |acrossCoord j₀.2 j₀.1 pp.1 - acrossCoord j₀.2 j₀.1 pp.2|
              ≤ |acrossCoord j₀.2 j₀.1 pp.1| + |acrossCoord j₀.2 j₀.1 pp.2| := abs_sub _ _
            _ ≤ 18 * r := by linarith only [hnearH _ h1, hnearH _ h2]
        have hframe := inner_frame hnu (pp.1 - pp.2) (pp.1 - pp.2)
        rw [real_inner_self_eq_norm_sq] at hframe
        have h2k : r ≤ r * 2 ^ k := by
          have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
          have hm := mul_le_mul_of_nonneg_left this hr.le
          linarith only [hm]
        have hsq : ‖pp.1 - pp.2‖ ^ 2 < (20 * (r * 2 ^ k)) ^ 2 := by
          rw [hframe]
          have ha2 : inner ℝ (pp.1 - pp.2) (perp j₀.2) ^ 2 ≤ (r * 2 ^ k) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) halong 2
          have hb2 : inner ℝ (pp.1 - pp.2) j₀.2 ^ 2 ≤ (18 * (r * 2 ^ k)) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hacross.trans (by linarith only [h2k])) 2
          have hX2 : 0 < (r * 2 ^ k) ^ 2 := pow_pos (mul_pos hr (pow_pos two_pos k)) 2
          have e18 : (18 * (r * 2 ^ k)) ^ 2 = 324 * (r * 2 ^ k) ^ 2 := by ring
          have e20 : (20 * (r * 2 ^ k)) ^ 2 = 400 * (r * 2 ^ k) ^ 2 := by ring
          rw [e18] at hb2
          rw [e20]
          linarith only [ha2, hb2, hX2]
        rw [dist_eq_norm]
        exact (pow_lt_pow_iff_left₀ (norm_nonneg _)
          (mul_pos (by norm_num) (mul_pos hr (pow_pos two_pos k))).le (by norm_num)).mp hsq
    have hinj : Set.InjOn (fun pp : E2 × E2 => ((pp.1, lab pp.1), (pp.2, lab pp.2)))
        ↑((H ×ˢ H).filter (fun q => |X₀ q.1 - X₀ q.2| ≤ r * 2 ^ k)) := by
      intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1.1 hab.2.1
    have hcard : (((H ×ˢ H).filter (fun q => |X₀ q.1 - X₀ q.2| ≤ r * 2 ^ k)).card : ℝ) ≤
        cl j₀ k := by
      simp only [hcl]
      rw [← Finset.card_image_of_injOn hinj]
      exact_mod_cast Finset.card_le_card hsub
    refine hcard.trans ((hclj k hk).trans ?_)
    have hXk : X k = 10 ^ 6 * r ^ (-2 - 4 * η) * ((20 : ℝ) ^ (1 / 2 : ℝ) *
        (r * 2 ^ k) ^ (1 / 2 : ℝ)) := by
      simp only [hX]
      rw [Real.mul_rpow (x := (20 : ℝ)) (y := r * 2 ^ k) (z := 1 / 2) (by norm_num)
        (mul_pos hr (pow_pos two_pos k)).le]
    rw [hXk]
    have hw2 : w j₀ / W ≤ 4 * r ^ (-(2 * η)) * (H.card : ℝ) ^ 2 / W := by
      apply div_le_div_of_nonneg_right _ hWpos.le
      have e : (2 * r ^ (-η) * (H.card : ℝ)) ^ 2 = 4 * r ^ (-(2 * η)) * (H.card : ℝ) ^ 2 := by
        have : (r ^ (-η)) ^ 2 = r ^ (-(2 * η)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
        rw [mul_pow, mul_pow, this]; ring
      rw [← e]; exact hwH
    have hnn : 0 ≤ 10 ^ 6 * r ^ (-2 - 4 * η) * ((20 : ℝ) ^ (1 / 2 : ℝ) *
        (r * 2 ^ k) ^ (1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hr.le _))
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (mul_pos hr (pow_pos two_pos k)).le _))
    calc 4 * ((L : ℝ) + 1) * (w j₀ / W) * (10 ^ 6 * r ^ (-2 - 4 * η) *
          ((20 : ℝ) ^ (1 / 2 : ℝ) * (r * 2 ^ k) ^ (1 / 2 : ℝ)))
        ≤ 4 * ((L : ℝ) + 1) * (4 * r ^ (-(2 * η)) * (H.card : ℝ) ^ 2 / W) *
            (10 ^ 6 * r ^ (-2 - 4 * η) * ((20 : ℝ) ^ (1 / 2 : ℝ) * (r * 2 ^ k) ^ (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hw2 (mul_pos (by norm_num) (Nat.cast_add_one_pos L)).le) hnn
      _ = B * (r * 2 ^ k) ^ (1 / 2 : ℝ) * (H.card : ℝ) ^ 2 := by
          rw [hBdef]; ring
  -- prune
  obtain ⟨H', hH'H, hH'card, hwin⟩ := two_ends_frostman H X₀ L hBpos hr
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hpairs
  have hH'P : H' ⊆ P := hH'H.trans hHP
  have hnearH' : ∀ p ∈ H', |acrossCoord j₀.2 j₀.1 p| ≤ 9 * r :=
    fun p hp => (hnearH p (hHpins (hH'H hp))).le
  obtain ⟨A, hAH', hAsep, hAcard⟩ := along_separated_prune hr h.P_kt hnu hH'P hnearH'
  refine ⟨j₀.1, j₀.2, A, hnu, hp₀4, hAH'.trans hH'P, fun p hp => hnearH' p (hAH' hp), hAsep,
    ?_, ?_, ?_⟩
  · -- windows
    intro x ρ hρ
    have hρ0 : 0 ≤ ρ := hr.le.trans hρ
    have hρs : 0 ≤ ρ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hρ0 _
    have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    have hBle : B ≤ 16 * Real.sqrt 20 * 10 ^ 6 * ((L : ℝ) + 1) * (8 / 3) * r ^ (-(10 * η) - ε₀) := by
      rw [hBdef]
      have hWinv : 1 / W ≤ 8 / 3 * r ^ (-(4 * η + ε₀ - 2)) := by
        rw [div_le_iff₀ hWpos]
        have e : r ^ (-(4 * η + ε₀ - 2)) * r ^ (4 * η + ε₀ - 2) = 1 := by
          rw [← Real.rpow_add hr,
            show -(4 * η + ε₀ - 2) + (4 * η + ε₀ - 2) = (0 : ℝ) by ring, Real.rpow_zero]
        have hm := mul_le_mul_of_nonneg_left hWlow
          (le_of_lt (Real.rpow_pos_of_pos hr (-(4 * η + ε₀ - 2))))
        calc (1 : ℝ) = 8 / 3 * (r ^ (-(4 * η + ε₀ - 2)) * (3 / 8 * r ^ (4 * η + ε₀ - 2))) := by
              rw [← e]; ring
          _ ≤ 8 / 3 * (r ^ (-(4 * η + ε₀ - 2)) * W) :=
              mul_le_mul_of_nonneg_left hm (by norm_num)
          _ = 8 / 3 * r ^ (-(4 * η + ε₀ - 2)) * W := by ring
      have e2 : r ^ (-(2 * η)) * r ^ (-2 - 4 * η) * r ^ (-(4 * η + ε₀ - 2)) =
          r ^ (-(10 * η) - ε₀) := by
        rw [← Real.rpow_add hr, ← Real.rpow_add hr]; congr 1; ring
      rw [← Real.sqrt_eq_rpow]
      have hpos1 : 0 ≤ 4 * ((L : ℝ) + 1) * 4 * r ^ (-(2 * η)) * (10 ^ 6 * r ^ (-2 - 4 * η)) *
          Real.sqrt 20 :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          (Nat.cast_add_one_pos L).le) (by norm_num)) (Real.rpow_nonneg hr.le _))
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hr.le _))) (Real.sqrt_nonneg _)
      calc 4 * ((L : ℝ) + 1) * (4 * r ^ (-(2 * η)) / W) * (10 ^ 6 * r ^ (-2 - 4 * η)) *
            Real.sqrt 20
          = (4 * ((L : ℝ) + 1) * 4 * r ^ (-(2 * η)) * (10 ^ 6 * r ^ (-2 - 4 * η)) *
              Real.sqrt 20) * (1 / W) := by ring
        _ ≤ (4 * ((L : ℝ) + 1) * 4 * r ^ (-(2 * η)) * (10 ^ 6 * r ^ (-2 - 4 * η)) *
              Real.sqrt 20) * (8 / 3 * r ^ (-(4 * η + ε₀ - 2))) :=
            mul_le_mul_of_nonneg_left hWinv hpos1
        _ = 16 * Real.sqrt 20 * 10 ^ 6 * ((L : ℝ) + 1) * (8 / 3) *
              (r ^ (-(2 * η)) * r ^ (-2 - 4 * η) * r ^ (-(4 * η + ε₀ - 2))) := by ring
        _ = _ := by rw [e2]
    have hconst : 152 * ((L : ℝ) + 1) * B * r ^ (-η) ≤ r ^ (-(100 * (ε₀ + η))) := by
      refine le_trans ?_ (hF5 L hL128)
      have : 0 ≤ 152 * ((L : ℝ) + 1) := mul_nonneg (by norm_num) (Nat.cast_add_one_pos L).le
      have hrη : 0 ≤ r ^ (-η) := Real.rpow_nonneg hr.le _
      calc 152 * ((L : ℝ) + 1) * B * r ^ (-η) ≤
          152 * ((L : ℝ) + 1) * (16 * Real.sqrt 20 * 10 ^ 6 * ((L : ℝ) + 1) * (8 / 3) *
            r ^ (-(10 * η) - ε₀)) * r ^ (-η) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBle this) hrη
        _ = _ := rfl
    have hsub : A.filter (fun p => |alongCoord j₀.2 j₀.1 p - x| ≤ ρ) ⊆
        H'.filter (fun p => |X₀ p - x| ≤ ρ) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hAH' hp'.1, hp'.2⟩
    have hle1 : ((A.filter (fun p => |alongCoord j₀.2 j₀.1 p - x| ≤ ρ)).card : ℝ) ≤
        ((H'.filter (fun p => |X₀ p - x| ≤ ρ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hrbig : (1 : ℝ) ≤ r ^ (-(100 * (ε₀ + η))) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr (by linarith only [hF1]) (by linarith only [hε₀, hη])
    by_cases hbig : 4 * ρ ≤ r * 2 ^ L
    · have hw := hwin x ρ hρ hbig
      have h4 : (4 * ρ) ^ (1 / 2 : ℝ) = 2 * ρ ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hρ0]
        congr 1
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h4] at hw
      have hHH' : (H.card : ℝ) ≤ 2 * (19 * r ^ (-η) * (A.card : ℝ)) := hH'card.trans (by linarith only [hAcard])
      have hcoef : 0 ≤ 2 * ((L : ℝ) + 1) * B * (2 * ρ ^ (1 / 2 : ℝ)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_add_one_pos L).le) hBpos.le)
          (mul_nonneg (by norm_num) hρs)
      calc ((A.filter (fun p => |alongCoord j₀.2 j₀.1 p - x| ≤ ρ)).card : ℝ)
          ≤ ((H'.filter (fun p => |X₀ p - x| ≤ ρ)).card : ℝ) := hle1
        _ ≤ 2 * ((L : ℝ) + 1) * B * (2 * ρ ^ (1 / 2 : ℝ)) * (H.card : ℝ) := hw
        _ ≤ 2 * ((L : ℝ) + 1) * B * (2 * ρ ^ (1 / 2 : ℝ)) * (2 * (19 * r ^ (-η) * (A.card : ℝ))) :=
            mul_le_mul_of_nonneg_left hHH' hcoef
        _ = (152 * ((L : ℝ) + 1) * B * r ^ (-η)) * (ρ ^ (1 / 2 : ℝ) * (A.card : ℝ)) := by ring
        _ ≤ r ^ (-(100 * (ε₀ + η))) * (ρ ^ (1 / 2 : ℝ) * (A.card : ℝ)) :=
            mul_le_mul_of_nonneg_right hconst (mul_nonneg hρs hA0)
        _ = _ := by ring
    · push Not at hbig
      have hρ16 : 16 ≤ ρ := by linarith only [hbig, hL64]
      have hsq : (4 : ℝ) ≤ ρ ^ (1 / 2 : ℝ) := by
        rw [show (4 : ℝ) = (16 : ℝ) ^ (1 / 2 : ℝ) by
          rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
        exact Real.rpow_le_rpow (by norm_num) hρ16 (by norm_num)
      have hle : ((A.filter (fun p => |alongCoord j₀.2 j₀.1 p - x| ≤ ρ)).card : ℝ) ≤ A.card := by
        exact_mod_cast Finset.card_filter_le _ _
      have h1 : (A.card : ℝ) ≤ ρ ^ (1 / 2 : ℝ) * (A.card : ℝ) := by
        have := mul_le_mul_of_nonneg_right hsq hA0
        linarith only [this, hA0]
      have h2 : ρ ^ (1 / 2 : ℝ) * (A.card : ℝ) ≤
          r ^ (-(100 * (ε₀ + η))) * (ρ ^ (1 / 2 : ℝ) * (A.card : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hrbig (mul_nonneg hρs hA0)
        linarith only [this]
      calc ((A.filter (fun p => |alongCoord j₀.2 j₀.1 p - x| ≤ ρ)).card : ℝ) ≤ A.card := hle
        _ ≤ r ^ (-(100 * (ε₀ + η))) * (ρ ^ (1 / 2 : ℝ) * (A.card : ℝ)) := h1.trans h2
        _ = _ := by ring
  · -- richness
    have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    have hrη : 0 < r ^ (-η) := Real.rpow_pos_of_pos hr _
    have hJinv : r ^ (1 + ε₀) ≤ 1 / (J₀.card : ℝ) := by
      rw [le_div_iff₀ hJpos]
      have e : r ^ (1 + ε₀) * r ^ (-1 - ε₀) = 1 := by
        rw [← Real.rpow_add hr, show (1 + ε₀) + (-1 - ε₀) = (0 : ℝ) by ring, Real.rpow_zero]
      have hp : 0 < r ^ (1 + ε₀) := Real.rpow_pos_of_pos hr _
      have hm := mul_le_mul_of_nonneg_left hJcard.le hp.le
      linarith only [hm, e]
    have hwlow : 3 / 64 * r ^ (4 * η + 2 * ε₀ - 1) ≤ w j₀ := by
      have e : r ^ (4 * η + 2 * ε₀ - 1) = r ^ (4 * η + ε₀ - 2) * r ^ (1 + ε₀) := by
        rw [← Real.rpow_add hr]; congr 1; ring
      calc 3 / 64 * r ^ (4 * η + 2 * ε₀ - 1) = (3 / 8 * r ^ (4 * η + ε₀ - 2)) / 8 * r ^ (1 + ε₀) := by
            rw [e]; ring
        _ ≤ W / 8 * (1 / (J₀.card : ℝ)) := by
            apply mul_le_mul (by linarith only [hWlow]) hJinv (Real.rpow_nonneg hr.le _)
              (div_nonneg hWpos.le (by norm_num))
        _ = W / (8 * (J₀.card : ℝ)) := by rw [div_mul_div_comm, mul_one]
        _ ≤ w j₀ := hwrich
    -- #A ^ 2 ≥ #H ^ 2 r ^ (2 η) / 1444 ≥ w j₀ r ^ (4 η) / 5776
    have hAH : (H.card : ℝ) ≤ 38 * r ^ (-η) * (A.card : ℝ) := by linarith only [hH'card, hAcard]
    have hsqA : r ^ (-1 + 200 * (ε₀ + η)) ≤ (A.card : ℝ) ^ 2 := by
      refine hF4.trans ?_
      have e1 : (2 * r ^ (-η) * (H.card : ℝ)) ^ 2 ≤ (2 * r ^ (-η) * (38 * r ^ (-η) * (A.card : ℝ))) ^ 2 := by
        have h0 : 0 ≤ 2 * r ^ (-η) * (H.card : ℝ) :=
          mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hr.le _)) (Nat.cast_nonneg _)
        exact pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left hAH
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hr.le _))) 2
      have e2 : (2 * r ^ (-η) * (38 * r ^ (-η) * (A.card : ℝ))) ^ 2 =
          5776 * (r ^ (-η)) ^ 4 * (A.card : ℝ) ^ 2 := by ring
      have e3 : (r ^ (-η)) ^ 4 * r ^ (4 * η) = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
        have : -η * ((4 : ℕ) : ℝ) + 4 * η = 0 := by push_cast; ring
        rw [this, Real.rpow_zero]
      have hchain : 3 / 64 * r ^ (4 * η + 2 * ε₀ - 1) ≤ 5776 * (r ^ (-η)) ^ 4 * (A.card : ℝ) ^ 2 :=
        hwlow.trans (hwH.trans (e1.trans (le_of_eq e2)))
      have e4 : r ^ (8 * η + 2 * ε₀ - 1) = r ^ (4 * η + 2 * ε₀ - 1) * r ^ (4 * η) := by
        rw [← Real.rpow_add hr]; congr 1; ring
      have hr4 : 0 < r ^ (4 * η) := Real.rpow_pos_of_pos hr _
      calc 3 / 369664 * r ^ (8 * η + 2 * ε₀ - 1) =
          (3 / 64 * r ^ (4 * η + 2 * ε₀ - 1)) * r ^ (4 * η) / 5776 := by rw [e4]; ring
        _ ≤ (5776 * (r ^ (-η)) ^ 4 * (A.card : ℝ) ^ 2) * r ^ (4 * η) / 5776 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hchain hr4.le) (by norm_num)
        _ = (A.card : ℝ) ^ 2 * ((r ^ (-η)) ^ 4 * r ^ (4 * η)) := by ring
        _ = (A.card : ℝ) ^ 2 := by rw [e3, mul_one]
    have hpowsq : (r ^ (-(1 / 2) + 100 * (ε₀ + η))) ^ 2 = r ^ (-1 + 200 * (ε₀ + η)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
    rw [← hpowsq] at hsqA
    exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hr.le _) hA0 (by norm_num)).mp hsqA
  · -- degrees
    intro p hp
    have hpG : p ∈ Good := (Finset.mem_filter.mp (hH'H (hAH' hp))).2
    have hpP : p ∈ P := (Finset.mem_filter.mp hpG).1
    have hτp : τ ≤ (farCount D cls d₀ p : ℝ) := (Finset.mem_filter.mp hpG).2
    have hdeg := h.good_degree hF1 hη cls hgeo hcls4 hd₀52 p hpP
    have hτlow : 3 / 128 * r ^ (5 * η + ε₀ - 1) ≤ τ := by
      rw [hτ, le_div_iff₀ (mul_pos (by norm_num) hPpos)]
      have e : r ^ (5 * η + ε₀ - 1) * (4 * (r ^ (-η) * (8 / r))) =
          32 * r ^ (4 * η + ε₀ - 2) := by
        have : r ^ (5 * η + ε₀ - 1) * r ^ (-η) / r = r ^ (4 * η + ε₀ - 2) := by
          rw [← Real.rpow_add hr, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hr]
          congr 1; ring
        calc r ^ (5 * η + ε₀ - 1) * (4 * (r ^ (-η) * (8 / r)))
            = 32 * (r ^ (5 * η + ε₀ - 1) * r ^ (-η) / r) := by ring
          _ = _ := by rw [this]
      have hm : 3 / 128 * r ^ (5 * η + ε₀ - 1) * (4 * (P.card : ℝ)) ≤
          3 / 128 * r ^ (5 * η + ε₀ - 1) * (4 * (r ^ (-η) * (8 / r))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPup (by norm_num))
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hr.le _))
      calc 3 / 128 * r ^ (5 * η + ε₀ - 1) * (4 * (P.card : ℝ))
          ≤ 3 / 128 * r ^ (5 * η + ε₀ - 1) * (4 * (r ^ (-η) * (8 / r))) := hm
        _ = 3 / 128 * (r ^ (5 * η + ε₀ - 1) * (4 * (r ^ (-η) * (8 / r)))) := by ring
        _ = 3 / 128 * (32 * r ^ (4 * η + ε₀ - 2)) := by rw [e]
        _ = 3 / 4 * r ^ (4 * η + ε₀ - 2) := by ring
        _ ≤ (F.card : ℝ) := hFlow
    set K := 12 * 52 ^ (1 / 2 : ℝ) * r ^ (-2 * η) * d₀ ^ (-(1 / 2) : ℝ) with hK
    have hKpos : 0 < K := by
      rw [hK]
      exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
        (Real.rpow_pos_of_pos hr _)) (Real.rpow_pos_of_pos (lt_of_lt_of_le hr hd₀r) _)
    have hchain : r ^ (-1 + 100 * (ε₀ + η)) * K ≤ K * ((P.filter (fun q => d₀ ≤ dist q p ∧
        ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r)).card : ℝ) := by
      calc r ^ (-1 + 100 * (ε₀ + η)) * K ≤ 3 / 128 * r ^ (5 * η + ε₀ - 1) := hF6
        _ ≤ τ := hτlow
        _ ≤ (farCount D cls d₀ p : ℝ) := hτp
        _ ≤ _ := hdeg
    have hchain' : K * r ^ (-1 + 100 * (ε₀ + η)) ≤ K * ((P.filter (fun q => d₀ ≤ dist q p ∧
        ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r)).card : ℝ) := by
      rw [mul_comm K]; exact hchain
    exact le_of_mul_le_mul_left hchain' hKpos

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
