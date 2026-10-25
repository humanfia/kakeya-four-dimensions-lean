-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.Classes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Defs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CircleGeometry
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.DiscreteEnergy

/-!
# Classes of labels in a failed bush estimate

`HalfData.classes`: from `HalfData r ε₀ η P D` we pick a maximal `StripSep`-separated
subfamily `J₀ ⊆ D` and send every label to a label of `J₀` it is not separated from (its
class). Then

* `J₀` has fewer than `r ^ (-1 - ε₀)` elements (`few_lines`), and every label lies near the
  strip of its class, with its normal near the class normal up to sign;
* there are at least `r ^ (4 η + ε₀ - 2)` same-class pairs (Cauchy–Schwarz over the classes,
  since `#D ≥ #P r ^ (η - 1/2) ≥ r ^ (2 η - 3/2)`);
* at most `10 ^ 6 r ^ (-2 - 4 η) d ^ (1/2)` same-class pairs have their points within `d`
  of each other (for `d ≥ r`): the points of such a pair `((p, e), (p', e'))` satisfy
  `|⟪p' - p, e⟫| < 26 r` and `e'` is within `2 r` of `± e`; the normals `e` of the bush of
  `p` in such a strip lie in two arcs of length `≈ r / |p' - p|`, and the dyadic energy
  bound `SP.sum_rpow_neg_le_of_count` sums `|p' - p| ^ (-1/2)` over the points `p'`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

noncomputable section

/-- Same-class pairs of labels. -/
def sameClass (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) :
    Finset ((E2 × E2) × (E2 × E2)) :=
  (D ×ˢ D).filter (fun qq => cls qq.1 = cls qq.2)

/-! ### Generic helpers -/

/-- Counting by fibres, with a real bound on every fibre. -/
theorem cls_card_le_sum {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    {g : α → β} (hg : ∀ a ∈ s, g a ∈ t) (w : β → ℝ)
    (hw : ∀ b ∈ t, ((s.filter (fun a => g a = b)).card : ℝ) ≤ w b) :
    (s.card : ℝ) ≤ ∑ b ∈ t, w b := by
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (fun a ha => hg a ha)]
  push_cast
  exact Finset.sum_le_sum hw

theorem cls_rpow_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

theorem cls_rpow_split {r η : ℝ} (hr : 0 < r) : r ^ (-2 - 4 * η) = (r ^ (-η)) ^ 4 / r ^ 2 := by
  have h1 : (-2 - 4 * η) = (-η) * ((4 : ℕ) : ℝ) - 2 := by push_cast; ring
  rw [h1, Real.rpow_sub hr, Real.rpow_mul hr.le, Real.rpow_natCast, Real.rpow_two]

/-! ### The classes -/

theorem cls_exists {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) :
    ∃ (J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2),
      J₀ ⊆ D ∧ (J₀.card : ℝ) < r ^ (-1 - ε₀) ∧
      (∀ q ∈ D, cls q ∈ J₀) ∧
      (∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r)) := by
  obtain ⟨J, hJD, hJpair, hJmax⟩ := exists_maximal_pairwise D (StripSep r)
  have hch : ∀ q : E2 × E2, ∃ j : E2 × E2,
      q ∈ D → j ∈ J ∧ (q = j ∨ ¬ StripSep r q j ∨ ¬ StripSep r j q) := by
    intro q
    by_cases hq : q ∈ D
    · by_cases hqJ : q ∈ J
      · exact ⟨q, fun _ => ⟨hqJ, Or.inl rfl⟩⟩
      · obtain ⟨j, hj, hj'⟩ := hJmax q hq hqJ
        exact ⟨j, fun _ => ⟨hj, Or.inr hj'⟩⟩
    · exact ⟨q, fun h' => absurd h' hq⟩
  choose cls hcls using hch
  refine ⟨J, cls, hJD, h.few_lines J hJD hJpair, fun q hq => (hcls q hq).1, ?_⟩
  intro q hq
  have hj := hcls q hq
  have hq4 : ‖q.1‖ ≤ 4 := h.P_norm _ (h.D_mem q hq).1
  have hj4 : ‖(cls q).1‖ ≤ 4 := h.P_norm _ (h.D_mem _ (hJD hj.1)).1
  exact near_of_not_stripSep hq4 hj4 hj.2 h.r_pos

/-! ### The lower bound -/

theorem cls_card_D_ge {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) : r ^ (2 * η - 3 / 2) ≤ (D.card : ℝ) := by
  have hr := h.r_pos
  have h1 : (D.card : ℝ) ≤ ∑ p ∈ P, ((D.filter (fun q => q.1 = p)).card : ℝ) := by
    apply cls_card_le_sum (g := fun q => q.1) (fun q hq => (h.D_mem q hq).1)
    intro p _
    exact le_refl _
  have h2 : (D.card : ℝ) = ∑ p ∈ P, ((D.filter (fun q => q.1 = p)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun q => q.1) (fun q hq => (h.D_mem q hq).1)]
    push_cast
    rfl
  have hle : ∀ p ∈ P, ((bushOf D p).card : ℝ) ≤ ((D.filter (fun q => q.1 = p)).card : ℝ) := by
    intro p _
    unfold bushOf
    exact_mod_cast Finset.card_image_le
  have h3 : ∑ _p ∈ P, r ^ (η - 1 / 2) ≤ ∑ p ∈ P, ((D.filter (fun q => q.1 = p)).card : ℝ) :=
    Finset.sum_le_sum (fun p hp => (h.D_card p hp).trans (hle p hp))
  rw [Finset.sum_const, nsmul_eq_mul] at h3
  have h4 : r ^ (η - 1) * r ^ (η - 1 / 2) ≤ (P.card : ℝ) * r ^ (η - 1 / 2) :=
    mul_le_mul_of_nonneg_right h.P_card (Real.rpow_nonneg hr.le _)
  have h5 : r ^ (2 * η - 3 / 2) = r ^ (η - 1) * r ^ (η - 1 / 2) := by
    rw [← Real.rpow_add hr]; ring_nf
  rw [h5, h2]
  linarith

theorem cls_sameClass_card (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (J₀ : Finset (E2 × E2)) (hcls : ∀ q ∈ D, cls q ∈ J₀) :
    ((sameClass D cls).card : ℝ) = ∑ j ∈ J₀, ((D.filter (fun q => cls q = j)).card : ℝ) ^ 2 := by
  have hmaps : Set.MapsTo (fun qq : (E2 × E2) × (E2 × E2) => cls qq.1)
      (sameClass D cls : Set ((E2 × E2) × (E2 × E2))) (J₀ : Set (E2 × E2)) := by
    intro qq hqq
    rw [Finset.mem_coe] at hqq
    simp only [sameClass, Finset.mem_filter, Finset.mem_product] at hqq
    exact hcls _ hqq.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hset : (sameClass D cls).filter (fun qq => cls qq.1 = j) =
      (D.filter (fun q => cls q = j)) ×ˢ (D.filter (fun q => cls q = j)) := by
    ext qq
    simp only [sameClass, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h1, h4⟩, h2, h3 ▸ h4⟩
    · rintro ⟨⟨h1, h4⟩, h2, h5⟩
      exact ⟨⟨⟨h1, h2⟩, h4.trans h5.symm⟩, h4⟩
  rw [hset, Finset.card_product]
  push_cast
  ring

theorem cls_lower {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (hJ : (J₀.card : ℝ) < r ^ (-1 - ε₀)) (hcls : ∀ q ∈ D, cls q ∈ J₀) :
    r ^ (4 * η + ε₀ - 2) ≤ ((sameClass D cls).card : ℝ) := by
  have hr := h.r_pos
  have hD := cls_card_D_ge h
  have hS := cls_sameClass_card D cls J₀ hcls
  have hDsum : (D.card : ℝ) = ∑ j ∈ J₀, ((D.filter (fun q => cls q = j)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := cls) (fun q hq => hcls q hq)]
    push_cast
    rfl
  have hCS := sq_sum_le_card_mul_sum_sq (s := J₀)
    (f := fun j => ((D.filter (fun q => cls q = j)).card : ℝ))
  rw [← hDsum, ← hS] at hCS
  have hpos1 : 0 < r ^ (2 * η - 3 / 2) := Real.rpow_pos_of_pos hr _
  have hD2 : r ^ (4 * η - 3) ≤ (D.card : ℝ) ^ 2 := by
    have h1 : r ^ (4 * η - 3) = (r ^ (2 * η - 3 / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      congr 1
      push_cast
      ring
    rw [h1]
    exact pow_le_pow_left₀ hpos1.le hD 2
  have hSnn : 0 ≤ ((sameClass D cls).card : ℝ) := Nat.cast_nonneg _
  have key : r ^ (4 * η - 3) ≤ r ^ (-1 - ε₀) * ((sameClass D cls).card : ℝ) := by
    calc r ^ (4 * η - 3) ≤ (D.card : ℝ) ^ 2 := hD2
      _ ≤ (J₀.card : ℝ) * ((sameClass D cls).card : ℝ) := hCS
      _ ≤ r ^ (-1 - ε₀) * ((sameClass D cls).card : ℝ) :=
          mul_le_mul_of_nonneg_right hJ.le hSnn
  have hmul : r ^ (4 * η + ε₀ - 2) = r ^ (4 * η - 3) * r ^ (1 + ε₀) := by
    rw [← Real.rpow_add hr]; ring_nf
  have hone : r ^ (-1 - ε₀) * r ^ (1 + ε₀) = 1 := by
    rw [← Real.rpow_add hr]
    have : -1 - ε₀ + (1 + ε₀) = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [hmul]
  have hpos2 : 0 ≤ r ^ (1 + ε₀) := Real.rpow_nonneg hr.le _
  calc r ^ (4 * η - 3) * r ^ (1 + ε₀)
      ≤ (r ^ (-1 - ε₀) * ((sameClass D cls).card : ℝ)) * r ^ (1 + ε₀) :=
        mul_le_mul_of_nonneg_right key hpos2
    _ = ((sameClass D cls).card : ℝ) := by
        rw [mul_comm (r ^ (-1 - ε₀)), mul_assoc, hone, mul_one]

/-! ### Geometry of a same-class pair -/

theorem cls_pair_geom {p e p' e' j1 j2 : E2} {r : ℝ} (hp : ‖p‖ ≤ 4) (hp' : ‖p'‖ ≤ 4)
    (h1 : |inner ℝ (p - j1) j2| < 9 * r) (h2 : dist e j2 < r ∨ dist e (-j2) < r)
    (h3 : |inner ℝ (p' - j1) j2| < 9 * r) (h4 : dist e' j2 < r ∨ dist e' (-j2) < r) :
    |inner ℝ (p' - p) e| < 26 * r ∧ (dist e' e ≤ 2 * r ∨ dist e' (-e) ≤ 2 * r) := by
  have h8 : ‖p' - p‖ ≤ 8 := norm_le_eight_of_norm_le_four hp' hp
  have h18 : |inner ℝ (p' - p) j2| < 18 * r := by
    have hsplit : inner ℝ (p' - p) j2 = inner ℝ (p' - j1) j2 - inner ℝ (p - j1) j2 := by
      rw [← inner_sub_left]
      congr 1
      abel
    rw [hsplit]
    calc |inner ℝ (p' - j1) j2 - inner ℝ (p - j1) j2|
        ≤ |inner ℝ (p' - j1) j2| + |inner ℝ (p - j1) j2| := abs_sub _ _
      _ < 9 * r + 9 * r := add_lt_add h3 h1
      _ = 18 * r := by ring
  constructor
  · rcases h2 with h2 | h2
    · have hee : ‖j2 - e‖ ≤ r := by rw [← dist_eq_norm, dist_comm]; exact h2.le
      have := inner_lt_of_close h8 h18 hee
      linarith
    · have h18' : |inner ℝ (p' - p) (-j2)| < 18 * r := by
        rw [inner_neg_right, abs_neg]; exact h18
      have hee : ‖-j2 - e‖ ≤ r := by rw [← dist_eq_norm, dist_comm]; exact h2.le
      have := inner_lt_of_close h8 h18' hee
      linarith
  · rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4
    · left
      calc dist e' e ≤ dist e' j2 + dist j2 e := dist_triangle _ _ _
        _ ≤ 2 * r := by rw [dist_comm j2]; linarith
    · right
      calc dist e' (-e) ≤ dist e' (-j2) + dist (-j2) (-e) := dist_triangle _ _ _
        _ = dist e' (-j2) + dist e j2 := by rw [dist_neg_neg, dist_comm j2 e]
        _ ≤ 2 * r := by linarith
    · right
      calc dist e' (-e) ≤ dist e' j2 + dist j2 (-e) := dist_triangle _ _ _
        _ = dist e' j2 + dist e (-j2) := by
            rw [← dist_neg_neg j2 (-e), neg_neg, dist_comm (-j2) e]
        _ ≤ 2 * r := by linarith
    · left
      calc dist e' e ≤ dist e' (-j2) + dist (-j2) e := dist_triangle _ _ _
        _ ≤ 2 * r := by rw [dist_comm (-j2)]; linarith

theorem cls_mem_pairs {D : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {r d : ℝ}
    (hP4 : ∀ q ∈ D, ‖q.1‖ ≤ 4)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    {qq : (E2 × E2) × (E2 × E2)}
    (hqq : qq ∈ (sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < d)) :
    qq.1 ∈ D ∧ qq.2 ∈ D ∧ dist qq.1.1 qq.2.1 < d ∧
      |inner ℝ (qq.2.1 - qq.1.1) qq.1.2| < 26 * r ∧
      (dist qq.2.2 qq.1.2 ≤ 2 * r ∨ dist qq.2.2 (-qq.1.2) ≤ 2 * r) := by
  simp only [sameClass, Finset.mem_filter, Finset.mem_product] at hqq
  obtain ⟨⟨⟨hq1, hq2⟩, hc⟩, hd⟩ := hqq
  obtain ⟨g1, g2⟩ := hgeo _ hq1
  obtain ⟨g3, g4⟩ := hgeo _ hq2
  rw [← hc] at g3 g4
  exact ⟨hq1, hq2, hd, cls_pair_geom (hP4 _ hq1) (hP4 _ hq2) g1 g2 g3 g4⟩

/-! ### Counting bounds from `HalfData` -/

theorem cls_card_B {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p' e : E2} (hp' : p' ∈ P) (he : ‖e‖ = 1) :
    (((bushOf D p').filter (fun e' => dist e' e ≤ 2 * r ∨ dist e' (-e) ≤ 2 * r)).card : ℝ) ≤
      3 * r ^ (-η) := by
  have hr := h.r_pos
  have hne : ‖-e‖ = 1 := by rw [norm_neg, he]
  have h1 := h.D_kt p' hp' e he (2 * r) (by linarith)
  have h2 := h.D_kt p' hp' (-e) hne (2 * r) (by linarith)
  have h2r : 2 * r / r = 2 := by field_simp
  rw [h2r] at h1 h2
  have ha2 := cls_rpow_half_sq (x := 2) (by norm_num)
  have ha0 : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have ha1 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 / 2 := by nlinarith
  have hX : 0 ≤ r ^ (-η) := Real.rpow_nonneg hr.le _
  rw [Finset.filter_or]
  calc (((bushOf D p').filter (fun e' => dist e' e ≤ 2 * r) ∪
        (bushOf D p').filter (fun e' => dist e' (-e) ≤ 2 * r)).card : ℝ)
      ≤ (((bushOf D p').filter (fun e' => dist e' e ≤ 2 * r)).card : ℝ) +
        (((bushOf D p').filter (fun e' => dist e' (-e) ≤ 2 * r)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ r ^ (-η) * (2 : ℝ) ^ (1 / 2 : ℝ) + r ^ (-η) * (2 : ℝ) ^ (1 / 2 : ℝ) := add_le_add h1 h2
    _ ≤ 3 * r ^ (-η) := by nlinarith

theorem cls_card_bush {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hr : r ≤ 1 / 100) {p : E2} (hp : p ∈ P) :
    ((bushOf D p).card : ℝ) ≤ r ^ (-η) * (2 / r) ^ (1 / 2 : ℝ) := by
  have h1 := h.D_kt p hp ax0 norm_ax0 2 (by linarith)
  have hsub : (bushOf D p).filter (fun e => dist e ax0 ≤ 2) = bushOf D p := by
    apply Finset.filter_true_of_mem
    intro e he
    have he1 : ‖e‖ = 1 := (h.D_mem _ (mem_bushOf.mp he)).2
    calc dist e ax0 ≤ ‖e‖ + ‖ax0‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
      _ = 2 := by rw [he1, norm_ax0]; norm_num
  rw [hsub] at h1
  exact h1

theorem cls_card_strip {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p p' : E2} (hp : p ∈ P) (hp' : p' ∈ P) (hne : p' ≠ p) :
    (((bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r)).card : ℝ) ≤
      2 * r ^ (-η) * ((52 : ℝ) ^ (1 / 2 : ℝ) * (dist p' p) ^ (-(1 / 2 : ℝ))) := by
  have hr := h.r_pos
  have hv0 : p' - p ≠ 0 := sub_ne_zero.mpr hne
  have hvpos : 0 < ‖p' - p‖ := norm_pos_iff.mpr hv0
  have hv8 : ‖p' - p‖ ≤ 8 := norm_le_eight_of_norm_le_four (h.P_norm _ hp') (h.P_norm _ hp)
  obtain ⟨e₀, he₀, hball⟩ := SP.unit_circle_strip_two_balls hv0 (s := 26 * r)
  set ρ := 2 * (26 * r) / ‖p' - p‖ with hρ
  have hρr : r ≤ ρ := by
    rw [hρ, le_div_iff₀ hvpos]
    nlinarith
  have hsub : (bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r) ⊆
      (bushOf D p).filter (fun e => dist e e₀ ≤ ρ) ∪
        (bushOf D p).filter (fun e => dist e (-e₀) ≤ ρ) := by
    intro e he
    rw [Finset.mem_filter] at he
    have he1 : ‖e‖ = 1 := (h.D_mem _ (mem_bushOf.mp he.1)).2
    have hin : |inner ℝ e (p' - p)| ≤ 26 * r := by rw [real_inner_comm]; exact he.2.le
    rcases hball e he1 hin with h1 | h1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he.1, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he.1, h1⟩)
  have hne₀ : ‖-e₀‖ = 1 := by rw [norm_neg, he₀]
  have h1 := h.D_kt p hp e₀ he₀ ρ hρr
  have h2 := h.D_kt p hp (-e₀) hne₀ ρ hρr
  have hρ' : (ρ / r) ^ (1 / 2 : ℝ) =
      (52 : ℝ) ^ (1 / 2 : ℝ) * (dist p' p) ^ (-(1 / 2 : ℝ)) := by
    have h52 : ρ / r = 52 / ‖p' - p‖ := by
      rw [hρ]; field_simp; ring
    rw [h52, Real.div_rpow (by norm_num) hvpos.le, dist_eq_norm, Real.rpow_neg hvpos.le,
      div_eq_mul_inv]
  calc (((bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r)).card : ℝ)
      ≤ (((bushOf D p).filter (fun e => dist e e₀ ≤ ρ) ∪
          (bushOf D p).filter (fun e => dist e (-e₀) ≤ ρ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((bushOf D p).filter (fun e => dist e e₀ ≤ ρ)).card : ℝ) +
          (((bushOf D p).filter (fun e => dist e (-e₀) ≤ ρ)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ) + r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ) := add_le_add h1 h2
    _ = 2 * r ^ (-η) * ((52 : ℝ) ^ (1 / 2 : ℝ) * (dist p' p) ^ (-(1 / 2 : ℝ))) := by
        rw [hρ']; ring

theorem cls_card_P {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hr8 : r ≤ 8) : (P.card : ℝ) ≤ r ^ (-η) * (8 / r) := by
  have h1 := h.P_kt 0 8 hr8
  have h2 : P.filter (fun p => dist p 0 ≤ 8) = P := by
    apply Finset.filter_true_of_mem
    intro p hp
    rw [dist_zero_right]
    linarith [h.P_norm p hp]
  rw [h2] at h1
  exact h1

/-! ### The energy of the points near a point -/

theorem cls_energy_numeric {A d : ℝ} (hA : 0 ≤ A) (hd : 0 < d) :
    A * d * (d / 2) ^ (-(1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ) ^ (1 - 1 / 2 : ℝ)) ≤
      10 * A * d ^ (1 / 2 : ℝ) := by
  have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h12, Real.rpow_neg (by positivity), Real.div_rpow hd.le (by norm_num)]
  have hs0 : 0 < d ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hd _
  have hs2 := cls_rpow_half_sq hd.le
  have ht2 := cls_rpow_half_sq (x := 2) (by norm_num)
  have hq2 := cls_rpow_half_sq (x := 1 / 2) (by norm_num)
  have ht0 : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  set s := d ^ (1 / 2 : ℝ) with hs
  set t := (2 : ℝ) ^ (1 / 2 : ℝ) with ht
  set q := (1 / 2 : ℝ) ^ (1 / 2 : ℝ) with hq
  have hq1 : q ≤ 3 / 4 := by nlinarith
  have ht1 : t ≤ 3 / 2 := by nlinarith
  have hden : 0 < 1 - q := by linarith
  rw [div_le_iff₀ hden]
  have hrew : A * d * (s / t)⁻¹ = A * s * t := by
    rw [← hs2]
    field_simp
  rw [hrew]
  have hAs : 0 ≤ A * s := by positivity
  nlinarith

theorem cls_energy {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p : E2} (hp : p ∈ P) {d : ℝ} (hd : r ≤ d) :
    ∑ p' ∈ (P.filter (fun p' => dist p p' < d)).erase p, (dist p' p) ^ (-(1 / 2 : ℝ)) ≤
      10 * (r ^ (-η) / r) * d ^ (1 / 2 : ℝ) := by
  have hr := h.r_pos
  set S := (P.filter (fun p' => dist p p' < d)).erase p with hS
  have hd0 : 0 < d := lt_of_lt_of_le hr hd
  have hA : 0 ≤ r ^ (-η) / r := by positivity
  have hmemS : ∀ x ∈ S, x ≠ p ∧ x ∈ P ∧ dist p x < d := by
    intro x hx
    rw [hS, Finset.mem_erase, Finset.mem_filter] at hx
    exact ⟨hx.1, hx.2.1, hx.2.2⟩
  have key := SP.sum_rpow_neg_le_of_count (X := S) (fun x => dist x.1 p)
    (A := r ^ (-η) / r) (R := d) (γ := 1 / 2) hA hd0 (by norm_num) (by norm_num) ?_ ?_
  · have hsum : ∑ x : S, dist x.1 p ^ (-(1 / 2 : ℝ)) =
        ∑ x ∈ S, dist x p ^ (-(1 / 2 : ℝ)) :=
      Finset.sum_coe_sort S (fun x => dist x p ^ (-(1 / 2 : ℝ)))
    rw [hsum] at key
    exact key.trans (cls_energy_numeric hA hd0)
  · intro x
    obtain ⟨hx1, -, hx3⟩ := hmemS x.1 x.2
    refine ⟨dist_pos.mpr hx1, ?_⟩
    rw [dist_comm]
    exact hx3.le
  · intro t ht
    by_cases htr : r ≤ t
    · have hkt := h.P_kt p t htr
      have hcard : (Finset.univ.filter (fun x : S => dist x.1 p ≤ t)).card ≤
          (P.filter (fun p' => dist p' p ≤ t)).card := by
        apply Finset.card_le_card_of_injOn (fun x : S => (x : E2))
        · intro x hx
          rw [Finset.mem_coe, Finset.mem_filter] at hx
          rw [Finset.mem_coe, Finset.mem_filter]
          exact ⟨(hmemS x.1 x.2).2.1, hx.2⟩
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      calc ((Finset.univ.filter (fun x : S => dist x.1 p ≤ t)).card : ℝ)
          ≤ ((P.filter (fun p' => dist p' p ≤ t)).card : ℝ) := by exact_mod_cast hcard
        _ ≤ r ^ (-η) * (t / r) := hkt
        _ = r ^ (-η) / r * t := by ring
    · have hempty : Finset.univ.filter (fun x : S => dist x.1 p ≤ t) = ∅ := by
        apply Finset.filter_false_of_mem
        intro x _
        obtain ⟨hx1, hx2, -⟩ := hmemS x.1 x.2
        have hsep := h.P_sep x.1 hx2 p hp hx1
        intro hle
        exact htr (hsep.trans hle)
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity

/-! ### The upper bound -/

section Upper

variable {r ε₀ η d : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
  {G : Finset ((E2 × E2) × (E2 × E2))}

/-- The pairs of a fixed pair of points `(p, p')`. -/
theorem cls_cell (h : HalfData r ε₀ η P D)
    (hG : ∀ qq ∈ G, qq.1 ∈ D ∧ qq.2 ∈ D ∧ dist qq.1.1 qq.2.1 < d ∧
      |inner ℝ (qq.2.1 - qq.1.1) qq.1.2| < 26 * r ∧
      (dist qq.2.2 qq.1.2 ≤ 2 * r ∨ dist qq.2.2 (-qq.1.2) ≤ 2 * r))
    {p p' : E2} (hp' : p' ∈ P) :
    (((G.filter (fun qq => qq.1.1 = p)).filter (fun qq => qq.2.1 = p')).card : ℝ) ≤
      3 * r ^ (-η) * (((bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r)).card : ℝ) := by
  have h1 : (((G.filter (fun qq => qq.1.1 = p)).filter (fun qq => qq.2.1 = p')).card : ℝ) ≤
      ∑ _e ∈ (bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r), 3 * r ^ (-η) := by
    apply cls_card_le_sum (g := fun qq => qq.1.2)
    · intro qq hqq
      simp only [Finset.mem_filter] at hqq
      obtain ⟨⟨hqG, hqp⟩, hqp'⟩ := hqq
      obtain ⟨hq1, -, -, hin, -⟩ := hG qq hqG
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [mem_bushOf, ← hqp]
        exact hq1
      · rw [← hqp, ← hqp']
        exact hin
    · intro e he
      have he1 : ‖e‖ = 1 := (h.D_mem _ (mem_bushOf.mp (Finset.mem_filter.mp he).1)).2
      refine le_trans ?_ (cls_card_B h hp' he1)
      have hcard : ((((G.filter (fun qq => qq.1.1 = p)).filter
            (fun qq => qq.2.1 = p')).filter (fun qq => qq.1.2 = e)).card) ≤
          ((bushOf D p').filter
            (fun e' => dist e' e ≤ 2 * r ∨ dist e' (-e) ≤ 2 * r)).card := by
        apply Finset.card_le_card_of_injOn (fun qq => qq.2.2)
        · intro qq hqq
          rw [Finset.mem_coe] at hqq
          simp only [Finset.mem_filter] at hqq
          obtain ⟨⟨⟨hqG, hqp⟩, hqp'⟩, hqe⟩ := hqq
          obtain ⟨-, hq2, -, -, hcl⟩ := hG qq hqG
          rw [Finset.mem_coe, Finset.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [mem_bushOf, ← hqp']
            exact hq2
          · rw [← hqe]
            exact hcl
        · intro qq hqq qq' hqq' heq
          rw [Finset.mem_coe] at hqq hqq'
          simp only [Finset.mem_filter] at hqq hqq'
          obtain ⟨⟨⟨-, hqp⟩, hqp'⟩, hqe⟩ := hqq
          obtain ⟨⟨⟨-, hqp2⟩, hqp2'⟩, hqe2⟩ := hqq'
          exact Prod.ext (Prod.ext (hqp.trans hqp2.symm) (hqe.trans hqe2.symm))
            (Prod.ext (hqp'.trans hqp2'.symm) heq)
      exact_mod_cast hcard
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  linarith

/-- The pairs whose first point is `p`. -/
theorem cls_row (h : HalfData r ε₀ η P D) (hr : r ≤ 1 / 100) (hd : r ≤ d)
    (hG : ∀ qq ∈ G, qq.1 ∈ D ∧ qq.2 ∈ D ∧ dist qq.1.1 qq.2.1 < d ∧
      |inner ℝ (qq.2.1 - qq.1.1) qq.1.2| < 26 * r ∧
      (dist qq.2.2 qq.1.2 ≤ 2 * r ∨ dist qq.2.2 (-qq.1.2) ≤ 2 * r))
    {p : E2} (hp : p ∈ P) :
    ((G.filter (fun qq => qq.1.1 = p)).card : ℝ) ≤
      3 * r ^ (-η) * (r ^ (-η) * (2 / r) ^ (1 / 2 : ℝ) +
        2 * r ^ (-η) * ((52 : ℝ) ^ (1 / 2 : ℝ) * (10 * (r ^ (-η) / r) * d ^ (1 / 2 : ℝ)))) := by
  have hr0 := h.r_pos
  have hX : 0 ≤ r ^ (-η) := Real.rpow_nonneg hr0.le _
  have hb : 0 ≤ (52 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  set N := P.filter (fun p' => dist p p' < d) with hN
  have hpN : p ∈ N := Finset.mem_filter.mpr ⟨hp, by rw [dist_self]; linarith⟩
  have h1 : ((G.filter (fun qq => qq.1.1 = p)).card : ℝ) ≤
      ∑ p' ∈ N, 3 * r ^ (-η) *
        (((bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r)).card : ℝ) := by
    apply cls_card_le_sum (g := fun qq => qq.2.1)
    · intro qq hqq
      rw [Finset.mem_filter] at hqq
      obtain ⟨-, hq2, hdist, -, -⟩ := hG qq hqq.1
      refine Finset.mem_filter.mpr ⟨(h.D_mem _ hq2).1, ?_⟩
      rw [← hqq.2]
      exact hdist
    · intro p' hp'
      exact cls_cell h hG (Finset.mem_filter.mp hp').1
  rw [← Finset.add_sum_erase N _ hpN] at h1
  have hdiag : 3 * r ^ (-η) *
      (((bushOf D p).filter (fun e => |inner ℝ (p - p) e| < 26 * r)).card : ℝ) ≤
      3 * r ^ (-η) * (r ^ (-η) * (2 / r) ^ (1 / 2 : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (cls_card_bush h hr hp)
  have hoff : ∑ p' ∈ N.erase p, 3 * r ^ (-η) *
        (((bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r)).card : ℝ) ≤
      3 * r ^ (-η) * (2 * r ^ (-η) * ((52 : ℝ) ^ (1 / 2 : ℝ) *
        ∑ p' ∈ N.erase p, (dist p' p) ^ (-(1 / 2 : ℝ)))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p' hp'
    have hp'P : p' ∈ P := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp')).1
    exact mul_le_mul_of_nonneg_left (cls_card_strip h hp hp'P (Finset.ne_of_mem_erase hp'))
      (by positivity)
  have hen := cls_energy h hp hd
  have hen' : 3 * r ^ (-η) * (2 * r ^ (-η) * ((52 : ℝ) ^ (1 / 2 : ℝ) *
        ∑ p' ∈ N.erase p, (dist p' p) ^ (-(1 / 2 : ℝ)))) ≤
      3 * r ^ (-η) * (2 * r ^ (-η) * ((52 : ℝ) ^ (1 / 2 : ℝ) *
        (10 * (r ^ (-η) / r) * d ^ (1 / 2 : ℝ)))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hen hb
  linarith

theorem cls_numeric {r d X : ℝ} (hr : 0 < r) (hrd : r ≤ d) (hX : 1 ≤ X) :
    X * (8 / r) * (3 * X * (X * (2 / r) ^ (1 / 2 : ℝ) +
        2 * X * ((52 : ℝ) ^ (1 / 2 : ℝ) * (10 * (X / r) * d ^ (1 / 2 : ℝ))))) ≤
      10 ^ 6 * (X ^ 4 / r ^ 2) * d ^ (1 / 2 : ℝ) := by
  have hd : 0 < d := lt_of_lt_of_le hr hrd
  have hu0 : 0 < r ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr _
  have hus : r ^ (1 / 2 : ℝ) ≤ d ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hr.le hrd (by norm_num)
  have hu2 := cls_rpow_half_sq hr.le
  have ha2 := cls_rpow_half_sq (x := 2) (by norm_num)
  have hb2 := cls_rpow_half_sq (x := 52) (by norm_num)
  have ha0 : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hb0 : 0 ≤ (52 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h2r : (2 / r) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) / r ^ (1 / 2 : ℝ) :=
    Real.div_rpow (by norm_num) hr.le _
  rw [h2r]
  set u := r ^ (1 / 2 : ℝ) with hu
  set s := d ^ (1 / 2 : ℝ) with hs
  set a := (2 : ℝ) ^ (1 / 2 : ℝ) with ha
  set b := (52 : ℝ) ^ (1 / 2 : ℝ) with hb
  have ha1 : a ≤ 3 / 2 := by nlinarith
  have hb1 : b ≤ 8 := by nlinarith
  have hX0 : 0 < X := by linarith
  have hX34 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
  have hlhs : X * (8 / r) * (3 * X * (X * (a / u) + 2 * X * (b * (10 * (X / r) * s)))) =
      (24 * X ^ 3 * a * u + 480 * X ^ 4 * b * s) / u ^ 4 := by
    rw [← hu2]
    field_simp
    ring
  have hrhs : 10 ^ 6 * (X ^ 4 / r ^ 2) * s = (10 ^ 6 * X ^ 4 * s) / u ^ 4 := by
    rw [← hu2]
    field_simp
  rw [hlhs, hrhs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs0 : 0 ≤ s := hu0.le.trans hus
  have hX4 : 0 ≤ X ^ 4 := by positivity
  have hau : a * u ≤ 3 / 2 * s := mul_le_mul ha1 hus hu0.le (by norm_num)
  have ht1 : 24 * X ^ 3 * a * u ≤ 36 * X ^ 4 * s := by
    have h3 : 0 ≤ X ^ 3 := by positivity
    have : X ^ 3 * (a * u) ≤ X ^ 4 * (3 / 2 * s) :=
      mul_le_mul hX34 hau (mul_nonneg ha0 hu0.le) hX4
    nlinarith
  have ht2 : 480 * X ^ 4 * b * s ≤ 3840 * X ^ 4 * s := by
    have : X ^ 4 * s * b ≤ X ^ 4 * s * 8 := mul_le_mul_of_nonneg_left hb1 (by positivity)
    nlinarith
  have hXs : 0 ≤ X ^ 4 * s := by positivity
  nlinarith

theorem cls_upper (h : HalfData r ε₀ η P D) (hr : r ≤ 1 / 100) (hη : 0 < η) (hd : r ≤ d)
    (hG : ∀ qq ∈ G, qq.1 ∈ D ∧ qq.2 ∈ D ∧ dist qq.1.1 qq.2.1 < d ∧
      |inner ℝ (qq.2.1 - qq.1.1) qq.1.2| < 26 * r ∧
      (dist qq.2.2 qq.1.2 ≤ 2 * r ∨ dist qq.2.2 (-qq.1.2) ≤ 2 * r)) :
    (G.card : ℝ) ≤ 10 ^ 6 * r ^ (-2 - 4 * η) * d ^ (1 / 2 : ℝ) := by
  have hr0 := h.r_pos
  have hd0 : 0 < d := lt_of_lt_of_le hr0 hd
  have hX1 : 1 ≤ r ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 (by linarith) (by linarith)
  have hX0 : 0 ≤ r ^ (-η) := by linarith
  have hb : 0 ≤ (52 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  set K := 3 * r ^ (-η) * (r ^ (-η) * (2 / r) ^ (1 / 2 : ℝ) +
    2 * r ^ (-η) * ((52 : ℝ) ^ (1 / 2 : ℝ) * (10 * (r ^ (-η) / r) * d ^ (1 / 2 : ℝ)))) with hK
  have h1 : (G.card : ℝ) ≤ ∑ _p ∈ P, K := by
    apply cls_card_le_sum (g := fun qq => qq.1.1) (fun qq hqq => (h.D_mem _ (hG qq hqq).1).1)
    intro p hp
    exact cls_row h hr hd hG hp
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hP := cls_card_P h (by linarith)
  have hK0 : 0 ≤ K := by positivity
  rw [cls_rpow_split hr0]
  calc (G.card : ℝ) ≤ (P.card : ℝ) * K := h1
    _ ≤ r ^ (-η) * (8 / r) * K := mul_le_mul_of_nonneg_right hP hK0
    _ ≤ 10 ^ 6 * ((r ^ (-η)) ^ 4 / r ^ 2) * d ^ (1 / 2 : ℝ) := cls_numeric hr0 hd hX1

end Upper

/-! ### The theorem -/

theorem HalfData.classes {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hr : r ≤ 1 / 100) (hη : 0 < η) :
    ∃ (J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2),
      J₀ ⊆ D ∧ (J₀.card : ℝ) < r ^ (-1 - ε₀) ∧
      (∀ q ∈ D, cls q ∈ J₀) ∧
      (∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r)) ∧
      r ^ (4 * η + ε₀ - 2) ≤ ((sameClass D cls).card : ℝ) ∧
      ∀ d : ℝ, r ≤ d →
        (((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < d)).card : ℝ) ≤
          10 ^ 6 * r ^ (-2 - 4 * η) * d ^ (1 / 2 : ℝ) := by
  obtain ⟨J₀, cls, hJD, hJcard, hcls, hgeo⟩ := cls_exists h
  refine ⟨J₀, cls, hJD, hJcard, hcls, hgeo, cls_lower h J₀ cls hJcard hcls, ?_⟩
  intro d hd
  apply cls_upper h hr hη hd
  intro qq hqq
  exact cls_mem_pairs (fun q hq => h.P_norm _ (h.D_mem q hq).1) hgeo hqq

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
