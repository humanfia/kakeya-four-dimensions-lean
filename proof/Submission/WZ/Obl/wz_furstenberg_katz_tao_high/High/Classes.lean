-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.Classes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/Classes.lean (c61cafd).
-- Adapted from local obligation o157, branch x0675, commit dfe14ebd23a4.
-- Source: High/Classes.lean. Own namespace renamed; shared class geometry imported from accepted o213.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Classes
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.FailData

/-!
# Classes of labels in a failed bush estimate at a general exponent

`FailData.classes` is x0538's `HalfData.classes` (`HalfExt/Classes.lean`) for a general
exponent `0 ≤ s < 1`. A maximal `StripSep`-separated subfamily `J₀ ⊆ D` (the lines) has
fewer than `r ^ (-2 s - ε₀)` elements, every label is sent to a line it is not separated
from (its class), and

* there are at least `r ^ (4 η + ε₀ - 2)` same-class pairs (Cauchy–Schwarz over the
  classes, since `#D ≥ #P r ^ (η - s) ≥ r ^ (2 η - 1 - s)`);
* for `d ≥ r` at most `10 ^ 4 / (1 - (1/2) ^ (1 - s)) * r ^ (-2 - 4 η) * d ^ (1 - s)`
  same-class pairs have their points within `d`.

So the pins of the lines are `(1 - s)`-dimensional in the energy sense. The proofs follow
x0538's; only the exponent `1/2` of the bushes becomes `s`, and the s-independent
helpers (`sameClass`, `cls_exists`'s geometry, `cls_pair_geom`, `cls_mem_pairs`,
`cls_cell`'s counting) are reused from `HalfExt/Classes.lean`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

noncomputable section

/-! ### The classes and the lower bound -/

theorem fcls_exists_full {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) :
    ∃ (J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2),
      J₀ ⊆ D ∧ (∀ x ∈ J₀, ∀ y ∈ J₀, x ≠ y → StripSep r x y) ∧
      (J₀.card : ℝ) < r ^ (-(2 * s) - ε₀) ∧
      (∀ q ∈ D, cls q ∈ J₀) ∧
      (∀ q ∈ D, q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q) ∧
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
  refine ⟨J, cls, hJD, hJpair, h.few_lines J hJD hJpair,
    fun q hq => (hcls q hq).1, fun q hq => (hcls q hq).2, ?_⟩
  intro q hq
  have hj := hcls q hq
  have hq4 : ‖q.1‖ ≤ 4 := h.P_norm _ (h.D_mem q hq).1
  have hj4 : ‖(cls q).1‖ ≤ 4 := h.P_norm _ (h.D_mem _ (hJD hj.1)).1
  exact near_of_not_stripSep hq4 hj4 hj.2 h.r_pos

theorem fcls_exists {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) :
    ∃ (J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2),
      J₀ ⊆ D ∧ (J₀.card : ℝ) < r ^ (-(2 * s) - ε₀) ∧
      (∀ q ∈ D, cls q ∈ J₀) ∧
      (∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r)) := by
  obtain ⟨J, cls, hJD, _, hcard, hmem, _, hgeo⟩ := fcls_exists_full h
  exact ⟨J, cls, hJD, hcard, hmem, hgeo⟩

theorem fcls_card_D_ge {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) : r ^ (2 * η - 1 - s) ≤ (D.card : ℝ) := by
  have hr := h.r_pos
  have h2 : (D.card : ℝ) = ∑ p ∈ P, ((bushOf D p).card : ℝ) :=
    card_eq_sum_bushOf (fun q hq => (h.D_mem q hq).1)
  have h3 : ∑ _p ∈ P, r ^ (η - s) ≤ ∑ p ∈ P, ((bushOf D p).card : ℝ) :=
    Finset.sum_le_sum (fun p hp => h.D_card p hp)
  rw [Finset.sum_const, nsmul_eq_mul] at h3
  have h4 : r ^ (η - 1) * r ^ (η - s) ≤ (P.card : ℝ) * r ^ (η - s) :=
    mul_le_mul_of_nonneg_right h.P_card (Real.rpow_nonneg hr.le _)
  have h5 : r ^ (2 * η - 1 - s) = r ^ (η - 1) * r ^ (η - s) := by
    rw [← Real.rpow_add hr]; ring_nf
  rw [h5, h2]
  linarith

theorem fcls_lower {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (hJ : (J₀.card : ℝ) < r ^ (-(2 * s) - ε₀)) (hcls : ∀ q ∈ D, cls q ∈ J₀) :
    r ^ (4 * η + ε₀ - 2) ≤ ((sameClass D cls).card : ℝ) := by
  have hr := h.r_pos
  have hD := fcls_card_D_ge h
  have hS := cls_sameClass_card D cls J₀ hcls
  have hDsum : (D.card : ℝ) = ∑ j ∈ J₀, ((D.filter (fun q => cls q = j)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := cls) (fun q hq => hcls q hq)]
    push_cast
    rfl
  have hCS := sq_sum_le_card_mul_sum_sq (s := J₀)
    (f := fun j => ((D.filter (fun q => cls q = j)).card : ℝ))
  rw [← hDsum, ← hS] at hCS
  have hpos1 : 0 < r ^ (2 * η - 1 - s) := Real.rpow_pos_of_pos hr _
  have hD2 : r ^ (4 * η - 2 - 2 * s) ≤ (D.card : ℝ) ^ 2 := by
    have h1 : r ^ (4 * η - 2 - 2 * s) = (r ^ (2 * η - 1 - s)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      congr 1
      push_cast
      ring
    rw [h1]
    exact pow_le_pow_left₀ hpos1.le hD 2
  have hSnn : 0 ≤ ((sameClass D cls).card : ℝ) := Nat.cast_nonneg _
  have key : r ^ (4 * η - 2 - 2 * s) ≤
      r ^ (-(2 * s) - ε₀) * ((sameClass D cls).card : ℝ) := by
    calc r ^ (4 * η - 2 - 2 * s) ≤ (D.card : ℝ) ^ 2 := hD2
      _ ≤ (J₀.card : ℝ) * ((sameClass D cls).card : ℝ) := hCS
      _ ≤ r ^ (-(2 * s) - ε₀) * ((sameClass D cls).card : ℝ) :=
          mul_le_mul_of_nonneg_right hJ.le hSnn
  have hmul : r ^ (4 * η + ε₀ - 2) = r ^ (4 * η - 2 - 2 * s) * r ^ (2 * s + ε₀) := by
    rw [← Real.rpow_add hr]; ring_nf
  have hone : r ^ (-(2 * s) - ε₀) * r ^ (2 * s + ε₀) = 1 := by
    rw [← Real.rpow_add hr]
    have : -(2 * s) - ε₀ + (2 * s + ε₀) = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [hmul]
  have hpos2 : 0 ≤ r ^ (2 * s + ε₀) := Real.rpow_nonneg hr.le _
  calc r ^ (4 * η - 2 - 2 * s) * r ^ (2 * s + ε₀)
      ≤ (r ^ (-(2 * s) - ε₀) * ((sameClass D cls).card : ℝ)) * r ^ (2 * s + ε₀) :=
        mul_le_mul_of_nonneg_right key hpos2
    _ = ((sameClass D cls).card : ℝ) := by
        rw [mul_comm (r ^ (-(2 * s) - ε₀)), mul_assoc, hone, mul_one]

/-! ### Counting bounds from `FailData` -/

theorem fcls_two_rpow_le {s : ℝ} (_hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (2 : ℝ) ^ s ≤ 2 := by
  simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1

theorem fcls_card_B {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {p' e : E2} (hp' : p' ∈ P)
    (he : ‖e‖ = 1) :
    (((bushOf D p').filter (fun e' => dist e' e ≤ 2 * r ∨ dist e' (-e) ≤ 2 * r)).card : ℝ) ≤
      4 * r ^ (-η) := by
  have hr := h.r_pos
  have hne : ‖-e‖ = 1 := by rw [norm_neg, he]
  have h1 := h.D_kt p' hp' e he (2 * r) (by linarith)
  have h2 := h.D_kt p' hp' (-e) hne (2 * r) (by linarith)
  have h2r : 2 * r / r = 2 := by field_simp
  rw [h2r] at h1 h2
  have ha1 := fcls_two_rpow_le hs0 hs1
  have hX : 0 ≤ r ^ (-η) := Real.rpow_nonneg hr.le _
  rw [Finset.filter_or]
  calc (((bushOf D p').filter (fun e' => dist e' e ≤ 2 * r) ∪
        (bushOf D p').filter (fun e' => dist e' (-e) ≤ 2 * r)).card : ℝ)
      ≤ (((bushOf D p').filter (fun e' => dist e' e ≤ 2 * r)).card : ℝ) +
        (((bushOf D p').filter (fun e' => dist e' (-e) ≤ 2 * r)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ r ^ (-η) * (2 : ℝ) ^ s + r ^ (-η) * (2 : ℝ) ^ s := add_le_add h1 h2
    _ ≤ 4 * r ^ (-η) := by nlinarith

theorem fcls_card_bush {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hr : r ≤ 1 / 100) {p : E2} (hp : p ∈ P) :
    ((bushOf D p).card : ℝ) ≤ r ^ (-η) * (2 / r) ^ s := by
  have h1 := h.D_kt p hp ax0 norm_ax0 2 (by linarith)
  have hsub : (bushOf D p).filter (fun e => dist e ax0 ≤ 2) = bushOf D p := by
    apply Finset.filter_true_of_mem
    intro e he
    have he1 : ‖e‖ = 1 := (h.D_mem _ (mem_bushOf.mp he)).2
    calc dist e ax0 ≤ ‖e‖ + ‖ax0‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
      _ = 2 := by rw [he1, norm_ax0]; norm_num
  rw [hsub] at h1
  exact h1

theorem fcls_card_strip {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) {p p' : E2} (hp : p ∈ P) (hp' : p' ∈ P) (hne : p' ≠ p) :
    (((bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r)).card : ℝ) ≤
      2 * r ^ (-η) * ((52 : ℝ) ^ s * (dist p' p) ^ (-s)) := by
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
  have hρ' : (ρ / r) ^ s = (52 : ℝ) ^ s * (dist p' p) ^ (-s) := by
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
    _ ≤ r ^ (-η) * (ρ / r) ^ s + r ^ (-η) * (ρ / r) ^ s := add_le_add h1 h2
    _ = 2 * r ^ (-η) * ((52 : ℝ) ^ s * (dist p' p) ^ (-s)) := by
        rw [hρ']; ring

theorem fcls_card_P {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hr8 : r ≤ 8) : (P.card : ℝ) ≤ r ^ (-η) * (8 / r) := by
  have h1 := h.P_kt 0 8 hr8
  have h2 : P.filter (fun p => dist p 0 ≤ 8) = P := by
    apply Finset.filter_true_of_mem
    intro p hp
    rw [dist_zero_right]
    linarith [h.P_norm p hp]
  rw [h2] at h1
  exact h1

/-! ### The energy of the points near a point -/

theorem fcls_energy {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s < 1) {p : E2} (hp : p ∈ P) {d : ℝ}
    (hd : r ≤ d) :
    ∑ p' ∈ (P.filter (fun p' => dist p p' < d)).erase p, (dist p' p) ^ (-s) ≤
      (r ^ (-η) / r) * d * (d / 2) ^ (-s) / (1 - (1 / 2 : ℝ) ^ (1 - s)) := by
  have hr := h.r_pos
  set S := (P.filter (fun p' => dist p p' < d)).erase p with hS
  have hd0 : 0 < d := lt_of_lt_of_le hr hd
  have hA : 0 ≤ r ^ (-η) / r := by positivity
  have hmemS : ∀ x ∈ S, x ≠ p ∧ x ∈ P ∧ dist p x < d := by
    intro x hx
    rw [hS, Finset.mem_erase, Finset.mem_filter] at hx
    exact ⟨hx.1, hx.2.1, hx.2.2⟩
  have key := SP.sum_rpow_neg_le_of_count (X := S) (fun x => dist x.1 p)
    (A := r ^ (-η) / r) (R := d) (γ := s) hA hd0 hs0 hs1 ?_ ?_
  · have hsum : ∑ x : S, dist x.1 p ^ (-s) = ∑ x ∈ S, dist x p ^ (-s) :=
      Finset.sum_coe_sort S (fun x => dist x p ^ (-s))
    rw [hsum] at key
    exact key
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

variable {r s ε₀ η d : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
  {G : Finset ((E2 × E2) × (E2 × E2))}

/-- The pairs of a fixed pair of points `(p, p')`. -/
theorem fcls_cell (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hG : ∀ qq ∈ G, qq.1 ∈ D ∧ qq.2 ∈ D ∧ dist qq.1.1 qq.2.1 < d ∧
      |inner ℝ (qq.2.1 - qq.1.1) qq.1.2| < 26 * r ∧
      (dist qq.2.2 qq.1.2 ≤ 2 * r ∨ dist qq.2.2 (-qq.1.2) ≤ 2 * r))
    {p p' : E2} (hp' : p' ∈ P) :
    (((G.filter (fun qq => qq.1.1 = p)).filter (fun qq => qq.2.1 = p')).card : ℝ) ≤
      4 * r ^ (-η) *
        (((bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r)).card : ℝ) := by
  have h1 : (((G.filter (fun qq => qq.1.1 = p)).filter (fun qq => qq.2.1 = p')).card : ℝ) ≤
      ∑ _e ∈ (bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r), 4 * r ^ (-η) := by
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
      refine le_trans ?_ (fcls_card_B h hs0 hs1 hp' he1)
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
theorem fcls_row (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s < 1) (hr : r ≤ 1 / 100)
    (hd : r ≤ d)
    (hG : ∀ qq ∈ G, qq.1 ∈ D ∧ qq.2 ∈ D ∧ dist qq.1.1 qq.2.1 < d ∧
      |inner ℝ (qq.2.1 - qq.1.1) qq.1.2| < 26 * r ∧
      (dist qq.2.2 qq.1.2 ≤ 2 * r ∨ dist qq.2.2 (-qq.1.2) ≤ 2 * r))
    {p : E2} (hp : p ∈ P) :
    ((G.filter (fun qq => qq.1.1 = p)).card : ℝ) ≤
      4 * r ^ (-η) * (r ^ (-η) * (2 / r) ^ s +
        2 * r ^ (-η) * ((52 : ℝ) ^ s *
          ((r ^ (-η) / r) * d * (d / 2) ^ (-s) / (1 - (1 / 2 : ℝ) ^ (1 - s))))) := by
  have hr0 := h.r_pos
  have hX : 0 ≤ r ^ (-η) := Real.rpow_nonneg hr0.le _
  have hb : 0 ≤ (52 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) _
  set N := P.filter (fun p' => dist p p' < d) with hN
  have hpN : p ∈ N := Finset.mem_filter.mpr ⟨hp, by rw [dist_self]; linarith⟩
  have h1 : ((G.filter (fun qq => qq.1.1 = p)).card : ℝ) ≤
      ∑ p' ∈ N, 4 * r ^ (-η) *
        (((bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r)).card : ℝ) := by
    apply cls_card_le_sum (g := fun qq => qq.2.1)
    · intro qq hqq
      rw [Finset.mem_filter] at hqq
      obtain ⟨-, hq2, hdist, -, -⟩ := hG qq hqq.1
      refine Finset.mem_filter.mpr ⟨(h.D_mem _ hq2).1, ?_⟩
      rw [← hqq.2]
      exact hdist
    · intro p' hp'
      exact fcls_cell h hs0 hs1.le hG (Finset.mem_filter.mp hp').1
  rw [← Finset.add_sum_erase N _ hpN] at h1
  have hdiag : 4 * r ^ (-η) *
      (((bushOf D p).filter (fun e => |inner ℝ (p - p) e| < 26 * r)).card : ℝ) ≤
      4 * r ^ (-η) * (r ^ (-η) * (2 / r) ^ s) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (fcls_card_bush h hr hp)
  have hoff : ∑ p' ∈ N.erase p, 4 * r ^ (-η) *
        (((bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r)).card : ℝ) ≤
      4 * r ^ (-η) * (2 * r ^ (-η) * ((52 : ℝ) ^ s *
        ∑ p' ∈ N.erase p, (dist p' p) ^ (-s))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p' hp'
    have hp'P : p' ∈ P := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp')).1
    exact mul_le_mul_of_nonneg_left (fcls_card_strip h hp hp'P (Finset.ne_of_mem_erase hp'))
      (by positivity)
  have hen := fcls_energy h hs0 hs1 hp hd
  have hen' : 4 * r ^ (-η) * (2 * r ^ (-η) * ((52 : ℝ) ^ s *
        ∑ p' ∈ N.erase p, (dist p' p) ^ (-s))) ≤
      4 * r ^ (-η) * (2 * r ^ (-η) * ((52 : ℝ) ^ s *
        ((r ^ (-η) / r) * d * (d / 2) ^ (-s) / (1 - (1 / 2 : ℝ) ^ (1 - s))))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hen hb
  linarith

theorem fcls_numeric {r s d X : ℝ} (hr : 0 < r) (hrd : r ≤ d) (hX : 1 ≤ X)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    X * (8 / r) * (4 * X * (X * (2 / r) ^ s +
        2 * X * ((52 : ℝ) ^ s * ((X / r) * d * (d / 2) ^ (-s) /
          (1 - (1 / 2 : ℝ) ^ (1 - s)))))) ≤
      10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) * (X ^ 4 / r ^ 2) * d ^ (1 - s) := by
  have hd : 0 < d := lt_of_lt_of_le hr hrd
  have hq : (1 / 2 : ℝ) ^ (1 - s) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (1 - s) := Real.rpow_nonneg (by norm_num) _
  set q := (1 / 2 : ℝ) ^ (1 - s) with hqdef
  have hden : 0 < 1 - q := by linarith
  have hX0 : 0 < X := by linarith
  -- the pieces
  have h2s : (2 : ℝ) ^ s ≤ 2 := fcls_two_rpow_le hs0 hs1.le
  have h52s : (52 : ℝ) ^ s ≤ 52 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 52) hs1.le
  have h2s0 : 0 ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) _
  have h52s0 : 0 ≤ (52 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) _
  have hds : d * (d / 2) ^ (-s) = (2 : ℝ) ^ s * d ^ (1 - s) := by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hd.le (by norm_num),
      Real.rpow_sub hd, Real.rpow_one]
    field_simp
  have hrs : (2 / r) ^ s = (2 : ℝ) ^ s * r ^ (-s) := by
    rw [Real.div_rpow (by norm_num) hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
  -- r ^ (-s) * r ≤ d ^ (1 - s)
  have hr1s : r ^ (1 - s) ≤ d ^ (1 - s) := Real.rpow_le_rpow hr.le hrd (by linarith)
  have hrr : r ^ (-s) = r ^ (1 - s) / r := by
    rw [Real.rpow_sub hr, Real.rpow_one, Real.rpow_neg hr.le]
    field_simp
  have hd1s : 0 ≤ d ^ (1 - s) := Real.rpow_nonneg hd.le _
  have hX34 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
  have hX3 : 0 ≤ X ^ 3 := by positivity
  rw [hrs, hrr]
  have hrew : X * (8 / r) * (4 * X * (X * ((2 : ℝ) ^ s * (r ^ (1 - s) / r)) +
        2 * X * ((52 : ℝ) ^ s * ((X / r) * d * (d / 2) ^ (-s) / (1 - q))))) =
      (32 * X ^ 3 * (2 : ℝ) ^ s * r ^ (1 - s) +
        64 * X ^ 4 * (52 : ℝ) ^ s * (d * (d / 2) ^ (-s)) / (1 - q)) / r ^ 2 := by
    field_simp
    ring
  rw [hrew, hds]
  have hrhs : 10 ^ 4 / (1 - q) * (X ^ 4 / r ^ 2) * d ^ (1 - s) =
      (10 ^ 4 * X ^ 4 * d ^ (1 - s) / (1 - q)) / r ^ 2 := by
    field_simp
  rw [hrhs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  -- first term
  have hq1 : 1 ≤ 1 / (1 - q) := by
    rw [le_div_iff₀ hden]; linarith
  have ht1 : 32 * X ^ 3 * (2 : ℝ) ^ s * r ^ (1 - s) ≤ 64 * X ^ 4 * d ^ (1 - s) / (1 - q) := by
    have hA : 32 * X ^ 3 * (2 : ℝ) ^ s * r ^ (1 - s) ≤ 64 * X ^ 4 * d ^ (1 - s) := by
      have : X ^ 3 * (2 : ℝ) ^ s * r ^ (1 - s) ≤ X ^ 4 * 2 * d ^ (1 - s) := by
        apply mul_le_mul _ hr1s (Real.rpow_nonneg hr.le _) (by positivity)
        exact mul_le_mul hX34 h2s h2s0 (by positivity)
      nlinarith
    calc 32 * X ^ 3 * (2 : ℝ) ^ s * r ^ (1 - s) ≤ 64 * X ^ 4 * d ^ (1 - s) := hA
      _ = 64 * X ^ 4 * d ^ (1 - s) * 1 := by ring
      _ ≤ 64 * X ^ 4 * d ^ (1 - s) * (1 / (1 - q)) :=
          mul_le_mul_of_nonneg_left hq1 (by positivity)
      _ = 64 * X ^ 4 * d ^ (1 - s) / (1 - q) := by ring
  have ht2 : 64 * X ^ 4 * (52 : ℝ) ^ s * ((2 : ℝ) ^ s * d ^ (1 - s)) / (1 - q) ≤
      6656 * X ^ 4 * d ^ (1 - s) / (1 - q) := by
    apply div_le_div_of_nonneg_right _ hden.le
    have h1 : (52 : ℝ) ^ s * (2 : ℝ) ^ s ≤ 104 := by nlinarith
    have hX4 : 0 ≤ X ^ 4 * d ^ (1 - s) := by positivity
    nlinarith
  have hsum : 64 * X ^ 4 * d ^ (1 - s) / (1 - q) + 6656 * X ^ 4 * d ^ (1 - s) / (1 - q) ≤
      10 ^ 4 * X ^ 4 * d ^ (1 - s) / (1 - q) := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hden.le
    have hX4 : 0 ≤ X ^ 4 * d ^ (1 - s) := by positivity
    nlinarith
  linarith

theorem fcls_upper (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s < 1) (hr : r ≤ 1 / 100)
    (hη : 0 < η) (hd : r ≤ d)
    (hG : ∀ qq ∈ G, qq.1 ∈ D ∧ qq.2 ∈ D ∧ dist qq.1.1 qq.2.1 < d ∧
      |inner ℝ (qq.2.1 - qq.1.1) qq.1.2| < 26 * r ∧
      (dist qq.2.2 qq.1.2 ≤ 2 * r ∨ dist qq.2.2 (-qq.1.2) ≤ 2 * r)) :
    (G.card : ℝ) ≤
      10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) * r ^ (-2 - 4 * η) * d ^ (1 - s) := by
  have hr0 := h.r_pos
  have hd0 : 0 < d := lt_of_lt_of_le hr0 hd
  have hX1 : 1 ≤ r ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 (by linarith) (by linarith)
  have hX0 : 0 ≤ r ^ (-η) := by linarith
  have hq : (1 / 2 : ℝ) ^ (1 - s) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hb : 0 ≤ (52 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) _
  set K := 4 * r ^ (-η) * (r ^ (-η) * (2 / r) ^ s +
    2 * r ^ (-η) * ((52 : ℝ) ^ s *
      ((r ^ (-η) / r) * d * (d / 2) ^ (-s) / (1 - (1 / 2 : ℝ) ^ (1 - s))))) with hK
  have h1 : (G.card : ℝ) ≤ ∑ _p ∈ P, K := by
    apply cls_card_le_sum (g := fun qq => qq.1.1) (fun qq hqq => (h.D_mem _ (hG qq hqq).1).1)
    intro p hp
    exact fcls_row h hs0 hs1 hr hd hG hp
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hP := fcls_card_P h (by linarith)
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ (1 - s) := by linarith
  have hK0 : 0 ≤ K := by positivity
  rw [cls_rpow_split hr0]
  calc (G.card : ℝ) ≤ (P.card : ℝ) * K := h1
    _ ≤ r ^ (-η) * (8 / r) * K := mul_le_mul_of_nonneg_right hP hK0
    _ ≤ 10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) * ((r ^ (-η)) ^ 4 / r ^ 2) * d ^ (1 - s) :=
        fcls_numeric hr0 hd hX1 hs0 hs1

end Upper

/-! ### The theorem -/

/-- `HalfData.classes` at a general exponent `0 ≤ s < 1`. -/
theorem FailData.classes {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s < 1) (hr : r ≤ 1 / 100)
    (hη : 0 < η) :
    ∃ (J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2),
      J₀ ⊆ D ∧ (J₀.card : ℝ) < r ^ (-(2 * s) - ε₀) ∧
      (∀ q ∈ D, cls q ∈ J₀) ∧
      (∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r)) ∧
      r ^ (4 * η + ε₀ - 2) ≤ ((sameClass D cls).card : ℝ) ∧
      ∀ d : ℝ, r ≤ d →
        (((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < d)).card : ℝ) ≤
          10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) * r ^ (-2 - 4 * η) * d ^ (1 - s) := by
  obtain ⟨J₀, cls, hJD, hJcard, hcls, hgeo⟩ := fcls_exists h
  refine ⟨J₀, cls, hJD, hJcard, hcls, hgeo, fcls_lower h J₀ cls hJcard hcls, ?_⟩
  intro d hd
  apply fcls_upper h hs0 hs1 hr hη hd
  intro qq hqq
  exact cls_mem_pairs (fun q hq => h.P_norm _ (h.D_mem q hq).1) hgeo hqq

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
