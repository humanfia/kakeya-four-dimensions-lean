-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.SharedArcs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/SharedArcs.lean (c61cafd).
-- Adapted from local obligation o157, branch x0675, commit 5a2c82ba2c9f.
-- Source: High/SharedArcs.lean. Shared half definitions imported from accepted o213.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeLines
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WideIncidence

/-!
# Coarse tubes, their number, and the coarse tubes met by a cell

* `exists_coarse_tubes` (A1): a maximal `StripSep ρ` subfamily `J₁` of the lines `J₀`, and an
  assignment `tb` of every line to a tube of `J₁` near it.
* `tube_count` (A3): if every occupied tube holds `≳ m ^ 2` lines (`tube_lines_quadratic`),
  the number of occupied tubes is `≲ #lines / m ^ 2`, since the tubes partition the lines.
* `cell_tubes_bound` (A4): points `Y` (one per cell), normalized 1-Frostman at scale `ρ`, each
  within `20 ρ` of at least `B` tubes of a `StripSep ρ` family `T`, have
  `B ^ 2 ≲ log (1/ρ) #T` (x0563's `wide_strip_incidence_bound`).
Together (x0665, 2026-10-13T12:26Z, steps (1)-(2)): the coarse tubes met by a cell are at
most `r ^ (-O(ε))` times those met by one of its pins.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

attribute [local instance] Classical.propDecidable

/-- A1: coarse tubes at scale `ρ` for a family of lines. -/
theorem exists_coarse_tubes (J₀ : Finset (E2 × E2)) (hJ₀ : ∀ ℓ ∈ J₀, ‖ℓ.1‖ ≤ 4)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (J₁ : Finset (E2 × E2)) (tb : E2 × E2 → E2 × E2), J₁ ⊆ J₀ ∧
      (∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep ρ x y) ∧
      (∀ ℓ ∈ J₀, tb ℓ ∈ J₁) ∧
      (∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tb ℓ).1) (tb ℓ).2| < 9 * ρ ∧
        (dist ℓ.2 (tb ℓ).2 < ρ ∨ dist ℓ.2 (-(tb ℓ).2) < ρ)) := by
  classical
  obtain ⟨J, hJD, hJpair, hJmax⟩ := exists_maximal_pairwise J₀ (StripSep ρ)
  have hch : ∀ ℓ : E2 × E2, ∃ j : E2 × E2,
      ℓ ∈ J₀ → j ∈ J ∧ (ℓ = j ∨ ¬ StripSep ρ ℓ j ∨ ¬ StripSep ρ j ℓ) := by
    intro ℓ
    by_cases hℓ : ℓ ∈ J₀
    · by_cases hℓJ : ℓ ∈ J
      · exact ⟨ℓ, fun _ => ⟨hℓJ, Or.inl rfl⟩⟩
      · obtain ⟨j, hj, hj'⟩ := hJmax ℓ hℓ hℓJ
        exact ⟨j, fun _ => ⟨hj, Or.inr hj'⟩⟩
    · exact ⟨ℓ, fun h' => absurd h' hℓ⟩
  choose tb htb using hch
  refine ⟨J, tb, hJD, hJpair, fun ℓ hℓ => (htb ℓ hℓ).1, ?_⟩
  intro ℓ hℓ
  have hj := htb ℓ hℓ
  exact near_of_not_stripSep (hJ₀ ℓ hℓ) (hJ₀ _ (hJD hj.1)) hj.2 hρ

/-- A3: the occupied tubes number at most `C #lines / m ^ 2`. -/
theorem tube_count {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2} {C m : ℝ}
    (hC : 0 ≤ C)
    (hquad : ∀ q₀ ∈ S, m ^ 2 ≤
      C * ((S.filter (fun q => tb (cls q) = tb (cls q₀))).image cls).card) :
    ((S.image (fun q => tb (cls q))).card : ℝ) * m ^ 2 ≤ C * (S.image cls).card := by
  classical
  set T := S.image (fun q => tb (cls q)) with hT
  have hpart : ((S.image cls).card : ℝ) =
      ∑ j ∈ T, (((S.image cls).filter (fun ℓ => tb ℓ = j)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := tb) (s := S.image cls) (t := T)
      (fun ℓ hℓ => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
        exact Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    exact_mod_cast this
  have hfib : ∀ q₀ ∈ S, ((S.filter (fun q => tb (cls q) = tb (cls q₀))).image cls) =
      (S.image cls).filter (fun ℓ => tb ℓ = tb (cls q₀)) := by
    intro q₀ _
    ext ℓ
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨q, ⟨hq, hqj⟩, rfl⟩; exact ⟨⟨q, hq, rfl⟩, hqj⟩
    · rintro ⟨⟨q, hq, rfl⟩, hqj⟩; exact ⟨q, ⟨hq, hqj⟩, rfl⟩
  calc (T.card : ℝ) * m ^ 2 = ∑ _j ∈ T, m ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ T, C * (((S.image cls).filter (fun ℓ => tb ℓ = j)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hj
        have h := hquad q₀ hq₀
        rwa [hfib q₀ hq₀] at h
    _ = C * (S.image cls).card := by rw [← Finset.mul_sum, ← hpart]

/-- A4: points each within `w` of at least `B` tubes of a `StripSep ρ` family, `ρ ≤ w ≤ 1/2`. -/
theorem cell_tubes_bound {ρ w C B : ℝ} (hρ : 0 < ρ) (hρw : ρ ≤ w) (hw2 : w ≤ 1 / 2) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (Y : Finset E2) (hYne : Y.Nonempty) (hY4 : ∀ y ∈ Y, ‖y‖ ≤ 4)
    (hFr : ∀ (x : E2) (t : ℝ), ρ ≤ t →
      ((Y.filter (fun z => z ∈ Metric.closedBall x t)).card : ℝ) ≤ C * t * Y.card)
    (T : Finset (E2 × E2)) (hT : ∀ j ∈ T, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → StripSep ρ x y)
    (K : ℕ) (hK : (Y.card : ℝ) ≤ (2 : ℝ) ^ K)
    (hinc : ∀ y ∈ Y, B ≤ ((T.filter (fun j => |inner ℝ (y - j.1) j.2| < w)).card : ℝ)) :
    B ^ 2 ≤ 128000 * (64 * w / ρ + 2) * (36 * w / ρ + 2) *
      C * (1 + Real.log (1 / w)) * (K + 1) ^ 2 * T.card := by
  classical
  have hsum : B * Y.card ≤ ∑ j ∈ T,
      ((Y.filter (fun y => |inner ℝ (y - j.1) j.2| < w)).card : ℝ) := by
    have hswap : ∑ j ∈ T, ((Y.filter (fun y => |inner ℝ (y - j.1) j.2| < w)).card : ℝ) =
        ∑ y ∈ Y, ((T.filter (fun j => |inner ℝ (y - j.1) j.2| < w)).card : ℝ) := by
      simp only [Finset.card_filter]
      push_cast
      exact Finset.sum_comm
    rw [hswap]
    calc B * Y.card = ∑ _y ∈ Y, B := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hinc
  have hsep' : (T : Set (E2 × E2)).Pairwise
      (WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep ρ) :=
    fun x hx y hy hne => hsep x hx y hy hne
  exact wide_strip_incidence_bound hρ hρw hw2 hC hB Y hYne hY4 hFr T hT hsep' K hK hsum

/-- A pin with a label of class `ℓ`, where `ℓ` is assigned to the tube `j`, lies within
`9 r + 17 ρ` of the central line of `j`. -/
theorem pin_near_tube {q ℓ j : E2 × E2} {r ρ : ℝ} (hq4 : ‖q.1‖ ≤ 4) (hℓ4 : ‖ℓ.1‖ ≤ 4)
    (hℓ1 : ‖ℓ.2‖ = 1) (hj1 : ‖j.2‖ = 1)
    (hqℓ : |inner ℝ (q.1 - ℓ.1) ℓ.2| < 9 * r)
    (hℓj : |inner ℝ (ℓ.1 - j.1) j.2| < 9 * ρ) (hn : dist ℓ.2 j.2 < ρ ∨ dist ℓ.2 (-j.2) < ρ) :
    |inner ℝ (q.1 - j.1) j.2| < 9 * r + 17 * ρ := by
  have h8 : ‖q.1 - ℓ.1‖ ≤ 8 := norm_le_eight_of_norm_le_four hq4 hℓ4
  have hsplit : inner ℝ (q.1 - j.1) j.2 = inner ℝ (q.1 - ℓ.1) j.2 + inner ℝ (ℓ.1 - j.1) j.2 := by
    rw [← inner_add_left]; congr 1; abel
  -- the first term: compare `j.2` with `± ℓ.2`
  have hfirst : |inner ℝ (q.1 - ℓ.1) j.2| < 9 * r + 8 * ρ := by
    rcases hn with hp | hm
    · have hd : ‖j.2 - ℓ.2‖ < ρ := by rw [← dist_eq_norm, dist_comm]; exact hp
      have e1 : inner ℝ (q.1 - ℓ.1) j.2 =
          inner ℝ (q.1 - ℓ.1) ℓ.2 + inner ℝ (q.1 - ℓ.1) (j.2 - ℓ.2) := by
        rw [← inner_add_right]; congr 1; abel
      have e2 : |inner ℝ (q.1 - ℓ.1) (j.2 - ℓ.2)| ≤ ‖q.1 - ℓ.1‖ * ‖j.2 - ℓ.2‖ :=
        abs_real_inner_le_norm _ _
      have e3 : ‖q.1 - ℓ.1‖ * ‖j.2 - ℓ.2‖ ≤ 8 * ρ := by
        have := mul_le_mul h8 hd.le (norm_nonneg _) (by norm_num)
        linarith
      rw [e1]
      calc |inner ℝ (q.1 - ℓ.1) ℓ.2 + inner ℝ (q.1 - ℓ.1) (j.2 - ℓ.2)|
          ≤ |inner ℝ (q.1 - ℓ.1) ℓ.2| + |inner ℝ (q.1 - ℓ.1) (j.2 - ℓ.2)| := abs_add_le _ _
        _ < 9 * r + 8 * ρ := by linarith
    · have hd : ‖j.2 + ℓ.2‖ < ρ := by
        have : dist ℓ.2 (-j.2) = ‖j.2 + ℓ.2‖ := by
          rw [dist_eq_norm, sub_neg_eq_add, add_comm]
        rw [← this]; exact hm
      have e1 : inner ℝ (q.1 - ℓ.1) j.2 =
          -inner ℝ (q.1 - ℓ.1) ℓ.2 + inner ℝ (q.1 - ℓ.1) (j.2 + ℓ.2) := by
        rw [inner_add_right]; ring
      have e2 : |inner ℝ (q.1 - ℓ.1) (j.2 + ℓ.2)| ≤ ‖q.1 - ℓ.1‖ * ‖j.2 + ℓ.2‖ :=
        abs_real_inner_le_norm _ _
      have e3 : ‖q.1 - ℓ.1‖ * ‖j.2 + ℓ.2‖ ≤ 8 * ρ := by
        have := mul_le_mul h8 hd.le (norm_nonneg _) (by norm_num)
        linarith
      rw [e1]
      calc |-inner ℝ (q.1 - ℓ.1) ℓ.2 + inner ℝ (q.1 - ℓ.1) (j.2 + ℓ.2)|
          ≤ |-inner ℝ (q.1 - ℓ.1) ℓ.2| + |inner ℝ (q.1 - ℓ.1) (j.2 + ℓ.2)| := abs_add_le _ _
        _ = |inner ℝ (q.1 - ℓ.1) ℓ.2| + |inner ℝ (q.1 - ℓ.1) (j.2 + ℓ.2)| := by rw [abs_neg]
        _ < 9 * r + 8 * ρ := by linarith
  rw [hsplit]
  calc |inner ℝ (q.1 - ℓ.1) j.2 + inner ℝ (ℓ.1 - j.1) j.2|
      ≤ |inner ℝ (q.1 - ℓ.1) j.2| + |inner ℝ (ℓ.1 - j.1) j.2| := abs_add_le _ _
    _ < 9 * r + 17 * ρ := by linarith

/-- Balanced labels per tube and per line make all occupied tubes hold comparably many
lines: each holds at most `K ^ 3` times the average. -/
theorem lines_per_tube_le {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2} {K : ℝ}
    (hK : 0 ≤ K)
    (htube : ∀ q ∈ S, ∀ q' ∈ S, ((S.filter (fun a => tb (cls a) = tb (cls q))).card : ℝ) ≤
      K * (S.filter (fun a => tb (cls a) = tb (cls q'))).card)
    (hline : ∀ q ∈ S, ∀ q' ∈ S, ((S.filter (fun a => cls a = cls q)).card : ℝ) ≤
      K * (S.filter (fun a => cls a = cls q')).card)
    {q₀ : E2 × E2} (hq₀ : q₀ ∈ S) :
    (((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card : ℝ) *
        (S.image (fun a => tb (cls a))).card ≤
      K ^ 3 * (S.image cls).card := by
  classical
  have hkpos : (0 : ℝ) < ((S.filter (fun a => cls a = cls q₀)).card : ℝ) := by
    have hmem : q₀ ∈ S.filter (fun a => cls a = cls q₀) := Finset.mem_filter.mpr ⟨hq₀, rfl⟩
    have := Finset.card_pos.mpr ⟨q₀, hmem⟩
    exact_mod_cast this
  -- labels of a tube as a sum over its lines
  have hsum : ∀ j : E2 × E2, ((S.filter (fun a => tb (cls a) = j)).card : ℝ) =
      ∑ ℓ ∈ (S.filter (fun a => tb (cls a) = j)).image cls,
        (((S.filter (fun a => tb (cls a) = j)).filter (fun a => cls a = ℓ)).card : ℝ) := by
    intro j
    have := Finset.card_eq_sum_card_fiberwise (f := cls)
      (s := S.filter (fun a => tb (cls a) = j))
      (t := (S.filter (fun a => tb (cls a) = j)).image cls)
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    rw [this]
    push_cast
    rfl
  -- a line of the tube `j` has all its labels in `j`
  have hfibeq : ∀ j : E2 × E2, ∀ a ∈ S.filter (fun a => tb (cls a) = j),
      (S.filter (fun a' => tb (cls a') = j)).filter (fun a' => cls a' = cls a) =
        S.filter (fun a' => cls a' = cls a) := by
    intro j a ha
    have haj : tb (cls a) = j := (Finset.mem_filter.mp ha).2
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, _⟩, hxc⟩; exact ⟨hx, hxc⟩
    · rintro ⟨hx, hxc⟩; exact ⟨⟨hx, by rw [hxc, haj]⟩, hxc⟩
  set k : ℝ := ((S.filter (fun a => cls a = cls q₀)).card : ℝ) with hk
  have hNlow : ∀ j : E2 × E2, ((S.filter (fun a => tb (cls a) = j)).card : ℝ) ≤
      (((S.filter (fun a => tb (cls a) = j)).image cls).card : ℝ) * (K * k) := by
    intro j
    rw [hsum j]
    calc ∑ ℓ ∈ (S.filter (fun a => tb (cls a) = j)).image cls,
          (((S.filter (fun a => tb (cls a) = j)).filter (fun a => cls a = ℓ)).card : ℝ)
        ≤ ∑ _ℓ ∈ (S.filter (fun a => tb (cls a) = j)).image cls, K * k := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hℓ
          rw [hfibeq j a ha]
          exact hline a (Finset.mem_filter.mp ha).1 q₀ hq₀
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hNup : ∀ j : E2 × E2, (((S.filter (fun a => tb (cls a) = j)).image cls).card : ℝ) * k ≤
      K * ((S.filter (fun a => tb (cls a) = j)).card : ℝ) := by
    intro j
    rw [hsum j, Finset.mul_sum]
    calc (((S.filter (fun a => tb (cls a) = j)).image cls).card : ℝ) * k
        = ∑ _ℓ ∈ (S.filter (fun a => tb (cls a) = j)).image cls, k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hℓ
          rw [hfibeq j a ha]
          exact hline q₀ hq₀ a (Finset.mem_filter.mp ha).1
  set T := S.image (fun a => tb (cls a)) with hT
  have hpart : ((S.image cls).card : ℝ) =
      ∑ j ∈ T, (((S.filter (fun a => tb (cls a) = j)).image cls).card : ℝ) := by
    have hfib : ∀ j ∈ T, (S.image cls).filter (fun ℓ => tb ℓ = j) =
        (S.filter (fun a => tb (cls a) = j)).image cls := by
      intro j _
      ext ℓ
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hqj⟩; exact ⟨q, ⟨hq, hqj⟩, rfl⟩
      · rintro ⟨q, ⟨hq, hqj⟩, rfl⟩; exact ⟨⟨q, hq, rfl⟩, hqj⟩
    have := Finset.card_eq_sum_card_fiberwise (f := tb) (s := S.image cls) (t := T)
      (fun ℓ hℓ => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
        exact Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    rw [this]
    push_cast
    exact Finset.sum_congr rfl (fun j hj => by rw [hfib j hj])
  have hcmp : ∀ j ∈ T, (((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card : ℝ) ≤
      K ^ 3 * (((S.filter (fun a => tb (cls a) = j)).image cls).card : ℝ) := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    have h1 := hNup (tb (cls q₀))
    have h2 := htube q₀ hq₀ a ha
    have h3 := hNlow (tb (cls a))
    have h4 : (((S.filter (fun a' => tb (cls a') = tb (cls q₀))).image cls).card : ℝ) * k ≤
        (K ^ 3 * (((S.filter (fun a' => tb (cls a') = tb (cls a))).image cls).card : ℝ)) * k := by
      calc (((S.filter (fun a' => tb (cls a') = tb (cls q₀))).image cls).card : ℝ) * k
          ≤ K * ((S.filter (fun a' => tb (cls a') = tb (cls q₀))).card : ℝ) := h1
        _ ≤ K * (K * ((S.filter (fun a' => tb (cls a') = tb (cls a))).card : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 hK
        _ ≤ K * (K * ((((S.filter (fun a' => tb (cls a') = tb (cls a))).image cls).card : ℝ) *
              (K * k))) := by
            apply mul_le_mul_of_nonneg_left _ hK
            exact mul_le_mul_of_nonneg_left h3 hK
        _ = _ := by ring
    exact le_of_mul_le_mul_right h4 hkpos
  rw [hpart, Finset.mul_sum]
  calc (((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card : ℝ) * (T.card : ℝ)
      = ∑ _j ∈ T, (((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum hcmp

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
