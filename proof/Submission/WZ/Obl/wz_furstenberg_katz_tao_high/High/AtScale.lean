-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.AtScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/AtScale.lean (064b94b).
-- Adapted from local obligation o157, branch x0675, commit 197726a72f30.
-- Source: High/AtScale.lean. Own namespace renamed; shared definitions imported from accepted o213.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Regularize

/-!
# A failed bush estimate made regular at one scale `ρ`

`cellOf ρ x` is the `ρ`-grid square of a point and `arcOf ρ e` the `ρ`-grid square of a
unit normal (a `ρ`-arc up to a bounded factor). `RegularAt r s ε₀ η ρ K Q S` says that
`(Q, S)` is `FailData` and that at scale `ρ`
* all bushes have comparable sizes,
* all occupied cells hold comparably many pins,
* in every bush, all occupied arcs hold comparably many normals,
* all occupied (cell, arc) pairs carry comparably many labels,
each with ratio `K`. `exists_regularAt` produces it from `FailData`, losing `r ^ ε` of
the labels, with `K = r ^ (-3 ε)` and `η` replaced by `3 η + 2 ε`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- The `ρ`-grid square containing `x`. -/
noncomputable def cellOf (ρ : ℝ) (x : E2) : ℤ × ℤ := (⌊x 0 / ρ⌋, ⌊x 1 / ρ⌋)

/-- The `ρ`-grid square containing the normal `e` (an arc of length `≍ ρ`). -/
noncomputable def arcOf (ρ : ℝ) (e : E2) : ℤ × ℤ := (⌊e 0 / ρ⌋, ⌊e 1 / ρ⌋)

theorem abs_sub_lt_of_floor_eq {ρ a b : ℝ} (hρ : 0 < ρ) (h : ⌊a / ρ⌋ = ⌊b / ρ⌋) :
    |a - b| < ρ := by
  have ha1 := Int.floor_le (a / ρ)
  have ha2 := Int.lt_floor_add_one (a / ρ)
  have hb1 := Int.floor_le (b / ρ)
  have hb2 := Int.lt_floor_add_one (b / ρ)
  rw [h] at ha1 ha2
  have h1 : a / ρ - b / ρ < 1 := by linarith
  have h2 : b / ρ - a / ρ < 1 := by linarith
  rw [abs_lt]
  constructor
  · have : (b - a) / ρ < 1 := by rw [sub_div]; exact h2
    rw [div_lt_one hρ] at this; linarith
  · have : (a - b) / ρ < 1 := by rw [sub_div]; exact h1
    rwa [div_lt_one hρ] at this

/-- Two points of the same `ρ`-square are within `2 ρ`. -/
theorem dist_le_of_cellOf_eq {ρ : ℝ} (hρ : 0 < ρ) {x y : E2}
    (h : cellOf ρ x = cellOf ρ y) : dist x y ≤ 2 * ρ := by
  have h0 : |x 0 - y 0| < ρ := abs_sub_lt_of_floor_eq hρ (Prod.ext_iff.mp h).1
  have h1 : |x 1 - y 1| < ρ := abs_sub_lt_of_floor_eq hρ (Prod.ext_iff.mp h).2
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
  rw [Real.sqrt_le_left (by positivity)]
  have e0 : |x 0 - y 0| ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h0.le 2
  have e1 : |x 1 - y 1| ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1.le 2
  nlinarith

/-- Two normals of the same `ρ`-square are within `2 ρ`. -/
theorem dist_le_of_arcOf_eq {ρ : ℝ} (hρ : 0 < ρ) {e f : E2}
    (h : arcOf ρ e = arcOf ρ f) : dist e f ≤ 2 * ρ :=
  dist_le_of_cellOf_eq hρ h

/-- The pins of `Q` in the cell of `p`. -/
noncomputable def cellPins (ρ : ℝ) (Q : Finset E2) (p : E2) : Finset E2 :=
  Q.filter (fun x => cellOf ρ x = cellOf ρ p)

/-- The normals of the bush of `p` in the arc of `e`. -/
noncomputable def arcNormals (ρ : ℝ) (S : Finset (E2 × E2)) (p e : E2) : Finset E2 :=
  (bushOf S p).filter (fun f => arcOf ρ f = arcOf ρ e)

/-- The labels with pin in the cell of `q.1` and normal in the arc of `q.2`. -/
noncomputable def cellArcLabels (ρ : ℝ) (S : Finset (E2 × E2)) (q : E2 × E2) :
    Finset (E2 × E2) :=
  S.filter (fun q' => cellOf ρ q'.1 = cellOf ρ q.1 ∧ arcOf ρ q'.2 = arcOf ρ q.2)

/-- A failed bush estimate that is regular at the scale `ρ`, with ratio `K`. -/
structure RegularAt (r s ε₀ η ρ K : ℝ) (Q : Finset E2) (S : Finset (E2 × E2)) : Prop where
  fail : FailData r s ε₀ η Q S
  bush_bal : ∀ p ∈ Q, ∀ p' ∈ Q, ((bushOf S p).card : ℝ) ≤ K * (bushOf S p').card
  cell_bal : ∀ p ∈ Q, ∀ p' ∈ Q,
    ((cellPins ρ Q p).card : ℝ) ≤ K * (cellPins ρ Q p').card
  arc_bal : ∀ q ∈ S, ∀ q' ∈ S,
    ((arcNormals ρ S q.1 q.2).card : ℝ) ≤ K * (arcNormals ρ S q'.1 q'.2).card
  cellArc_bal : ∀ q ∈ S, ∀ q' ∈ S,
    ((cellArcLabels ρ S q).card : ℝ) ≤ K * (cellArcLabels ρ S q').card

/-- The three scale-`ρ` label maps: cell of the pin, (pin, arc), (cell, arc). -/
noncomputable def scaleMaps (ρ : ℝ) : ∀ i : Fin 3, E2 × E2 →
    (![ℤ × ℤ, E2 × (ℤ × ℤ), (ℤ × ℤ) × (ℤ × ℤ)] i)
  | 0 => fun q => cellOf ρ q.1
  | 1 => fun q => (q.1, arcOf ρ q.2)
  | 2 => fun q => (cellOf ρ q.1, arcOf ρ q.2)

noncomputable scoped instance scaleMaps.decEq :
    ∀ i : Fin 3, DecidableEq (![ℤ × ℤ, E2 × (ℤ × ℤ), (ℤ × ℤ) × (ℤ × ℤ)] i)
  | 0 => inferInstanceAs (DecidableEq (ℤ × ℤ))
  | 1 => inferInstanceAs (DecidableEq (E2 × (ℤ × ℤ)))
  | 2 => inferInstanceAs (DecidableEq ((ℤ × ℤ) × (ℤ × ℤ)))

/-- Labels whose pin lies in the cell of `p`. -/
theorem cell_labels_eq_sum (ρ : ℝ) {Q : Finset E2} {S : Finset (E2 × E2)}
    (hS : ∀ q ∈ S, q.1 ∈ Q) (p : E2) :
    ((S.filter (fun q => cellOf ρ q.1 = cellOf ρ p)).card : ℝ) =
      ∑ x ∈ cellPins ρ Q p, ((bushOf S x).card : ℝ) := by
  classical
  have hsub : ∀ q ∈ S.filter (fun q => cellOf ρ q.1 = cellOf ρ p), q.1 ∈ cellPins ρ Q p := by
    intro q hq
    obtain ⟨hqS, hqc⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hS q hqS, hqc⟩
  rw [card_eq_sum_bushOf hsub]
  apply Finset.sum_congr rfl
  intro x hx
  have hxc := (Finset.mem_filter.mp hx).2
  congr 2
  ext e
  simp only [mem_bushOf, Finset.mem_filter]
  constructor
  · rintro ⟨h1, _⟩; exact h1
  · intro h1; exact ⟨h1, hxc⟩

/-- Membership in a fiber of a partition map. -/
theorem mem_leafFiber' {α β : Type*} [DecidableEq α] {S : Finset α} {f : α → β} {x a : α} :
    a ∈ leafFiber S f x ↔ a ∈ S ∧ f a = f x := by
  classical
  unfold leafFiber
  exact Finset.mem_filter

/-- Labels over `p` with normal in the arc of `e`, counted as normals. -/
theorem card_arc_fiber (ρ : ℝ) (S : Finset (E2 × E2)) (p e : E2) :
    (S.filter (fun a => a.1 = p ∧ arcOf ρ a.2 = arcOf ρ e)).card =
      (arcNormals ρ S p e).card := by
  classical
  have himg : (S.filter (fun a => a.1 = p ∧ arcOf ρ a.2 = arcOf ρ e)).image Prod.snd =
      arcNormals ρ S p e := by
    ext f
    simp only [Finset.mem_image, Finset.mem_filter, arcNormals, mem_bushOf]
    constructor
    · rintro ⟨a, ⟨haS, ha1, ha2⟩, rfl⟩
      refine ⟨?_, ha2⟩
      rw [show a = (p, a.2) from Prod.ext ha1 rfl] at haS
      exact haS
    · rintro ⟨hf, hfa⟩
      exact ⟨(p, f), ⟨hf, rfl, hfa⟩, rfl⟩
  rw [← himg, Finset.card_image_of_injOn]
  intro a ha b hb hab
  have ha1 := (Finset.mem_filter.mp ha).2.1
  have hb1 := (Finset.mem_filter.mp hb).2.1
  exact Prod.ext (ha1.trans hb1.symm) hab

theorem exists_regularAt (s ε : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 2 ∧ ∀ r ε₀ η ρ : ℝ, r ≤ r₀ → 0 ≤ η → η ≤ 1 →
      ∀ (P : Finset E2) (D : Finset (E2 × E2)), FailData r s ε₀ η P D →
        ∃ S ⊆ D, r ^ ε * (D.card : ℝ) ≤ S.card ∧
          RegularAt r s ε₀ (3 * η + 2 * ε) ρ (r ^ (-3 * ε)) (S.image Prod.fst) S := by
  classical
  obtain ⟨r₀, hr₀, hr₀h, hreg⟩ := FailData.regularize s ε hs0 hs1 hε 3
  refine ⟨r₀, hr₀, hr₀h, ?_⟩
  intro r ε₀ η ρ hrr₀ hη0 hη1 P D h
  have hr : 0 < r := h.r_pos
  have hr1 : r ≤ 1 := by linarith
  obtain ⟨S, hSD, hmass, hfail, hfst, hbal⟩ :=
    hreg r ε₀ η hrr₀ hη0 hη1 P D h (I := Fin 3) (Y := ![ℤ × ℤ, E2 × (ℤ × ℤ), (ℤ × ℤ) × (ℤ × ℤ)])
      (by simp) (scaleMaps ρ)
  refine ⟨S, hSD, hmass, ?_⟩
  set Q := S.image Prod.fst with hQ
  have hKmono : r ^ (-ε) ≤ r ^ (-3 * ε) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hK1 : (1 : ℝ) ≤ r ^ (-ε) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  have hKcube : r ^ (-ε) * r ^ (-ε) * r ^ (-ε) = r ^ (-3 * ε) := by
    rw [← Real.rpow_add hr, ← Real.rpow_add hr]; ring_nf
  have hSQ : ∀ q ∈ S, q.1 ∈ Q := fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩
  -- bushes
  have hbush : ∀ p ∈ Q, ∀ p' ∈ Q, ((bushOf S p).card : ℝ) ≤ r ^ (-ε) * (bushOf S p').card :=
    fun p hp p' hp' => bush_le_of_balanced hfst hp hp'
  refine ⟨hfail, fun p hp p' hp' => (hbush p hp p' hp').trans
    (mul_le_mul_of_nonneg_right hKmono (Nat.cast_nonneg _)), ?_, ?_, ?_⟩
  · -- pins per cell
    intro p hp p' hp'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hp'
    have hb0 := hbal 0 q hq q' hq'
    have hfib : ∀ x, leafFiber S (scaleMaps ρ 0) x =
        S.filter (fun a => cellOf ρ a.1 = cellOf ρ x.1) := by
      intro x; ext a; rw [mem_leafFiber', Finset.mem_filter]; rfl
    rw [hfib, hfib, cell_labels_eq_sum ρ hSQ, cell_labels_eq_sum ρ hSQ] at hb0
    -- bounds through the extreme bushes
    set b := ((bushOf S q.1).card : ℝ)
    have hlow : ∀ x ∈ Q, b ≤ r ^ (-ε) * (bushOf S x).card := fun x hx => hbush q.1 hp x hx
    have hup : ∀ x ∈ Q, ((bushOf S x).card : ℝ) ≤ r ^ (-ε) * b := fun x hx => hbush x hx q.1 hp
    have hcp : ∀ x ∈ cellPins ρ Q q.1, x ∈ Q := fun x hx => (Finset.mem_filter.mp hx).1
    have hcp' : ∀ x ∈ cellPins ρ Q q'.1, x ∈ Q := fun x hx => (Finset.mem_filter.mp hx).1
    have hA : ((cellPins ρ Q q.1).card : ℝ) * b ≤
        r ^ (-ε) * ∑ x ∈ cellPins ρ Q q.1, ((bushOf S x).card : ℝ) := by
      rw [Finset.mul_sum]
      calc ((cellPins ρ Q q.1).card : ℝ) * b = ∑ _x ∈ cellPins ρ Q q.1, b := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun x hx => hlow x (hcp x hx))
    have hB : ∑ x ∈ cellPins ρ Q q'.1, ((bushOf S x).card : ℝ) ≤
        ((cellPins ρ Q q'.1).card : ℝ) * (r ^ (-ε) * b) := by
      calc ∑ x ∈ cellPins ρ Q q'.1, ((bushOf S x).card : ℝ)
          ≤ ∑ _x ∈ cellPins ρ Q q'.1, r ^ (-ε) * b :=
            Finset.sum_le_sum (fun x hx => hup x (hcp' x hx))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hbpos : 0 < b := by
      have := hfail.D_card q.1 hp
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos hr _) this
    have key : ((cellPins ρ Q q.1).card : ℝ) * b ≤
        (r ^ (-ε) * r ^ (-ε) * r ^ (-ε)) * ((cellPins ρ Q q'.1).card : ℝ) * b := by
      calc ((cellPins ρ Q q.1).card : ℝ) * b
          ≤ r ^ (-ε) * ∑ x ∈ cellPins ρ Q q.1, ((bushOf S x).card : ℝ) := hA
        _ ≤ r ^ (-ε) * (r ^ (-ε) * ∑ x ∈ cellPins ρ Q q'.1, ((bushOf S x).card : ℝ)) :=
            mul_le_mul_of_nonneg_left hb0 (by positivity)
        _ ≤ r ^ (-ε) * (r ^ (-ε) * (((cellPins ρ Q q'.1).card : ℝ) * (r ^ (-ε) * b))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hB (by positivity)
        _ = _ := by ring
    have key' := le_of_mul_le_mul_right key hbpos
    rwa [hKcube] at key'
  · -- normals per arc of a bush
    intro q hq q' hq'
    have hb1 := hbal 1 q hq q' hq'
    have hfib : ∀ x, leafFiber S (scaleMaps ρ 1) x =
        S.filter (fun a => a.1 = x.1 ∧ arcOf ρ a.2 = arcOf ρ x.2) := by
      intro x; ext a; rw [mem_leafFiber', Finset.mem_filter]
      show a ∈ S ∧ ((a.1, arcOf ρ a.2) = (x.1, arcOf ρ x.2)) ↔ _
      rw [Prod.mk.injEq]
    rw [hfib, hfib, card_arc_fiber, card_arc_fiber] at hb1
    exact hb1.trans (mul_le_mul_of_nonneg_right hKmono (Nat.cast_nonneg _))
  · -- labels per (cell, arc)
    intro q hq q' hq'
    have hb2 := hbal 2 q hq q' hq'
    have hfib : ∀ x, leafFiber S (scaleMaps ρ 2) x = cellArcLabels ρ S x := by
      intro x; ext a; rw [mem_leafFiber', cellArcLabels, Finset.mem_filter]
      show a ∈ S ∧ ((cellOf ρ a.1, arcOf ρ a.2) = (cellOf ρ x.1, arcOf ρ x.2)) ↔ _
      rw [Prod.mk.injEq]
    rw [hfib, hfib] at hb2
    exact hb2.trans (mul_le_mul_of_nonneg_right hKmono (Nat.cast_nonneg _))

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
