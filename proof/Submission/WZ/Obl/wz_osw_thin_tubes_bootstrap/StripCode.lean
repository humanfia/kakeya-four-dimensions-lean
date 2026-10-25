-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.StripCode.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_thin_tubes_bootstrap.Geometry

/-!
# Few separated strips through a point

A strip is labelled by `(p, e)`, a point and a unit normal; it is
`{z | |⟪z - p, e⟫| < r}`.  Labels are `r`-separated (`StripSep r`) when their
normals differ by at least `r` (up to sign) or the second point is at distance
at least `r` from the line of the first.  Coding a label by the side of `rot u`
its normal lies on, the coordinate `⟪e, u⟫` at resolution `r / 32` and the offset
`⟪y - p, e⟫` at resolution `r / 2` is injective on separated labels whose strips
contain `y`; this bounds their number by the size of a box of codes.
-/

namespace WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap

/-- Separation of strip labels `(p, e)`. -/
def StripSep (r : ℝ) (x y : E2 × E2) : Prop :=
  (r ≤ dist x.2 y.2 ∧ r ≤ dist x.2 (-y.2)) ∨ r ≤ |inner ℝ (x.1 - y.1) x.2|

lemma floor_close {x x' s : ℝ} (hs : 0 < s) (h : ⌊x / s⌋ = ⌊x' / s⌋) : |x - x'| < s := by
  have h1 := Int.floor_le (x / s)
  have h2 := Int.lt_floor_add_one (x / s)
  have h3 := Int.floor_le (x' / s)
  have h4 := Int.lt_floor_add_one (x' / s)
  rw [h] at h1 h2
  have : |x / s - x' / s| < 1 := by rw [abs_sub_lt_iff]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hs, div_lt_one hs] at this
  exact this

/-- The code of a strip label relative to a frame `u` and a point `y`. -/
noncomputable def stripCode (u y : E2) (s s' : ℝ) (j : E2 × E2) : ℤ × ℤ × ℤ :=
  (if 0 ≤ inner ℝ j.2 (rot u) then 1 else 0, ⌊inner ℝ j.2 u / s⌋, ⌊inner ℝ (y - j.1) j.2 / s'⌋)

lemma stripCode_injOn {u y : E2} {r s s' : ℝ} (hu : ‖u‖ = 1) (hs : 0 < s) (hs' : 0 < s')
    (hss : s' + 16 * s ≤ r)
    {Jy : Set (E2 × E2)} (hsep : Jy.Pairwise (StripSep r))
    (hJ : ∀ j ∈ Jy, ‖j.2‖ = 1 ∧ ‖y - j.1‖ ≤ 8 ∧ (inner ℝ j.2 u) ^ 2 ≤ 1 / 2) :
    Set.InjOn (stripCode u y s s') Jy := by
  intro j hj j' hj' hcode
  by_contra hne
  have hS := hsep hj hj' hne
  obtain ⟨he, _, ha⟩ := hJ j hj
  obtain ⟨he', hy', ha'⟩ := hJ j' hj'
  simp only [stripCode, Prod.mk.injEq] at hcode
  obtain ⟨hsign, ha_eq, hc_eq⟩ := hcode
  have hb : 0 ≤ inner ℝ j.2 (rot u) * inner ℝ j'.2 (rot u) := by
    split_ifs at hsign with h1 h2 h2
    · exact mul_nonneg h1 h2
    · norm_num at hsign
    · norm_num at hsign
    · exact (mul_pos_of_neg_of_neg (not_le.mp h1) (not_le.mp h2)).le
  have hadiff := floor_close hs ha_eq
  have hcdiff := floor_close hs' hc_eq
  have hclose := frame_close hu he he' ha ha' hb
  have hee : ‖j.2 - j'.2‖ < 2 * s := by
    have h3 : (inner ℝ j.2 u - inner ℝ j'.2 u) ^ 2 < s ^ 2 := by
      have := abs_nonneg (inner ℝ j.2 u - inner ℝ j'.2 u)
      rw [← sq_abs]; nlinarith
    by_contra hcon
    have hcon' : 2 * s ≤ ‖j.2 - j'.2‖ := not_lt.mp hcon
    nlinarith [norm_nonneg (j.2 - j'.2)]
  have hkey : inner ℝ (j.1 - j'.1) j.2 = inner ℝ (y - j'.1) j'.2 - inner ℝ (y - j.1) j.2 +
      inner ℝ (y - j'.1) (j.2 - j'.2) := by
    simp only [inner_sub_left, inner_sub_right]; ring
  have hcross : |inner ℝ (y - j'.1) (j.2 - j'.2)| < 16 * s := by
    calc |inner ℝ (y - j'.1) (j.2 - j'.2)| ≤ ‖y - j'.1‖ * ‖j.2 - j'.2‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ 8 * ‖j.2 - j'.2‖ := mul_le_mul_of_nonneg_right hy' (norm_nonneg _)
      _ < 8 * (2 * s) := by linarith
      _ = 16 * s := by ring
  have hoff : |inner ℝ (j.1 - j'.1) j.2| < r := by
    rw [hkey]
    have h5 : |inner ℝ (y - j'.1) j'.2 - inner ℝ (y - j.1) j.2| < s' := by
      rw [abs_sub_comm]; exact hcdiff
    calc |inner ℝ (y - j'.1) j'.2 - inner ℝ (y - j.1) j.2 + inner ℝ (y - j'.1) (j.2 - j'.2)|
        ≤ |inner ℝ (y - j'.1) j'.2 - inner ℝ (y - j.1) j.2| +
          |inner ℝ (y - j'.1) (j.2 - j'.2)| := abs_add_le _ _
      _ < s' + 16 * s := add_lt_add h5 hcross
      _ ≤ r := hss
  have hdist : dist j.2 j'.2 < r := by rw [dist_eq_norm]; linarith
  rcases hS with ⟨h1, _⟩ | h2
  · linarith
  · linarith

lemma card_Icc_floor_le {x : ℝ} (hx : 0 ≤ x) :
    ((Finset.Icc ⌊-x⌋ ⌊x⌋).card : ℝ) ≤ 2 * x + 2 := by
  rw [Int.card_Icc]
  have hle : ⌊-x⌋ ≤ ⌊x⌋ := Int.floor_le_floor (by linarith)
  have hnn : 0 ≤ ⌊x⌋ + 1 - ⌊-x⌋ := by omega
  have hcast : (((⌊x⌋ + 1 - ⌊-x⌋).toNat : ℕ) : ℝ) = ((⌊x⌋ + 1 - ⌊-x⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [hcast]
  push_cast
  have h1 := Int.floor_le x
  have h2 := Int.sub_one_lt_floor (-x)
  linarith

/-- Separated labels whose strips contain `y` and whose normals are nearly
orthogonal to a unit vector `u` (`|⟪e, u⟫| ≤ amax`, `⟪e, u⟫ ^ 2 ≤ 1/2`) are at most
`2 (64 amax / r + 2) * 6`. -/
lemma card_le_of_frame {u y : E2} {r amax : ℝ} (hu : ‖u‖ = 1) (hr : 0 < r) (hamax : 0 ≤ amax)
    (Jy : Finset (E2 × E2)) (hsep : (Jy : Set (E2 × E2)).Pairwise (StripSep r))
    (hJ : ∀ j ∈ Jy, ‖j.2‖ = 1 ∧ ‖y - j.1‖ ≤ 8 ∧ (inner ℝ j.2 u) ^ 2 ≤ 1 / 2 ∧
      |inner ℝ j.2 u| ≤ amax ∧ |inner ℝ (y - j.1) j.2| < r) :
    (Jy.card : ℝ) ≤ 12 * (64 * amax / r + 2) := by
  set s := r / 32 with hsdef
  set s' := r / 2 with hs'def
  have hs : 0 < s := by positivity
  have hs' : 0 < s' := by positivity
  let box : Finset (ℤ × ℤ × ℤ) :=
    Finset.Icc (0 : ℤ) 1 ×ˢ (Finset.Icc ⌊-(amax / s)⌋ ⌊amax / s⌋ ×ˢ Finset.Icc ⌊-(r / s')⌋ ⌊r / s'⌋)
  have hmaps : Set.MapsTo (stripCode u y s s') (Jy : Set (E2 × E2)) (box : Set (ℤ × ℤ × ℤ)) := by
    intro j hj
    obtain ⟨_, _, _, ha, hc⟩ := hJ j hj
    simp only [box, stripCode, Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc]
    refine ⟨⟨by split_ifs <;> norm_num, by split_ifs <;> norm_num⟩,
      ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩, ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩⟩
    · rw [← neg_div]; exact div_le_div_of_nonneg_right (abs_le.mp ha).1 hs.le
    · exact div_le_div_of_nonneg_right (abs_le.mp ha).2 hs.le
    · rw [← neg_div]; exact div_le_div_of_nonneg_right (abs_lt.mp hc).1.le hs'.le
    · exact div_le_div_of_nonneg_right (abs_lt.mp hc).2.le hs'.le
  have hinj := stripCode_injOn (Jy := (Jy : Set (E2 × E2))) hu hs hs' (by rw [hsdef, hs'def]; linarith)
    hsep (fun j hj => ⟨(hJ j hj).1, (hJ j hj).2.1, (hJ j hj).2.2.1⟩)
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have hbox : (box.card : ℝ) ≤ 12 * (64 * amax / r + 2) := by
    simp only [box, Finset.card_product]
    push_cast
    have h1 : ((Finset.Icc (0 : ℤ) 1).card : ℝ) = 2 := by simp
    have hrs' : r / s' = 2 := by rw [hs'def]; field_simp
    have has : amax / s = 32 * amax / r := by rw [hsdef]; field_simp
    have h2 : ((Finset.Icc ⌊-(amax / s)⌋ ⌊amax / s⌋).card : ℝ) ≤ 2 * (32 * amax / r) + 2 :=
      (card_Icc_floor_le (x := amax / s) (by positivity)).trans_eq (by rw [has])
    have h3 : ((Finset.Icc ⌊-(r / s')⌋ ⌊r / s'⌋).card : ℝ) ≤ 2 * 2 + 2 :=
      (card_Icc_floor_le (x := r / s') (by positivity)).trans_eq (by rw [hrs'])
    rw [h1]
    have h2' : 0 ≤ ((Finset.Icc ⌊-(amax / s)⌋ ⌊amax / s⌋).card : ℝ) := Nat.cast_nonneg _
    calc 2 * (((Finset.Icc ⌊-(amax / s)⌋ ⌊amax / s⌋).card : ℝ) *
          ((Finset.Icc ⌊-(r / s')⌋ ⌊r / s'⌋).card : ℝ))
        ≤ 2 * ((2 * (32 * amax / r) + 2) * (2 * 2 + 2)) := by
          gcongr
      _ = 12 * (64 * amax / r + 2) := by ring
  exact (Nat.cast_le.mpr hcard).trans hbox

end WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap
