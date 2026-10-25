-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_bush_line_count.Bushes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_bush_line_count.StripCount

/-!
# Bushes of separated normals

* `strips_close_of_common_far_point`: two strips of half-width `r` through `b`
  sharing a point at distance `≥ 1/4` from `b` have normals within `16 r` (up to
  sign); so strips through `b` with `16 r`-separated normals are disjoint far from
  `b`.
* `inner_lt_of_close`: moving the normal by `ρ` moves the offset of a point at
  distance `≤ 8` by less than `8 ρ`.
* `exists_maximal_normSep`: every set of unit vectors has a finite maximal
  `s`-separated (up to sign) subset.

Ported from session x0394 (o141, commit d684c60).
-/

namespace WangZahlLot.Obl.wz_furstenberg_bush_line_count

open scoped Classical

/-- Separation of unit normals up to sign. -/
def NormSep (s : ℝ) (e e' : E2) : Prop := s ≤ dist e e' ∧ s ≤ dist e (-e')

lemma strips_close_of_common_far_point {v e e' : E2} {r : ℝ} (hr : 0 < r) (hr6 : r ≤ 1 / 6)
    (he : ‖e‖ = 1) (he' : ‖e'‖ = 1) (hv : 1 / 4 ≤ ‖v‖)
    (h1 : |inner ℝ v e| < r) (h2 : |inner ℝ v e'| < r) :
    dist e e' < 16 * r ∨ dist e (-e') < 16 * r := by
  have hv0 : 0 < ‖v‖ := by linarith
  set u : E2 := ‖v‖⁻¹ • v with hudef
  have hu : ‖u‖ = 1 := by rw [hudef, norm_smul, norm_inv, norm_norm]; field_simp
  have hcoef : ∀ f : E2, |inner ℝ f u| < 4 * r → (inner ℝ f u) ^ 2 ≤ 1 / 2 := by
    intro f hf
    have h0 := abs_nonneg (inner ℝ f u)
    rw [← sq_abs]; nlinarith
  have hsmall : ∀ f : E2, |inner ℝ v f| < r → |inner ℝ f u| < 4 * r := by
    intro f hf
    rw [hudef, inner_smul_right, real_inner_comm, abs_mul, abs_inv, abs_norm]
    rw [inv_mul_lt_iff₀ hv0]
    nlinarith [abs_nonneg (inner ℝ v f)]
  have ha := hsmall e h1
  have ha' := hsmall e' h2
  by_cases hside : 0 ≤ inner ℝ e (rot u) * inner ℝ e' (rot u)
  · left
    have hc := frame_close hu he he' (hcoef e ha) (hcoef e' ha') hside
    have hdiff : |inner ℝ e u - inner ℝ e' u| < 8 * r := by
      calc |inner ℝ e u - inner ℝ e' u| ≤ |inner ℝ e u| + |inner ℝ e' u| := abs_sub _ _
        _ < 4 * r + 4 * r := add_lt_add ha ha'
        _ = 8 * r := by ring
    have hsq : (inner ℝ e u - inner ℝ e' u) ^ 2 < (8 * r) ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ hdiff (abs_nonneg _) two_ne_zero
    rw [dist_eq_norm]
    by_contra hcon
    have hcon' := not_lt.mp hcon
    nlinarith [norm_nonneg (e - e')]
  · right
    have hne' : ‖-e'‖ = 1 := by rw [norm_neg, he']
    have ha'' : |inner ℝ (-e') u| < 4 * r := by rw [inner_neg_left, abs_neg]; exact ha'
    have hside' : 0 ≤ inner ℝ e (rot u) * inner ℝ (-e') (rot u) := by
      rw [inner_neg_left]; nlinarith
    have hc := frame_close hu he hne' (hcoef e ha) (hcoef (-e') ha'') hside'
    have hdiff : |inner ℝ e u - inner ℝ (-e') u| < 8 * r := by
      calc |inner ℝ e u - inner ℝ (-e') u| ≤ |inner ℝ e u| + |inner ℝ (-e') u| := abs_sub _ _
        _ < 4 * r + 4 * r := add_lt_add ha ha''
        _ = 8 * r := by ring
    have hsq : (inner ℝ e u - inner ℝ (-e') u) ^ 2 < (8 * r) ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ hdiff (abs_nonneg _) two_ne_zero
    rw [dist_eq_norm]
    by_contra hcon
    have hcon' := not_lt.mp hcon
    nlinarith [norm_nonneg (e - -e')]

lemma inner_lt_of_close {v e e' : E2} {w ρ : ℝ} (hv : ‖v‖ ≤ 8) (h : |inner ℝ v e| < w)
    (hee : ‖e - e'‖ ≤ ρ) : |inner ℝ v e'| < w + 8 * ρ := by
  have h1 : inner ℝ v e' = inner ℝ v e - inner ℝ v (e - e') := by
    rw [inner_sub_right]; ring
  have h2 : |inner ℝ v (e - e')| ≤ 8 * ρ := by
    calc |inner ℝ v (e - e')| ≤ ‖v‖ * ‖e - e'‖ := abs_real_inner_le_norm _ _
      _ ≤ 8 * ρ := mul_le_mul hv hee (norm_nonneg _) (by norm_num)
  rw [h1]
  calc |inner ℝ v e - inner ℝ v (e - e')| ≤ |inner ℝ v e| + |inner ℝ v (e - e')| := abs_sub _ _
    _ < w + 8 * ρ := by linarith

/-- `1` for nonnegative reals, `0` otherwise. -/
noncomputable def sgnCode (a : ℝ) : ℤ := if 0 ≤ a then 1 else 0

lemma mul_nonneg_of_sgnCode_eq {a a' : ℝ} (h : sgnCode a = sgnCode a') : 0 ≤ a * a' := by
  unfold sgnCode at h
  split_ifs at h with h1 h2 h2
  · exact mul_nonneg h1 h2
  · norm_num at h
  · norm_num at h
  · exact (mul_pos_of_neg_of_neg (not_le.mp h1) (not_le.mp h2)).le

lemma sgnCode_mem (a : ℝ) : sgnCode a ∈ Finset.Icc (0 : ℤ) 1 := by
  unfold sgnCode; split_ifs <;> simp

/-- The code of a unit vector: its frame (which coordinate is small), the sign of
the other coordinate, and the small coordinate at resolution `t`. -/
noncomputable def normalCode (t : ℝ) (e : E2) : ℤ × ℤ × ℤ :=
  if (e 0) ^ 2 ≤ 1 / 2 then (0, sgnCode (e 1), ⌊e 0 / t⌋)
  else (1, sgnCode (e 0), ⌊e 1 / t⌋)

lemma inner_rot_ax0 (e : E2) : inner ℝ e (rot ax0) = e 1 := by
  rw [inner_coords]; simp [rot, ax0]

lemma inner_rot_ax1 (e : E2) : inner ℝ e (rot ax1) = -(e 0) := by
  rw [inner_coords]; simp [rot, ax1]

lemma normalCode_close {t : ℝ} (ht : 0 < t) {e e' : E2} (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    (h : normalCode t e = normalCode t e') : ‖e - e'‖ < 2 * t := by
  have hsq : ∀ f : E2, ‖f‖ = 1 → f 0 ^ 2 + f 1 ^ 2 = 1 := by
    intro f hf; rw [← norm_sq_coords, hf]; norm_num
  have h0 := hsq e he
  have h0' := hsq e' he'
  have hfin : ∀ a a' : ℝ, |a - a'| < t → ‖e - e'‖ ^ 2 ≤ 3 * (a - a') ^ 2 → ‖e - e'‖ < 2 * t := by
    intro a a' hlt hle
    have : (a - a') ^ 2 < t ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ hlt (abs_nonneg _) two_ne_zero
    by_contra hcon
    have := not_lt.mp hcon
    nlinarith [norm_nonneg (e - e')]
  unfold normalCode at h
  split_ifs at h with h1 h2 h2
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, hs, hf⟩ := h
    apply hfin (e 0) (e' 0) (floor_close ht hf)
    have hc := frame_close norm_ax0 he he' (by rw [inner_ax0]; exact h1)
      (by rw [inner_ax0]; exact h2)
      (by rw [inner_rot_ax0, inner_rot_ax0]; exact mul_nonneg_of_sgnCode_eq hs)
    rwa [inner_ax0, inner_ax0] at hc
  · simp at h
  · simp at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, hs, hf⟩ := h
    apply hfin (e 1) (e' 1) (floor_close ht hf)
    have h1' : e 1 ^ 2 ≤ 1 / 2 := by have := not_le.mp h1; linarith
    have h2' : e' 1 ^ 2 ≤ 1 / 2 := by have := not_le.mp h2; linarith
    have hb : 0 ≤ inner ℝ e (rot ax1) * inner ℝ e' (rot ax1) := by
      rw [inner_rot_ax1, inner_rot_ax1, neg_mul_neg]; exact mul_nonneg_of_sgnCode_eq hs
    have hc := frame_close norm_ax1 he he' (by rw [inner_ax1]; exact h1')
      (by rw [inner_ax1]; exact h2') hb
    rwa [inner_ax1, inner_ax1] at hc

lemma normalCode_mem_box {t : ℝ} (ht : 0 < t) {e : E2} (he : ‖e‖ = 1) :
    normalCode t e ∈ (Finset.Icc (0 : ℤ) 1 ×ˢ (Finset.Icc (0 : ℤ) 1 ×ˢ
      Finset.Icc ⌊-(1 / t)⌋ ⌊1 / t⌋)) := by
  have h := norm_sq_coords e
  rw [he] at h
  have hb0 : |e 0| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg (e 1)]
  have hb1 : |e 1| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg (e 0)]
  have hfl : ∀ a : ℝ, |a| ≤ 1 → ⌊-(1 / t)⌋ ≤ ⌊a / t⌋ ∧ ⌊a / t⌋ ≤ ⌊1 / t⌋ := by
    intro a ha
    constructor
    · apply Int.floor_le_floor; rw [← neg_div]
      exact div_le_div_of_nonneg_right (abs_le.mp ha).1 ht.le
    · apply Int.floor_le_floor
      exact div_le_div_of_nonneg_right (abs_le.mp ha).2 ht.le
  unfold normalCode
  split_ifs
  · simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨by norm_num, Finset.mem_Icc.mp (sgnCode_mem _), hfl _ hb0⟩
  · simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨by norm_num, Finset.mem_Icc.mp (sgnCode_mem _), hfl _ hb1⟩

/-- Separated (up to sign) unit vectors are few. -/
lemma card_le_of_normSep {s : ℝ} (hs : 0 < s) (F : Finset E2) (hF : ∀ e ∈ F, ‖e‖ = 1)
    (hsep : (F : Set E2).Pairwise (NormSep s)) : (F.card : ℝ) ≤ 4 * (4 / s + 2) := by
  set t := s / 2 with htdef
  have ht : 0 < t := by positivity
  let box : Finset (ℤ × ℤ × ℤ) := Finset.Icc (0 : ℤ) 1 ×ˢ (Finset.Icc (0 : ℤ) 1 ×ˢ
      Finset.Icc ⌊-(1 / t)⌋ ⌊1 / t⌋)
  have hmaps : Set.MapsTo (normalCode t) (F : Set E2) (box : Set (ℤ × ℤ × ℤ)) :=
    fun e he => normalCode_mem_box ht (hF e he)
  have hinj : Set.InjOn (normalCode t) (F : Set E2) := by
    intro e he e' he' hcode
    by_contra hne
    have := hsep he he' hne
    have hc := normalCode_close ht (hF e he) (hF e' he') hcode
    have : s ≤ ‖e - e'‖ := by rw [← dist_eq_norm]; exact this.1
    linarith
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have hbox : (box.card : ℝ) ≤ 4 * (4 / s + 2) := by
    simp only [box, Finset.card_product]
    push_cast
    have h1 : ((Finset.Icc (0 : ℤ) 1).card : ℝ) = 2 := by simp
    have h3 : ((Finset.Icc ⌊-(1 / t)⌋ ⌊1 / t⌋).card : ℝ) ≤ 2 * (1 / t) + 2 :=
      card_Icc_floor_le (by positivity)
    rw [h1]
    have : 2 * (1 / t) + 2 = 4 / s + 2 := by rw [htdef]; field_simp; ring
    rw [this] at h3
    nlinarith
  exact (Nat.cast_le.mpr hcard).trans hbox

/-- A finite maximal separated subset. -/
lemma exists_maximal_normSep (H : Set E2) (hH : ∀ e ∈ H, ‖e‖ = 1) {s : ℝ} (hs : 0 < s) :
    ∃ D : Finset E2, (D : Set E2) ⊆ H ∧ (D : Set E2).Pairwise (NormSep s) ∧
      ∀ e ∈ H, ∃ e' ∈ D, dist e e' < s ∨ dist e (-e') < s := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 4 * (4 / s + 2) < N := exists_nat_gt _
  let Q : ℕ → Prop := fun n => ∃ D : Finset E2, (D : Set E2) ⊆ H ∧
    (D : Set E2).Pairwise (NormSep s) ∧ D.card = n
  have hQ0 : Q 0 := ⟨∅, by simp, by simp, rfl⟩
  have hQN : ∀ n, Q n → n ≤ N := by
    rintro n ⟨D, hDH, hDsep, rfl⟩
    have := card_le_of_normSep hs D (fun e he => hH e (hDH he)) hDsep
    exact_mod_cast (this.trans hN.le)
  set m := Nat.findGreatest Q N with hmdef
  have hQm : Q m := Nat.findGreatest_spec (P := Q) (Nat.zero_le N) hQ0
  obtain ⟨D, hDH, hDsep, hDcard⟩ := hQm
  refine ⟨D, hDH, hDsep, ?_⟩
  intro e he
  by_contra hcon
  push Not at hcon
  have heD : e ∉ D := by
    intro heD
    have h := (hcon e heD).1
    simp at h
    linarith
  have hQ : Q (m + 1) := by
    refine ⟨insert e D, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.coe_insert] at hx
      rcases hx with rfl | hx
      · exact he
      · exact hDH hx
    · rw [Finset.coe_insert]
      apply Set.Pairwise.insert hDsep
      intro b hb _
      obtain ⟨h1, h2⟩ := hcon b hb
      refine ⟨⟨h1, h2⟩, ?_, ?_⟩
      · rw [dist_comm]; exact h1
      · have : dist b (-e) = dist e (-b) := by
          rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
        rw [this]; exact h2
    · rw [Finset.card_insert_of_notMem heD, hDcard]
  have := Nat.le_findGreatest (hQN (m + 1) hQ) hQ
  omega

end WangZahlLot.Obl.wz_furstenberg_bush_line_count
