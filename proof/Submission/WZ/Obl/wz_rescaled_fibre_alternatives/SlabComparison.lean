-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.SlabComparison.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Basic

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

lemma homothety_inner (p q u : Space) (a : ℝ) :
    inner ℝ u (AffineMap.homothety p a q) = inner ℝ u p + a * (inner ℝ u q - inner ℝ u p) := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    inner_add_right, inner_smul_right, inner_sub_right]
  ring

/-- A set and its reflection can each be contracted into a slab that meets the
contraction center. This controls enlarged slab sections without centering assumptions. -/
lemma enlarged_slab_volume {D E : Set Space} {p u : Space} {t r a C : ℝ}
    (hp : p ∈ slab u t r) (ha : 0 < a) (hC : 1 ≤ C)
    (haC : a * (C + 1) ≤ 1) (hr : 0 < r)
    (hplus : AffineMap.homothety p a '' E ⊆ D)
    (hminus : AffineMap.homothety p (-a) '' E ⊆ D) :
    ENNReal.ofReal (a ^ 3) * volume (E ∩ slab u t (C * r)) ≤
      2 * volume (D ∩ slab u t r) := by
  let A := E ∩ slab u t (C * r) ∩ {q | inner ℝ u q ≤ inner ℝ u p}
  let B := E ∩ slab u t (C * r) ∩ {q | inner ℝ u p ≤ inner ℝ u q}
  have hsplit : E ∩ slab u t (C * r) = A ∪ B := by
    ext q
    constructor
    · intro hq
      rcases le_total (inner ℝ u q) (inner ℝ u p) with h | h
      · exact Or.inl ⟨hq, h⟩
      · exact Or.inr ⟨hq, h⟩
    · exact fun h => h.elim And.left And.left
  have hbound {q : Space} (hq : q ∈ slab u t (C * r)) :
      a * |inner ℝ u q - inner ℝ u p| ≤ r := by
    have htri : |inner ℝ u q - inner ℝ u p| ≤ (C + 1) * r := by
      have hh := abs_sub_le (inner ℝ u q) t (inner ℝ u p)
      rw [abs_sub_comm t] at hh
      change |inner ℝ u p - t| ≤ r at hp
      change |inner ℝ u q - t| ≤ C * r at hq
      linarith
    calc
      _ ≤ a * ((C + 1) * r) := mul_le_mul_of_nonneg_left htri ha.le
      _ ≤ r := by nlinarith [mul_le_mul_of_nonneg_right haC hr.le]
  have himage {Q : Set Space} (hQ : Q ⊆ E ∩ slab u t (C * r))
      {b : ℝ} (hb : b = a ∨ b = -a)
      (hdir : ∀ q ∈ Q, (inner ℝ u p - t) * (b * (inner ℝ u q - inner ℝ u p)) ≤ 0)
      (hsign : (0 ≤ inner ℝ u p - t ∧ ∀ q ∈ Q, b * (inner ℝ u q - inner ℝ u p) ≤ 0) ∨
        (inner ℝ u p - t ≤ 0 ∧ ∀ q ∈ Q, 0 ≤ b * (inner ℝ u q - inner ℝ u p))) :
      ENNReal.ofReal (a ^ 3) * volume Q ≤ volume (D ∩ slab u t r) := by
    have hsubset : AffineMap.homothety p b '' Q ⊆ D ∩ slab u t r := by
      rintro _ ⟨q, hq, rfl⟩
      have hqE := (hQ hq).1
      have hqS := (hQ hq).2
      refine ⟨?_, ?_⟩
      · rcases hb with rfl | rfl
        · exact hplus ⟨q, hqE, rfl⟩
        · exact hminus ⟨q, hqE, rfl⟩
      · have hh : |b * (inner ℝ u q - inner ℝ u p)| ≤ r := by
          rcases hb with rfl | rfl <;> simpa [abs_mul, abs_of_pos ha] using hbound hqS
        change |inner ℝ u (AffineMap.homothety p b q) - t| ≤ r
        rw [homothety_inner, abs_le]
        have hp' := abs_le.mp (show |inner ℝ u p - t| ≤ r from hp)
        have hh' := abs_le.mp hh
        rcases hsign with ⟨hp0, hb0⟩ | ⟨hp0, hb0⟩
        · have hb0' := hb0 q hq
          constructor <;> linarith [hp'.1, hp'.2, hh'.1, hh'.2]
        · have hb0' := hb0 q hq
          constructor <;> linarith [hp'.1, hp'.2, hh'.1, hh'.2]
    have hm : volume (AffineMap.homothety p b '' Q) ≤ volume (D ∩ slab u t r) := measure_mono hsubset
    rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at hm
    rcases hb with rfl | rfl <;> simpa [abs_of_pos ha, abs_pow] using hm
  have hA : ENNReal.ofReal (a ^ 3) * volume A ≤ volume (D ∩ slab u t r) := by
    rcases le_total 0 (inner ℝ u p - t) with ht | ht
    · apply himage (Q := A) (fun _ h => h.1) (b := a) (Or.inl rfl)
      · intro q hq; exact mul_nonpos_of_nonneg_of_nonpos ht
          (mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hq.2))
      · exact Or.inl ⟨ht, fun q hq => mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hq.2)⟩
    · apply himage (Q := A) (fun _ h => h.1) (b := -a) (Or.inr rfl)
      · intro q hq; exact mul_nonpos_of_nonpos_of_nonneg ht
          (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ha.le) (sub_nonpos.mpr hq.2))
      · exact Or.inr ⟨ht, fun q hq => mul_nonneg_of_nonpos_of_nonpos
          (neg_nonpos.mpr ha.le) (sub_nonpos.mpr hq.2)⟩
  have hB : ENNReal.ofReal (a ^ 3) * volume B ≤ volume (D ∩ slab u t r) := by
    rcases le_total 0 (inner ℝ u p - t) with ht | ht
    · apply himage (Q := B) (fun _ h => h.1) (b := -a) (Or.inr rfl)
      · intro q hq; exact mul_nonpos_of_nonneg_of_nonpos ht
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sub_nonneg.mpr hq.2))
      · exact Or.inl ⟨ht, fun q hq => mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr ha.le) (sub_nonneg.mpr hq.2)⟩
    · apply himage (Q := B) (fun _ h => h.1) (b := a) (Or.inl rfl)
      · intro q hq; exact mul_nonpos_of_nonpos_of_nonneg ht (mul_nonneg ha.le (sub_nonneg.mpr hq.2))
      · exact Or.inr ⟨ht, fun q hq => mul_nonneg ha.le (sub_nonneg.mpr hq.2)⟩
  calc
    _ ≤ ENNReal.ofReal (a ^ 3) * (volume A + volume B) := by
      rw [hsplit]
      exact mul_le_mul_right (measure_union_le A B) _
    _ = ENNReal.ofReal (a ^ 3) * volume A + ENNReal.ofReal (a ^ 3) * volume B := mul_add _ _ _
    _ ≤ volume (D ∩ slab u t r) + volume (D ∩ slab u t r) := add_le_add hA hB
    _ = _ := (two_mul _).symm

/-- A local slab estimate passes between comparable families and buffered domains. -/
lemma slabBound_of_comparable {D E : Set Space} {a B C L : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hC : 1 ≤ C) (haC : a * (2 * C + 2) ≤ 1)
    {n : ℕ} {P : Fin n → Prop} {U V : Fin n → Set Space} (p : Fin n → Space)
    (hp : ∀ i, P i → p i ∈ U i)
    (hV : ∀ i, P i → V i ⊆ E)
    (hexpand : ∀ i, P i → V i ⊆ AffineMap.homothety (p i) C '' U i)
    (hplus : ∀ i, P i → AffineMap.homothety (p i) a '' E ⊆ D)
    (hminus : ∀ i, P i → AffineMap.homothety (p i) (-a) '' E ⊆ D)
    (hvol : volume D ≤ ENNReal.ofReal B * volume E)
    (h : SlabBound E L P V) :
    SlabBound D (B * (2 / a ^ 3) * L) P U := by
  intro u t r hu hr
  let I : Set (Fin n) := {i | P i ∧ U i ⊆ D ∩ slab u t r}
  change ENNReal.ofReal (I.ncard : ℝ) * volume D ≤ _
  rcases I.eq_empty_or_nonempty with hI | ⟨i₀, hi₀⟩
  · simp [hI]
  have hm : p i₀ ∈ slab u t r := (hi₀.2 (hp i₀ hi₀.1)).2
  have hcount : I.ncard ≤ {i | P i ∧ V i ⊆ E ∩ slab u t ((2 * C + 1) * r)}.ncard := by
    apply Set.ncard_mono
    intro i hi
    refine ⟨hi.1, fun q hq => ⟨hV i hi.1 hq, ?_⟩⟩
    obtain ⟨z, hz, rfl⟩ := hexpand i hi.1 hq
    have hpm : |inner ℝ u (p i) - t| ≤ r := (hi.2 (hp i hi.1)).2
    have hzm : |inner ℝ u z - t| ≤ r := (hi.2 hz).2
    have hdiff : |inner ℝ u z - inner ℝ u (p i)| ≤ 2 * r := by
      have hh := abs_sub_le (inner ℝ u z) t (inner ℝ u (p i))
      rw [abs_sub_comm t] at hh
      linarith
    change |inner ℝ u (AffineMap.homothety (p i) C z) - t| ≤ _
    rw [homothety_inner]
    have hh := abs_add_le (inner ℝ u (p i) - t) (C * (inner ℝ u z - inner ℝ u (p i)))
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ C)] at hh
    have hdiff' := mul_le_mul_of_nonneg_left hdiff (by linarith : 0 ≤ C)
    have he : inner ℝ u (p i) + C * (inner ℝ u z - inner ℝ u (p i)) - t =
        (inner ℝ u (p i) - t) + C * (inner ℝ u z - inner ℝ u (p i)) := by ring
    rw [he]
    linarith
  have hraw := h u t ((2 * C + 1) * r) hu (by positivity)
  have hslice := enlarged_slab_volume hm ha (by linarith : 1 ≤ 2 * C + 1)
    (by linarith) hr (hplus i₀ hi₀.1) (hminus i₀ hi₀.1)
  have ha0 : ENNReal.ofReal (a ^ 3) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hslice' : volume (E ∩ slab u t ((2 * C + 1) * r)) ≤
      ENNReal.ofReal (2 / a ^ 3) * volume (D ∩ slab u t r) := by
    calc
      _ = (ENNReal.ofReal (a ^ 3))⁻¹ *
          (ENNReal.ofReal (a ^ 3) * volume (E ∩ slab u t ((2 * C + 1) * r))) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal (a ^ 3))⁻¹ * (2 * volume (D ∩ slab u t r)) := mul_le_mul_right hslice _
      _ = _ := by rw [← mul_assoc, ENNReal.ofReal_div_of_pos (by positivity)]; norm_num [div_eq_mul_inv, mul_comm]
  calc
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal (I.ncard : ℝ) * volume E) := by
      simpa only [mul_left_comm] using mul_le_mul_right hvol (ENNReal.ofReal (I.ncard : ℝ))
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal (L * ({i | P i}.ncard : ℝ)) *
        volume (E ∩ slab u t ((2 * C + 1) * r))) := by
      exact mul_le_mul_right ((mul_le_mul_left
        (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hcount)) _).trans hraw) _
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal (L * ({i | P i}.ncard : ℝ)) *
        (ENNReal.ofReal (2 / a ^ 3) * volume (D ∩ slab u t r))) := by gcongr
    _ = _ := by
      calc
        _ = (ENNReal.ofReal B * ENNReal.ofReal (2 / a ^ 3)) *
            ENNReal.ofReal (L * ({i | P i}.ncard : ℝ)) * volume (D ∩ slab u t r) := by ac_rfl
        _ = _ := by
          rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
