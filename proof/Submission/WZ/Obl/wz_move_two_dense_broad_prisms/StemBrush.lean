-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.StemBrush.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/- Adapted from session x0449 on o152 in this workspace. -/
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer
import Submission.WZ.Obl.wz_transverse_brush_selection.Geometry

/-! A broad fibre supplies many tubes transverse to a shaded stem. -/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
open scoped ENNReal

/-- A cap accounting for at most half of a broad fibre leaves at least half
of any lower multiplicity bound outside that cap. -/
theorem broad_count_away_from_direction {ω ζ δ h ρ r m : ℝ} {n N : ℕ}
    {v : Fin n → Space} {S : Finset (Fin n)} {Z : Fin n → Set Space}
    {f : Fin n → Fin N} (hBr : Broad ω ζ δ h ρ n N v S Z f)
    (k : Fin N) (p u : Space) (hu : ‖u‖ = 1) (hδr : δ ≤ r) (hrρ : r ≤ ρ)
    (hsmall : δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) ≤ 1 / 2)
    (hm : m ≤ ({i | i ∈ S ∧ f i = k ∧ p ∈ Z i}.ncard : ℝ)) :
    m / 2 ≤ ({i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧
      r < min ‖v i - u‖ ‖v i + u‖}.ncard : ℝ) := by
  classical
  let A : Set (Fin n) := {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}
  let B : Set (Fin n) := {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧
    min ‖v i - u‖ ‖v i + u‖ ≤ r}
  have hBA : B ⊆ A := fun _ hi => ⟨hi.1, hi.2.1, hi.2.2.1⟩
  have hsplit : ((A \ B).ncard : ℝ) + (B.ncard : ℝ) = (A.ncard : ℝ) := by
    exact_mod_cast Set.ncard_sdiff_add_ncard_of_subset hBA
  have hcap : (B.ncard : ℝ) ≤ (1 / 2) * (A.ncard : ℝ) :=
    (hBr k p u r hu hδr hrρ).trans
      (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _))
  have hfar : A \ B = {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧
      r < min ‖v i - u‖ ‖v i + u‖} := by
    ext i
    simp only [A, B, mem_sdiff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hiS, hfk, hp⟩, hnot⟩
      exact ⟨hiS, hfk, hp, lt_of_not_ge (fun hle => hnot ⟨hiS, hfk, hp, hle⟩)⟩
    · rintro ⟨hiS, hfk, hp, hgt⟩
      exact ⟨⟨hiS, hfk, hp⟩, fun hle => (not_le.mpr hgt) hle.2.2.2⟩
  rw [← hfar]
  change m ≤ (A.ncard : ℝ) at hm
  linarith

/-- Integrating the transverse incidences along a shaded stem gives the
quantitative bush count used in local grain extraction. The geometric overlap
estimate is imported from accepted o021. -/
theorem broad_stem_brush_count {ω ζ δ h ρ r m : ℝ} {n N : ℕ}
    {x v : Fin n → Space} {S : Finset (Fin n)} {Z : Fin n → Set Space}
    {f : Fin n → Fin N} (hδ : 0 < δ) (hρ1 : ρ ≤ 1) (hm : 0 ≤ m)
    (hv : ∀ i, ‖v i‖ = 1) (hZm : ∀ i, MeasurableSet (Z i))
    (hZT : ∀ i, Z i ⊆ T δ (x i) (v i))
    (hBr : Broad ω ζ δ h ρ n N v S Z f)
    (k : Fin N) (y u : Space) (hu : ‖u‖ = 1)
    {E : Set Space} (hE : MeasurableSet E) (hEstem : E ⊆ T δ y u)
    (hδr : δ ≤ r) (hrρ : r ≤ ρ)
    (hsmall : δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) ≤ 1 / 2)
    (hlevel : ∀ p ∈ E, m ≤ ({i | i ∈ S ∧ f i = k ∧ p ∈ Z i}.ncard : ℝ)) :
    ∃ H : Set (Fin n),
      (∀ i ∈ H, i ∈ S ∧ f i = k ∧ r < min ‖v i - u‖ ‖v i + u‖ ∧
        (E ∩ Z i).Nonempty) ∧
      ENNReal.ofReal (m / 2) * volume E ≤
        ENNReal.ofReal ((H.ncard : ℝ) * (4096 * δ ^ 3 / r)) := by
  classical
  let H : Set (Fin n) := {i | i ∈ S ∧ f i = k ∧
    r < min ‖v i - u‖ ‖v i + u‖ ∧ (E ∩ Z i).Nonempty}
  let W : Fin n → Set Space := fun i => if i ∈ H then E ∩ Z i else ∅
  have hWm : ∀ i, MeasurableSet (W i) := by
    intro i
    by_cases hi : i ∈ H
    · simpa only [W, ite_eq_left hi] using hE.inter (hZm i)
    · simpa only [W, ite_eq_right hi] using (MeasurableSet.empty : MeasurableSet (∅ : Set Space))
  have hcount : ∀ p, (m / 2) * bodyCount (fun _ : Fin 1 => E) p ≤ bodyCount W p := by
    intro p
    by_cases hp : p ∈ E
    · have hsets : {i | p ∈ W i} =
          {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ r < min ‖v i - u‖ ‖v i + u‖} := by
        ext i
        simp only [mem_ofPred_eq]
        constructor
        · intro hi
          have hiH : i ∈ H := by
            by_contra hnot
            simp only [W, ite_eq_right hnot, mem_empty_iff_false] at hi
          have hiW : p ∈ E ∩ Z i := by simpa only [W, ite_eq_left hiH] using hi
          exact ⟨hiH.1, hiH.2.1, hiW.2, hiH.2.2.1⟩
        · rintro ⟨hiS, hfk, hpi, hsep⟩
          have hiH : i ∈ H := ⟨hiS, hfk, hsep, ⟨p, hp, hpi⟩⟩
          simpa only [W, ite_eq_left hiH] using (show p ∈ E ∩ Z i from ⟨hp, hpi⟩)
      have hsingle : bodyCount (fun _ : Fin 1 => E) p = 1 := by simp [bodyCount, hp]
      rw [hsingle, mul_one]
      change m / 2 ≤ ({i | p ∈ W i}.ncard : ℝ)
      rw [hsets]
      exact broad_count_away_from_direction hBr k p u hu hδr hrρ hsmall (hlevel p hp)
    · have hsingle : bodyCount (fun _ : Fin 1 => E) p = 0 := by simp [bodyCount, hp]
      rw [hsingle, mul_zero]
      exact Nat.cast_nonneg _
  have hmass : ENNReal.ofReal (m / 2) * volume E ≤ ∑ i, volume (W i) := by
    simpa only [Fin.sum_univ_one] using
      (body_mass_le_of_count (fun _ : Fin 1 => hE) hWm (by positivity) hcount)
  have hvol : ∀ i, volume (W i) ≤ if i ∈ H then ENNReal.ofReal (4096 * δ ^ 3 / r) else 0 := by
    intro i
    by_cases hi : i ∈ H
    · rw [ite_eq_left hi]
      change volume (if i ∈ H then E ∩ Z i else ∅) ≤ _
      rw [ite_eq_left hi]
      refine (measure_mono (show E ∩ Z i ⊆ T δ (x i) (v i) ∩ T δ y u from
        fun p hp => ⟨hZT i hp.2, hEstem hp.1⟩)).trans ?_
      exact WangZahlLot.Obl.wz_transverse_brush_selection.transverse_intersection_volume
        hδ (hδ.trans_le hδr) (hrρ.trans hρ1) (hv i) hu hi.2.2.1.le
    · simp only [W, ite_eq_right hi, measure_empty, le_refl]
  have hcard : (Finset.univ.filter (fun i : Fin n => i ∈ H)).card = H.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext i
    simp
  refine ⟨H, fun _ hi => hi, hmass.trans ?_⟩
  calc (∑ i, volume (W i)) ≤ ∑ i : Fin n,
        if i ∈ H then ENNReal.ofReal (4096 * δ ^ 3 / r) else 0 :=
      Finset.sum_le_sum (fun i _ => hvol i)
    _ = _ := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard,
        ENNReal.ofReal_mul (Nat.cast_nonneg H.ncard), ENNReal.ofReal_natCast]

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
