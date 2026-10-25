-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_three_thick_grains_gain.Box.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_three_thick_grains_gain.Core

set_option linter.unusedVariables false

/-!
# The frozen box `P`: volume, a ball lemma, convexity

Taken from session x0423's `Box.lean` on o153 (branch x0423 of o153, commit 28b8eeb), rehomed
into this namespace.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_move_three_thick_grains_gain

open Set MeasureTheory Metric
open scoped ENNReal

/-- The frozen box `P a b c z e` in coordinates. -/
def boxCoord (z : V) (e : V ≃ₗᵢ[ℝ] V) (p : V) : Fin 3 → ℝ := WithLp.ofLp (e (p - z))

theorem boxCoord_measurePreserving (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (boxCoord z e) volume volume :=
  (PiLp.volume_preserving_ofLp (Fin 3)).comp
    (e.measurePreserving.comp (measurePreserving_sub_right volume z))

theorem P_eq_preimage (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    P a b c z e = boxCoord z e ⁻¹' Icc (fun k => -(![a, b, c] k / 2)) (fun k => ![a, b, c] k / 2) := by
  ext p
  simp only [P, ι, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def, boxCoord]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun k => ?_, fun k => ?_⟩ <;> fin_cases k <;>
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons] <;>
      first
      | exact (abs_le.mp h0).1 | exact (abs_le.mp h0).2
      | exact (abs_le.mp h1).1 | exact (abs_le.mp h1).2
      | exact (abs_le.mp h2).1 | exact (abs_le.mp h2).2
  · rintro ⟨hl, hu⟩
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩
    · simpa using hl 0
    · simpa using hu 0
    · simpa using hl 1
    · simpa using hu 1
    · simpa using hl 2
    · simpa using hu 2

theorem measurableSet_P (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) : MeasurableSet (P a b c z e) := by
  rw [P_eq_preimage]
  exact (boxCoord_measurePreserving z e).measurable measurableSet_Icc

theorem volume_P {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    volume (P a b c z e) = O (a * b * c) := by
  rw [P_eq_preimage, (boxCoord_measurePreserving z e).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by nlinarith)]
  congr 1
  ring

theorem mem_P_iff {a b c : ℝ} {z p : V} {e : V ≃ₗᵢ[ℝ] V} :
    p ∈ P a b c z e ↔ ∀ k, -(![a, b, c] k / 2) ≤ boxCoord z e p k ∧
      boxCoord z e p k ≤ ![a, b, c] k / 2 := by
  rw [P_eq_preimage, mem_preimage, mem_Icc, Pi.le_def, Pi.le_def, forall_and]

/-- An `s`-ball centred in a frozen box whose sides are at least `s` meets it in volume
at least `s³/8`. -/
theorem volume_P_inter_ball {a b c s : ℝ} (hs : 0 < s) (ha : s ≤ a) (hb : s ≤ b) (hc : s ≤ c)
    {z p : V} {e : V ≃ₗᵢ[ℝ] V} (hp : p ∈ P a b c z e) :
    O (s ^ 3 / 8) ≤ volume (P a b c z e ∩ ball p s) := by
  classical
  set d : Fin 3 → ℝ := ![a, b, c] with hd
  have hds : ∀ k, s ≤ d k := by
    intro k; fin_cases k <;> simp [hd, ha, hb, hc]
  set q₀ := boxCoord z e p with hq₀
  have hq₀P := (mem_P_iff.mp hp)
  let l : Fin 3 → ℝ := fun k => if q₀ k + s / 2 ≤ d k / 2 then q₀ k else q₀ k - s / 2
  let u : Fin 3 → ℝ := fun k => l k + s / 2
  have hlu : ∀ k, -(d k / 2) ≤ l k ∧ u k ≤ d k / 2 ∧ q₀ k - s / 2 ≤ l k ∧ u k ≤ q₀ k + s / 2 := by
    intro k
    have h1 := (hq₀P k).1
    have h2 := (hq₀P k).2
    have h3 := hds k
    by_cases hcase : q₀ k + s / 2 ≤ d k / 2
    · have hl : l k = q₀ k := by simp [l, hcase]
      simp only [u, hl]
      refine ⟨h1, hcase, by linarith, le_refl _⟩
    · have hl : l k = q₀ k - s / 2 := by simp [l, hcase]
      have hcase' := not_le.mp hcase
      simp only [u, hl]
      refine ⟨by linarith, by linarith, le_refl _, by linarith⟩
  have hsub : boxCoord z e ⁻¹' Icc l u ⊆ P a b c z e ∩ ball p s := by
    intro x hx
    rw [mem_preimage, mem_Icc, Pi.le_def, Pi.le_def] at hx
    obtain ⟨hxl, hxu⟩ := hx
    refine ⟨mem_P_iff.mpr fun k => ⟨(hlu k).1.trans (hxl k), (hxu k).trans (hlu k).2.1⟩, ?_⟩
    rw [mem_ball, dist_eq_norm]
    have hk : ∀ k, |boxCoord z e x k - q₀ k| ≤ s / 2 := by
      intro k
      rw [abs_le]
      constructor <;> linarith [hxl k, hxu k, (hlu k).2.2.1, (hlu k).2.2.2]
    have heq : ‖x - p‖ = ‖e (x - z) - e (p - z)‖ := by
      rw [← map_sub, show x - z - (p - z) = x - p by abel, LinearIsometryEquiv.norm_map]
    rw [heq, EuclideanSpace.norm_eq]
    have hsq : ∑ k, ‖(e (x - z) - e (p - z)) k‖ ^ 2 ≤ 3 * (s / 2) ^ 2 := by
      rw [Fin.sum_univ_three]
      have hb' : ∀ k, ‖(e (x - z) - e (p - z)) k‖ ^ 2 ≤ (s / 2) ^ 2 := by
        intro k
        rw [Real.norm_eq_abs, sq_abs]
        have := hk k
        simp only [boxCoord, hq₀] at this
        have h' : (e (x - z) - e (p - z)) k = WithLp.ofLp (e (x - z)) k - WithLp.ofLp (e (p - z)) k :=
          rfl
        rw [h']
        nlinarith [abs_le.mp this, sq_abs (WithLp.ofLp (e (x - z)) k - WithLp.ofLp (e (p - z)) k)]
      linarith [hb' 0, hb' 1, hb' 2]
    calc Real.sqrt (∑ k, ‖(e (x - z) - e (p - z)) k‖ ^ 2) ≤ Real.sqrt (3 * (s / 2) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ < s := by
          rw [Real.sqrt_lt' hs]
          nlinarith
  calc O (s ^ 3 / 8) = volume (Icc l u) := by
        rw [Real.volume_Icc_pi, Fin.prod_univ_three]
        simp only [u, add_sub_cancel_left]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ = volume (boxCoord z e ⁻¹' Icc l u) :=
        ((boxCoord_measurePreserving z e).measure_preimage
          measurableSet_Icc.nullMeasurableSet).symm
    _ ≤ volume (P a b c z e ∩ ball p s) := measure_mono hsub

theorem convex_P (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) : Convex ℝ (P a b c z e) := by
  intro p hp q hq s t hs ht hst
  have key : ∀ k, ι (e (s • p + t • q - z)) k = s * ι (e (p - z)) k + t * ι (e (q - z)) k := by
    intro k
    have h1 : s • p + t • q - z = s • (p - z) + t • (q - z) := by
      calc s • p + t • q - z = s • p + t • q - (s + t) • z := by rw [hst, one_smul]
        _ = s • (p - z) + t • (q - z) := by rw [add_smul, smul_sub, smul_sub]; abel
    rw [h1, map_add, map_smul, map_smul]
    rfl
  obtain ⟨hp0, hp1, hp2⟩ := hp
  obtain ⟨hq0, hq1, hq2⟩ := hq
  have hcomb : ∀ (A B r : ℝ), |A| ≤ r → |B| ≤ r → |s * A + t * B| ≤ r := by
    intro A B r hA hB
    calc |s * A + t * B| ≤ |s * A| + |t * B| := abs_add_le _ _
      _ = s * |A| + t * |B| := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * r + t * r := by gcongr
      _ = r := by rw [← add_mul, hst, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [key 0]; exact hcomb _ _ _ hp0 hq0
  · rw [key 1]; exact hcomb _ _ _ hp1 hq1
  · rw [key 2]; exact hcomb _ _ _ hp2 hq2

theorem P_subset_closedBall (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    P a b c z e ⊆ closedBall z (a + b + c) := by
  intro p hp
  obtain ⟨h0, h1, h2⟩ := hp
  rw [mem_closedBall, dist_eq_norm, ← LinearIsometryEquiv.norm_map e, EuclideanSpace.norm_eq,
    Fin.sum_univ_three]
  simp only [ι] at h0 h1 h2
  have ha : 0 ≤ a := by linarith [abs_nonneg ((e (p - z)) 0)]
  have hb : 0 ≤ b := by linarith [abs_nonneg ((e (p - z)) 1)]
  have hc : 0 ≤ c := by linarith [abs_nonneg ((e (p - z)) 2)]
  rw [Real.sqrt_le_left (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [abs_nonneg ((e (p - z)) 0), abs_nonneg ((e (p - z)) 1), abs_nonneg ((e (p - z)) 2),
    sq_abs ((e (p - z)) 0), sq_abs ((e (p - z)) 1), sq_abs ((e (p - z)) 2)]

theorem totallyBounded_P (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) : TotallyBounded (P a b c z e) :=
  (isCompact_closedBall z (a + b + c)).totallyBounded.subset (P_subset_closedBall a b c z e)

end WangZahlLot.Obl.wz_move_three_thick_grains_gain
