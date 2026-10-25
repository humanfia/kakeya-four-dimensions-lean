-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_long_grains_gain.CrossBox.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_long_grains_gain.Core

/-!
# A tube crossing a box between its long faces lies in an enlarged box

If a `δ`-tube around a unit segment meets a box `P a b c z e` (`δ ≤ a ≤ b ≤ c ≤ 1`,
`4 δ ≤ c`) at both long faces `ι (e (p - z)) 2 = ∓ c/2`, then its direction makes slopes
at most `6 a / c` and `6 b / c` with the long axis, and the whole tube lies in the box
`P (18 a / c) (18 b / c) 4 z e`.  Only the two crossing points are used.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_long_grains_gain

open MeasureTheory Set Metric
open scoped ENNReal

/-- A point of a tube is a point of the axis plus a vector shorter than `δ`. -/
lemma mem_tube_iff_exists {δ : ℝ} {x v p : V} (hp : p ∈ T δ x v) :
    ∃ τ ∈ Icc (0 : ℝ) 1, ∃ u : V, ‖u‖ < δ ∧ p = x + τ • v + u := by
  obtain ⟨s, hs, hps⟩ := Metric.mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hs
  obtain ⟨τ, hτ, rfl⟩ := hs
  refine ⟨τ, hτ, p - (x + τ • (x + v - x)), ?_, ?_⟩
  · rw [← dist_eq_norm]
    exact hps
  · simp only [add_sub_cancel_left]
    abel

lemma abs_coord_le_norm (p : V) (i : Fin 3) : |p i| ≤ ‖p‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p i

set_option maxHeartbeats 800000 in
/-- **Crossing tubes lie in an enlarged box.** -/
theorem tube_subset_enlarged_box {δ a b c : ℝ} {x v z : V} {e : V ≃ₗᵢ[ℝ] V}
    (hv : ‖v‖ = 1) (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc1 : c ≤ 1)
    (h4 : 4 * δ ≤ c)
    (hq₁ : ∃ p ∈ T δ x v ∩ P a b c z e, ι (e (p - z)) 2 = -c / 2)
    (hq₂ : ∃ p ∈ T δ x v ∩ P a b c z e, ι (e (p - z)) 2 = c / 2) :
    T δ x v ⊆ P (18 * a / c) (18 * b / c) 4 z e := by
  obtain ⟨q₁, ⟨hq₁T, hq₁P⟩, hq₁2⟩ := hq₁
  obtain ⟨q₂, ⟨hq₂T, hq₂P⟩, hq₂2⟩ := hq₂
  obtain ⟨τ₁, hτ₁, u₁, hu₁, rfl⟩ := mem_tube_iff_exists hq₁T
  obtain ⟨τ₂, hτ₂, u₂, hu₂, rfl⟩ := mem_tube_iff_exists hq₂T
  have hcpos : 0 < c := by linarith
  -- coordinates of the crossing points
  set w := e v with hw
  have hwn : ‖w‖ = 1 := by rw [hw, LinearIsometryEquiv.norm_map, hv]
  have hcoord : ∀ (τ : ℝ) (u : V) (i : Fin 3),
      (e (x + τ • v + u - z)) i = (e (x - z)) i + τ * w i + (e u) i := by
    intro τ u i
    have : x + τ • v + u - z = (x - z) + τ • v + u := by abel
    rw [this, map_add, map_add, map_smul]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hw]
  have heu : ∀ (u : V) (i : Fin 3), ‖u‖ < δ → |(e u) i| < δ := by
    intro u i hu
    calc |(e u) i| ≤ ‖e u‖ := abs_coord_le_norm _ _
      _ = ‖u‖ := LinearIsometryEquiv.norm_map _ _
      _ < δ := hu
  have hw_i : ∀ i : Fin 3, |w i| ≤ 1 := fun i => (abs_coord_le_norm w i).trans hwn.le
  have hP1 := hq₁P
  have hP2 := hq₂P
  simp only [P, mem_setOf_eq] at hP1 hP2
  change (e (x + τ₁ • v + u₁ - z)) 2 = -c / 2 at hq₁2
  change (e (x + τ₂ • v + u₂ - z)) 2 = c / 2 at hq₂2
  rw [hcoord] at hq₁2 hq₂2
  have e10 := hcoord τ₁ u₁ 0
  have e11 := hcoord τ₁ u₁ 1
  have e20 := hcoord τ₂ u₂ 0
  have e21 := hcoord τ₂ u₂ 1
  have hP10 : |(e (x + τ₁ • v + u₁ - z)) 0| ≤ a / 2 := hP1.1
  have hP11 : |(e (x + τ₁ • v + u₁ - z)) 1| ≤ b / 2 := hP1.2.1
  have hP20 : |(e (x + τ₂ • v + u₂ - z)) 0| ≤ a / 2 := hP2.1
  have hP21 : |(e (x + τ₂ • v + u₂ - z)) 1| ≤ b / 2 := hP2.2.1
  rw [e10] at hP10
  rw [e11] at hP11
  rw [e20] at hP20
  rw [e21] at hP21
  have hu10 := heu u₁ 0 hu₁
  have hu11 := heu u₁ 1 hu₁
  have hu12 := heu u₁ 2 hu₁
  have hu20 := heu u₂ 0 hu₂
  have hu21 := heu u₂ 1 hu₂
  have hu22 := heu u₂ 2 hu₂
  set D := τ₂ - τ₁ with hD
  have hDw : ∀ i : Fin 3, D * w i = τ₂ * w i - τ₁ * w i := fun i => by rw [hD]; ring
  -- the long-axis displacement
  have hD2 : c - 2 * δ ≤ D * w 2 := by
    have h1 := abs_lt.mp hu12
    have h2 := abs_lt.mp hu22
    rw [hDw 2]
    linarith
  have hD0 : |D * w 0| ≤ a + 2 * δ := by
    rw [hDw 0, abs_le]
    have h1 := abs_le.mp hP10
    have h2 := abs_le.mp hP20
    have h3 := abs_lt.mp hu10
    have h4 := abs_lt.mp hu20
    constructor <;> linarith
  have hD1 : |D * w 1| ≤ b + 2 * δ := by
    rw [hDw 1, abs_le]
    have h1 := abs_le.mp hP11
    have h2 := abs_le.mp hP21
    have h3 := abs_lt.mp hu11
    have h4 := abs_lt.mp hu21
    constructor <;> linarith
  have hDabs : c - 2 * δ ≤ |D| := by
    calc c - 2 * δ ≤ D * w 2 := hD2
      _ ≤ |D * w 2| := le_abs_self _
      _ = |D| * |w 2| := abs_mul _ _
      _ ≤ |D| * 1 := mul_le_mul_of_nonneg_left (hw_i 2) (abs_nonneg _)
      _ = |D| := mul_one _
  have hc2 : c / 2 ≤ |D| := by linarith
  have hDpos : 0 < |D| := by linarith
  -- slopes
  have hslope0 : |w 0| ≤ 6 * a / c := by
    have h1 : |D| * |w 0| ≤ a + 2 * δ := by rw [← abs_mul]; exact hD0
    have h2 : c / 2 * |w 0| ≤ a + 2 * δ :=
      (mul_le_mul_of_nonneg_right hc2 (abs_nonneg _)).trans h1
    rw [le_div_iff₀ hcpos]
    linarith
  have hslope1 : |w 1| ≤ 6 * b / c := by
    have h1 : |D| * |w 1| ≤ b + 2 * δ := by rw [← abs_mul]; exact hD1
    have h2 : c / 2 * |w 1| ≤ b + 2 * δ :=
      (mul_le_mul_of_nonneg_right hc2 (abs_nonneg _)).trans h1
    rw [le_div_iff₀ hcpos]
    linarith
  -- every point of the tube
  intro p hp
  obtain ⟨τ, hτ, u, hu, rfl⟩ := mem_tube_iff_exists hp
  have hτd : |τ - τ₁| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hτ.1, hτ.2, hτ₁.1, hτ₁.2]
  have hu0 := heu u 0 hu
  have hu1 := heu u 1 hu
  have hu2 := heu u 2 hu
  have ha0 : 0 ≤ a := hδ.le.trans hδa
  have hac : a / c ≥ a := by
    rw [ge_iff_le, le_div_iff₀ hcpos]
    calc a * c ≤ a * 1 := mul_le_mul_of_nonneg_left hc1 ha0
      _ = a := mul_one a
  have hbc' : b / c ≥ b := by
    rw [ge_iff_le, le_div_iff₀ hcpos]
    calc b * c ≤ b * 1 := mul_le_mul_of_nonneg_left hc1 (ha0.trans hab)
      _ = b := mul_one b
  have had : δ ≤ a / c := hδa.trans hac
  have hbd : δ ≤ b / c := (hδa.trans hab).trans hbc'
  refine ⟨?_, ?_, ?_⟩
  · change |(e (x + τ • v + u - z)) 0| ≤ 18 * a / c / 2
    rw [hcoord]
    -- coordinate relative to the first crossing point
    have hrel : (e (x - z)) 0 + τ * w 0 + (e u) 0 =
        ((e (x - z)) 0 + τ₁ * w 0 + (e u₁) 0) + (τ - τ₁) * w 0 + ((e u) 0 - (e u₁) 0) := by ring
    rw [hrel]
    have hmul : |(τ - τ₁) * w 0| ≤ 6 * a / c := by
      rw [abs_mul]
      calc |τ - τ₁| * |w 0| ≤ 1 * (6 * a / c) :=
            mul_le_mul hτd hslope0 (abs_nonneg _) zero_le_one
        _ = 6 * a / c := one_mul _
    have hdiff : |(e u) 0 - (e u₁) 0| ≤ 2 * δ := by
      have := abs_sub ((e u) 0) ((e u₁) 0)
      linarith
    have htri := abs_add_three (((e (x - z)) 0 + τ₁ * w 0 + (e u₁) 0)) ((τ - τ₁) * w 0)
      ((e u) 0 - (e u₁) 0)
    have ha2 : a / 2 ≤ a / c / 2 := by linarith
    have : 18 * a / c / 2 = 9 * (a / c) := by ring
    rw [this]
    have : 6 * a / c = 6 * (a / c) := by ring
    linarith
  · change |(e (x + τ • v + u - z)) 1| ≤ 18 * b / c / 2
    rw [hcoord]
    have hrel : (e (x - z)) 1 + τ * w 1 + (e u) 1 =
        ((e (x - z)) 1 + τ₁ * w 1 + (e u₁) 1) + (τ - τ₁) * w 1 + ((e u) 1 - (e u₁) 1) := by ring
    rw [hrel]
    have hmul : |(τ - τ₁) * w 1| ≤ 6 * b / c := by
      rw [abs_mul]
      calc |τ - τ₁| * |w 1| ≤ 1 * (6 * b / c) :=
            mul_le_mul hτd hslope1 (abs_nonneg _) zero_le_one
        _ = 6 * b / c := one_mul _
    have hdiff : |(e u) 1 - (e u₁) 1| ≤ 2 * δ := by
      have := abs_sub ((e u) 1) ((e u₁) 1)
      linarith
    have htri := abs_add_three (((e (x - z)) 1 + τ₁ * w 1 + (e u₁) 1)) ((τ - τ₁) * w 1)
      ((e u) 1 - (e u₁) 1)
    have hb2 : b / 2 ≤ b / c / 2 := by linarith
    have : 18 * b / c / 2 = 9 * (b / c) := by ring
    rw [this]
    have : 6 * b / c = 6 * (b / c) := by ring
    linarith
  · change |(e (x + τ • v + u - z)) 2| ≤ 4 / 2
    rw [hcoord]
    have hrel : (e (x - z)) 2 + τ * w 2 + (e u) 2 =
        ((e (x - z)) 2 + τ₁ * w 2 + (e u₁) 2) + (τ - τ₁) * w 2 + ((e u) 2 - (e u₁) 2) := by ring
    rw [hrel, hq₁2]
    have hmul : |(τ - τ₁) * w 2| ≤ 1 := by
      rw [abs_mul]
      calc |τ - τ₁| * |w 2| ≤ 1 * 1 := mul_le_mul hτd (hw_i 2) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul _
    have hdiff : |(e u) 2 - (e u₁) 2| ≤ 2 * δ := by
      have := abs_sub ((e u) 2) ((e u₁) 2)
      linarith
    have htri := abs_add_three (-c / 2) ((τ - τ₁) * w 2) ((e u) 2 - (e u₁) 2)
    have hcabs : |-c / 2| = c / 2 := by
      rw [abs_of_neg (by linarith)]
      ring
    linarith

end WangZahlLot.Obl.wz_move_two_long_grains_gain
