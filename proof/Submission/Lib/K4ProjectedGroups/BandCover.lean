import Mathlib

/-!
# Covering a moving band by cap cells

A set `E` of incidences whose base points lie, for times in an interval of length `σ`, in a
band of widths `wZ`, `wY` moving with velocities `vZ`, `vY`, meets few cells of the grid of
side `h` in the base. If each cell carries mass at most `c₀`, then
`μ E ≤ (2σ/h + 4) (2(wZ + |vZ| h)/h + 4) (2(wY + |vY| h)/h + 4) c₀`.
No measurability of `E` is needed. This is how the joint caps of the frozen model are
integrated over a projected group (paper Section 8.2, "the projected groups").

Adapted from: here:o200 (session x0701, Submission/Obl/k4_finite_projected_horizontal_candidates/BandCover.lean).
-/

namespace Submission.Lib.K4ProjectedGroups

open MeasureTheory Set
open scoped Classical ENNReal

noncomputable section

theorem abs_floor_sub_floor_le (x y : ℝ) : |(⌊x⌋ : ℝ) - (⌊y⌋ : ℝ)| ≤ |x - y| + 1 := by
  have hx1 := Int.floor_le x
  have hx2 := Int.lt_floor_add_one x
  have hy1 := Int.floor_le y
  have hy2 := Int.lt_floor_add_one y
  rw [abs_le]
  constructor
  · have := neg_abs_le (x - y)
    linarith
  · have := le_abs_self (x - y)
    linarith

/-- A finite set of integers of diameter at most `L` has at most `2L + 2` elements:
it lies in `[m, m + ⌊L⌋]` for its least element `m`. -/
theorem card_int_le_of_diam (S : Finset ℤ) {L : ℝ} (hL : 0 ≤ L)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, |(i : ℝ) - (j : ℝ)| ≤ L) :
    (S.card : ℝ) ≤ 2 * L + 2 := by
  rcases S.eq_empty_or_nonempty with hS | hne
  · rw [hS, Finset.card_empty, Nat.cast_zero]; linarith
  set m := S.min' hne with hm
  have hsub : S ⊆ Finset.Icc m (m + ⌊L⌋) := by
    intro i hi
    rw [Finset.mem_Icc]
    refine ⟨Finset.min'_le S i hi, ?_⟩
    have h1 : ((i - m : ℤ) : ℝ) ≤ L := by
      have := hdiam i hi m (Finset.min'_mem S hne)
      push_cast
      exact (le_abs_self _).trans this
    have : i - m ≤ ⌊L⌋ := Int.le_floor.mpr h1
    omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have h0 : (0 : ℤ) ≤ ⌊L⌋ := Int.floor_nonneg.mpr hL
  have htn : ((m + ⌊L⌋ + 1 - m).toNat : ℝ) = (⌊L⌋ : ℝ) + 1 := by
    rw [show m + ⌊L⌋ + 1 - m = ⌊L⌋ + 1 by ring]
    rw [show (((⌊L⌋ + 1).toNat : ℕ) : ℝ) = ((((⌊L⌋ + 1).toNat : ℕ) : ℤ) : ℝ) from
      (Int.cast_natCast _).symm, Int.toNat_of_nonneg (by omega)]
    push_cast; ring
  have hfl := Int.floor_le L
  calc (S.card : ℝ) ≤ ((m + ⌊L⌋ + 1 - m).toNat : ℝ) := by exact_mod_cast hcard
    _ = (⌊L⌋ : ℝ) + 1 := htn
    _ ≤ 2 * L + 2 := by linarith

/-- The integer codes `⌊x/h⌋` of reals within distance `L` of each other differ by at
most `L/h + 1`. -/
theorem abs_code_sub_le {h x y L : ℝ} (hh : 0 < h) (hxy : |x - y| ≤ L) :
    |(⌊x / h⌋ : ℝ) - (⌊y / h⌋ : ℝ)| ≤ L / h + 1 := by
  have := abs_floor_sub_floor_le (x / h) (y / h)
  have h2 : |x / h - y / h| ≤ L / h := by
    rw [← sub_div, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right hxy hh.le
  linarith

/-- A finite set of integers whose images under a map into `ℤ` have bounded diameter. -/
theorem card_image_le_of_diam {ι : Type*} (S : Finset ι) (f : ι → ℤ) {L : ℝ} (hL : 0 ≤ L)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, |(f a : ℝ) - (f b : ℝ)| ≤ L) :
    ((S.image f).card : ℝ) ≤ 2 * L + 2 := by
  apply card_int_le_of_diam _ hL
  intro i hi j hj
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
  exact hdiam a ha b hb

/-- The base cell code at side `h`. -/
def cellCode (h : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℤ := fun i => ⌊x i / h⌋

/-- A finite set of codes contained in a product box, sliced by its first coordinate. -/
theorem card_codes_le {S : Finset (Fin 3 → ℤ)} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (h0 : ∀ p ∈ S, ∀ q ∈ S, |((p 0 : ℤ) : ℝ) - (q 0 : ℝ)| ≤ A)
    (h1 : ∀ p ∈ S, ∀ q ∈ S, p 0 = q 0 → |((p 1 : ℤ) : ℝ) - (q 1 : ℝ)| ≤ B)
    (h2 : ∀ p ∈ S, ∀ q ∈ S, p 0 = q 0 → |((p 2 : ℤ) : ℝ) - (q 2 : ℝ)| ≤ C) :
    (S.card : ℝ) ≤ (2 * A + 2) * ((2 * B + 2) * (2 * C + 2)) := by
  -- slice by the first coordinate
  have hslice : ∀ i ∈ S.image (fun p => p 0),
      ((S.filter (fun p => p 0 = i)).card : ℝ) ≤ (2 * B + 2) * (2 * C + 2) := by
    intro i _
    set T := S.filter (fun p => p 0 = i) with hT
    have hinj : Set.InjOn (fun p : Fin 3 → ℤ => (p 1, p 2)) (T : Set (Fin 3 → ℤ)) := by
      intro p hp q hq hpq
      have hp0 := (Finset.mem_filter.mp hp).2
      have hq0 := (Finset.mem_filter.mp hq).2
      simp only [Prod.mk.injEq] at hpq
      funext k
      fin_cases k
      · simp [hp0, hq0]
      · exact hpq.1
      · exact hpq.2
    have hsub : T.image (fun p : Fin 3 → ℤ => (p 1, p 2)) ⊆
        (T.image (fun p => p 1)) ×ˢ (T.image (fun p => p 2)) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    have hc1 : ((T.image (fun p => p 1)).card : ℝ) ≤ 2 * B + 2 := by
      apply card_image_le_of_diam T (fun p => p 1) hB
      intro a ha b hb
      exact h1 a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    have hc2 : ((T.image (fun p => p 2)).card : ℝ) ≤ 2 * C + 2 := by
      apply card_image_le_of_diam T (fun p => p 2) hC
      intro a ha b hb
      exact h2 a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    calc (T.card : ℝ) = ((T.image (fun p : Fin 3 → ℤ => (p 1, p 2))).card : ℝ) := by
          rw [Finset.card_image_of_injOn hinj]
      _ ≤ (((T.image (fun p => p 1)) ×ˢ (T.image (fun p => p 2))).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ = ((T.image (fun p => p 1)).card : ℝ) * ((T.image (fun p => p 2)).card : ℝ) := by
          rw [Finset.card_product, Nat.cast_mul]
      _ ≤ (2 * B + 2) * (2 * C + 2) := by
          apply mul_le_mul hc1 hc2 (Nat.cast_nonneg _)
          linarith
  have hc0 : ((S.image (fun p => p 0)).card : ℝ) ≤ 2 * A + 2 :=
    card_image_le_of_diam S (fun p => p 0) hA h0
  have hS : S.card = ∑ i ∈ S.image (fun p => p 0), (S.filter (fun p => p 0 = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem _ hp)
  calc (S.card : ℝ) = ∑ i ∈ S.image (fun p => p 0), ((S.filter (fun p => p 0 = i)).card : ℝ) := by
        rw [hS, Nat.cast_sum]
    _ ≤ ∑ _i ∈ S.image (fun p => p 0), (2 * B + 2) * (2 * C + 2) :=
        Finset.sum_le_sum hslice
    _ = ((S.image (fun p => p 0)).card : ℝ) * ((2 * B + 2) * (2 * C + 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * A + 2) * ((2 * B + 2) * (2 * C + 2)) := by
        apply mul_le_mul_of_nonneg_right hc0
        positivity

/-- A moving band in the base meets few cap cells. -/
theorem band_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Set Ω) (base : Ω → Fin 3 → ℝ) {h : ℝ} (hh : 0 < h) (c₀ : ℝ≥0∞)
    (hcap : ∀ q : Fin 3 → ℤ, μ {ω | ω ∈ T ∧ cellCode h (base ω) = q} ≤ c₀)
    (t₀ σ z₀ vZ wZ y₀ vY wY : ℝ) (hσ : 0 ≤ σ) (hwZ : 0 ≤ wZ) (hwY : 0 ≤ wY)
    (E : Set Ω) (hE : E ⊆ T)
    (hband : ∀ ω ∈ E, t₀ ≤ base ω 0 ∧ base ω 0 ≤ t₀ + σ ∧
      z₀ + vZ * base ω 0 ≤ base ω 1 ∧ base ω 1 ≤ z₀ + vZ * base ω 0 + wZ ∧
      y₀ + vY * base ω 0 ≤ base ω 2 ∧ base ω 2 ≤ y₀ + vY * base ω 0 + wY) :
    μ E ≤ ENNReal.ofReal ((2 * (σ / h + 1) + 2) *
      ((2 * ((wZ + |vZ| * h) / h + 1) + 2) * (2 * ((wY + |vY| * h) / h + 1) + 2))) * c₀ := by
  -- a finite box containing all codes of `E`
  -- diameter estimates for codes of `E`
  have hdiam0 : ∀ ω ∈ E, ∀ ω' ∈ E, |((cellCode h (base ω) 0 : ℤ) : ℝ) -
      (cellCode h (base ω') 0 : ℝ)| ≤ σ / h + 1 := by
    intro ω hω ω' hω'
    obtain ⟨a1, a2, -⟩ := hband ω hω
    obtain ⟨b1, b2, -⟩ := hband ω' hω'
    apply abs_code_sub_le hh
    rw [abs_le]; constructor <;> linarith
  have htime : ∀ ω ∈ E, ∀ ω' ∈ E, cellCode h (base ω) 0 = cellCode h (base ω') 0 →
      |base ω 0 - base ω' 0| ≤ h := by
    intro ω _ ω' _ heq
    have e1 := Int.floor_le (base ω 0 / h)
    have e2 := Int.lt_floor_add_one (base ω 0 / h)
    have e3 := Int.floor_le (base ω' 0 / h)
    have e4 := Int.lt_floor_add_one (base ω' 0 / h)
    simp only [cellCode] at heq
    rw [heq] at e1 e2
    have : |base ω 0 / h - base ω' 0 / h| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hh, div_le_iff₀ hh, one_mul] at this
    exact this
  have hdiam1 : ∀ ω ∈ E, ∀ ω' ∈ E, cellCode h (base ω) 0 = cellCode h (base ω') 0 →
      |((cellCode h (base ω) 1 : ℤ) : ℝ) - (cellCode h (base ω') 1 : ℝ)| ≤
        (wZ + |vZ| * h) / h + 1 := by
    intro ω hω ω' hω' heq
    have ht := htime ω hω ω' hω' heq
    obtain ⟨-, -, a3, a4, -⟩ := hband ω hω
    obtain ⟨-, -, b3, b4, -⟩ := hband ω' hω'
    apply abs_code_sub_le hh
    have hv : |vZ * (base ω 0 - base ω' 0)| ≤ |vZ| * h := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    rw [abs_le] at hv ⊢
    constructor <;> nlinarith [hv.1, hv.2]
  have hdiam2 : ∀ ω ∈ E, ∀ ω' ∈ E, cellCode h (base ω) 0 = cellCode h (base ω') 0 →
      |((cellCode h (base ω) 2 : ℤ) : ℝ) - (cellCode h (base ω') 2 : ℝ)| ≤
        (wY + |vY| * h) / h + 1 := by
    intro ω hω ω' hω' heq
    have ht := htime ω hω ω' hω' heq
    obtain ⟨-, -, -, -, a5, a6⟩ := hband ω hω
    obtain ⟨-, -, -, -, b5, b6⟩ := hband ω' hω'
    apply abs_code_sub_le hh
    have hv : |vY * (base ω 0 - base ω' 0)| ≤ |vY| * h := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    rw [abs_le] at hv ⊢
    constructor <;> nlinarith [hv.1, hv.2]
  -- all codes of `E` lie in a finite box around one of them
  by_cases hEe : E = ∅
  · rw [hEe, measure_empty]; exact bot_le
  obtain ⟨ω₀, hω₀⟩ := Set.nonempty_iff_ne_empty.mpr hEe
  set q₀ := cellCode h (base ω₀) with hq₀
  set D : ℝ := (σ / h + 1) + (wZ + |vZ| * σ) / h + 1 + (wY + |vY| * σ) / h + 1 with hD
  have hglob : ∀ ω ∈ E, ∀ i, |((cellCode h (base ω) i : ℤ) : ℝ) - (q₀ i : ℝ)| ≤ D := by
    intro ω hω
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hband ω hω
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hband ω₀ hω₀
    have hdt : |base ω 0 - base ω₀ 0| ≤ σ := by rw [abs_le]; constructor <;> linarith
    have hσh : 0 ≤ σ / h := div_nonneg hσ hh.le
    have hZh : 0 ≤ (wZ + |vZ| * σ) / h := div_nonneg (by positivity) hh.le
    have hYh : 0 ≤ (wY + |vY| * σ) / h := div_nonneg (by positivity) hh.le
    have e0 : |((cellCode h (base ω) 0 : ℤ) : ℝ) - (q₀ 0 : ℝ)| ≤ D := by
      have := abs_code_sub_le (x := base ω 0) (y := base ω₀ 0) hh hdt
      rw [hq₀, hD]
      simp only [cellCode]
      linarith
    have e1 : |((cellCode h (base ω) 1 : ℤ) : ℝ) - (q₀ 1 : ℝ)| ≤ D := by
      have hv : |vZ * (base ω 0 - base ω₀ 0)| ≤ |vZ| * σ := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdt (abs_nonneg _)
      have hz : |base ω 1 - base ω₀ 1| ≤ wZ + |vZ| * σ := by
        rw [abs_le] at hv ⊢; constructor <;> nlinarith [hv.1, hv.2]
      have := abs_code_sub_le (x := base ω 1) (y := base ω₀ 1) hh hz
      rw [hq₀, hD]
      simp only [cellCode]
      linarith
    have e2 : |((cellCode h (base ω) 2 : ℤ) : ℝ) - (q₀ 2 : ℝ)| ≤ D := by
      have hv : |vY * (base ω 0 - base ω₀ 0)| ≤ |vY| * σ := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdt (abs_nonneg _)
      have hy : |base ω 2 - base ω₀ 2| ≤ wY + |vY| * σ := by
        rw [abs_le] at hv ⊢; constructor <;> nlinarith [hv.1, hv.2]
      have := abs_code_sub_le (x := base ω 2) (y := base ω₀ 2) hh hy
      rw [hq₀, hD]
      simp only [cellCode]
      linarith
    intro i
    fin_cases i
    exacts [e0, e1, e2]
  set M : ℤ := ⌈D⌉ with hM
  let S : Finset (Fin 3 → ℤ) :=
    (Fintype.piFinset (fun i => Finset.Icc (q₀ i - M) (q₀ i + M))).filter
      (fun q => ∃ ω ∈ E, cellCode h (base ω) = q)
  have hmemS : ∀ ω ∈ E, cellCode h (base ω) ∈ S := by
    intro ω hω
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ω, hω, rfl⟩
    have hb := abs_le.mp (hglob ω hω i)
    have hDM : D ≤ (M : ℝ) := Int.le_ceil D
    rw [Finset.mem_Icc]
    constructor
    · have : ((q₀ i - M : ℤ) : ℝ) ≤ (cellCode h (base ω) i : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : (cellCode h (base ω) i : ℝ) ≤ ((q₀ i + M : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  have hcard : (S.card : ℝ) ≤ (2 * (σ / h + 1) + 2) *
      ((2 * ((wZ + |vZ| * h) / h + 1) + 2) * (2 * ((wY + |vY| * h) / h + 1) + 2)) := by
    apply card_codes_le (by positivity) (by positivity) (by positivity)
    · intro p hp q hq
      obtain ⟨ω, hω, rfl⟩ := (Finset.mem_filter.mp hp).2
      obtain ⟨ω', hω', rfl⟩ := (Finset.mem_filter.mp hq).2
      exact hdiam0 ω hω ω' hω'
    · intro p hp q hq hpq
      obtain ⟨ω, hω, rfl⟩ := (Finset.mem_filter.mp hp).2
      obtain ⟨ω', hω', rfl⟩ := (Finset.mem_filter.mp hq).2
      exact hdiam1 ω hω ω' hω' hpq
    · intro p hp q hq hpq
      obtain ⟨ω, hω, rfl⟩ := (Finset.mem_filter.mp hp).2
      obtain ⟨ω', hω', rfl⟩ := (Finset.mem_filter.mp hq).2
      exact hdiam2 ω hω ω' hω' hpq
  have hsub : E ⊆ ⋃ q ∈ S, {ω | ω ∈ T ∧ cellCode h (base ω) = q} := by
    intro ω hω
    exact Set.mem_biUnion (hmemS ω hω) ⟨hE hω, rfl⟩
  calc μ E ≤ μ (⋃ q ∈ S, {ω | ω ∈ T ∧ cellCode h (base ω) = q}) := measure_mono hsub
    _ ≤ ∑ q ∈ S, μ {ω | ω ∈ T ∧ cellCode h (base ω) = q} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ S, c₀ := Finset.sum_le_sum fun q _ => hcap q
    _ = (S.card : ℝ≥0∞) * c₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcard

end

end Submission.Lib.K4ProjectedGroups
