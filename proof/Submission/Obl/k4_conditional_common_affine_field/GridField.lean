import Mathlib
import Submission.Obl.k4_conditional_common_affine_field.AnchorRows
import Submission.Obl.k4_conditional_common_affine_field.Selection
import Submission.Obl.k4_conditional_common_affine_field.Bilinear

set_option autoImplicit false

/-!
# The common bilinear field on a grid of two axis directions

Paper, Section 8, "A common coefficient field", the grid part.  Points `p ∈ W` of a finite measure
have axis intercepts `b₁ p, b₂ p` with `b₁ - b₂ = t u`; rows are the `ω`-strips of `b₁`, columns
the `ω`-strips of `b₂`.  Every point agrees to `E` with an option (affine first coefficient in time,
constant second coefficient) of its row's list and of its column's list, at most `n` options each,
and every grid cell carries mass at most `κ ω²`.  Then one bilinear function of `(b₁, b₂)` and one
constant fit the two coefficients on a dense part of `W`.

Proof: select one option per row, then per column (`exists_measure_selection`); choose two anchor
rows at height distance `γ` such that the columns occupied at both carry dense mass
(`exists_dense_anchor_rows`); interpolate each such column between its two anchors
(`anchor_fit`).
-/

namespace Submission.Obl.k4_conditional_common_affine_field

open MeasureTheory

/-- The height separation of the anchor rows. -/
noncomputable def gridGap (m : ℝ) (n : ℕ) (κ B : ℝ) : ℝ :=
  (m / (n : ℝ) ^ 2) ^ 2 / (384 * κ ^ 2 * B ^ 3)

/-- The dense mass kept by the grid field. -/
noncomputable def gridMass (m : ℝ) (n : ℕ) (κ B : ℝ) : ℝ :=
  (m / (n : ℝ) ^ 2) ^ 3 / (512 * κ ^ 2 * B ^ 4)

/-- The fitting error of the grid field. -/
noncomputable def gridErr (E ω u B γ : ℝ) : ℝ :=
  3 * E + 2 * (2 * E + 4 * B * ω / |u|) * (|u| + 3 * B) / γ

/-- Rows within height `γ` of a row. -/
theorem card_near_rows (J : Finset ℤ) {ω γ : ℝ} (hω : 0 < ω) (j : ℤ) :
    (J.filter fun j' : ℤ => |(j : ℝ) * ω - ((j' : ℤ) : ℝ) * ω| < γ).card ≤ 2 * ⌊γ / ω⌋₊ + 1 := by
  set a := ⌊γ / ω⌋₊ with ha
  have hsub : (J.filter fun j' : ℤ => |(j : ℝ) * ω - ((j' : ℤ) : ℝ) * ω| < γ) ⊆
      Finset.Icc (j - a) (j + a) := by
    intro j' hj'
    rw [Finset.mem_filter] at hj'
    rw [Finset.mem_Icc]
    have h1 : |((j - j' : ℤ) : ℝ)| * ω < γ := by
      have : |(j : ℝ) * ω - ((j' : ℤ) : ℝ) * ω| = |((j - j' : ℤ) : ℝ)| * ω := by
        push_cast; rw [← sub_mul, abs_mul, abs_of_pos hω]
      linarith [hj'.2]
    have h2 : ((j - j').natAbs : ℝ) ≤ γ / ω := by
      rw [le_div_iff₀ hω, Nat.cast_natAbs, Int.cast_abs]
      exact h1.le
    have h3 : (j - j').natAbs ≤ a := Nat.le_floor h2
    omega
  calc _ ≤ (Finset.Icc (j - a) (j + a)).card := Finset.card_le_card hsub
    _ = 2 * a + 1 := by rw [Int.card_Icc]; omega

/-- A point of a floor strip is within the strip width of its left edge. -/
theorem abs_sub_floor_mul_le {x ω : ℝ} (hω : 0 < ω) {j : ℤ} (h : ⌊x / ω⌋ = j) :
    |x - (j : ℝ) * ω| ≤ ω := by
  have h1 := Int.floor_le (x / ω)
  have h2 := Int.lt_floor_add_one (x / ω)
  rw [h] at h1 h2
  rw [le_div_iff₀ hω] at h1
  rw [div_lt_iff₀ hω] at h2
  rw [abs_le]; constructor <;> nlinarith

/-- Two points of one floor strip are within the strip width. -/
theorem abs_sub_le_of_floor_eq {x x' ω : ℝ} (hω : 0 < ω) (h : ⌊x / ω⌋ = ⌊x' / ω⌋) :
    |x - x'| ≤ ω := by
  have h1 := Int.floor_le (x / ω)
  have h2 := Int.lt_floor_add_one (x / ω)
  have h3 := Int.floor_le (x' / ω)
  have h4 := Int.lt_floor_add_one (x' / ω)
  rw [h] at h1 h2
  rw [le_div_iff₀ hω] at h1 h3
  rw [div_lt_iff₀ hω] at h2 h4
  rw [abs_le]; constructor <;> nlinarith

/-- The numerics of the anchor row choice. -/
theorem anchor_numeric {m₂ T c κ ω B G γ : ℝ} (hm₂ : 0 < m₂) (hT : m₂ ≤ T) (hc : 0 < c)
    (hcB : c ≤ 4 * B / ω) (hκ : 0 < κ) (hω : 0 < ω) (hB : 0 < B) (_hG0 : 0 ≤ G)
    (hγ : γ = m₂ ^ 2 / (384 * κ ^ 2 * B ^ 3)) (hG : G ≤ 3 * γ / ω) :
    0 < T ^ 3 / ((κ * ω ^ 2) ^ 2 * c ^ 2) - G * c * T ∧
      m₂ ^ 3 / (512 * κ ^ 2 * B ^ 4) ≤
        (T ^ 3 / ((κ * ω ^ 2) ^ 2 * c ^ 2) - G * c * T) / c ^ 2 := by
  subst hγ
  have hTpos : 0 < T := lt_of_lt_of_le hm₂ hT
  obtain ⟨M, hM⟩ : ∃ M, M = κ * ω ^ 2 := ⟨_, rfl⟩
  rw [← hM]
  have hMpos : 0 < M := by rw [hM]; positivity
  have hkey : G * (2 * M ^ 2 * c ^ 3) ≤ T ^ 2 := by
    have hc3 : c ^ 3 ≤ (4 * B / ω) ^ 3 := pow_le_pow_left₀ hc.le hcB 3
    have hval : 3 * (m₂ ^ 2 / (384 * κ ^ 2 * B ^ 3)) / ω * (2 * M ^ 2 * (4 * B / ω) ^ 3) =
        m₂ ^ 2 := by
      rw [hM]; field_simp; ring
    calc G * (2 * M ^ 2 * c ^ 3) ≤
          3 * (m₂ ^ 2 / (384 * κ ^ 2 * B ^ 3)) / ω * (2 * M ^ 2 * (4 * B / ω) ^ 3) := by
          apply mul_le_mul hG _ (by positivity) (by positivity)
          gcongr
      _ = m₂ ^ 2 := hval
      _ ≤ T ^ 2 := pow_le_pow_left₀ hm₂.le hT 2
  have hnear : G * c * T ≤ T ^ 3 / (2 * M ^ 2 * c ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : G * c * T * (2 * M ^ 2 * c ^ 2) = (G * (2 * M ^ 2 * c ^ 3)) * T := by ring
    rw [this]
    calc (G * (2 * M ^ 2 * c ^ 3)) * T ≤ T ^ 2 * T := mul_le_mul_of_nonneg_right hkey hTpos.le
      _ = T ^ 3 := by ring
  have hhalf : T ^ 3 / (M ^ 2 * c ^ 2) = 2 * (T ^ 3 / (2 * M ^ 2 * c ^ 2)) := by
    field_simp
  have hpos2 : 0 < T ^ 3 / (2 * M ^ 2 * c ^ 2) := by positivity
  constructor
  · linarith
  · rw [le_div_iff₀ (by positivity)]
    have h1 : T ^ 3 / (2 * M ^ 2 * c ^ 2) ≤ T ^ 3 / (M ^ 2 * c ^ 2) - G * c * T := by linarith
    have h2 : m₂ ^ 3 / (512 * κ ^ 2 * B ^ 4) * c ^ 2 ≤ T ^ 3 / (2 * M ^ 2 * c ^ 2) := by
      have hT3 : m₂ ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hm₂.le hT 3
      have e1 : m₂ ^ 3 / (512 * κ ^ 2 * B ^ 4) * c ^ 2 =
          m₂ ^ 3 * c ^ 2 * ω ^ 4 / (2 * M ^ 2 * (4 * B) ^ 4) := by
        rw [hM]; field_simp; ring
      rw [e1, div_le_div_iff₀ (by positivity) (by positivity)]
      have hcω : c * ω ≤ 4 * B := by rwa [le_div_iff₀ hω] at hcB
      have hcω4 : (c * ω) ^ 4 ≤ (4 * B) ^ 4 := pow_le_pow_left₀ (by positivity) hcω 4
      calc m₂ ^ 3 * c ^ 2 * ω ^ 4 * (2 * M ^ 2 * c ^ 2) = m₂ ^ 3 * (2 * M ^ 2) * (c * ω) ^ 4 := by
            ring
        _ ≤ T ^ 3 * (2 * M ^ 2) * (4 * B) ^ 4 := by gcongr
        _ = T ^ 3 * (2 * M ^ 2 * (4 * B) ^ 4) := by ring
    linarith

/-- **The common bilinear field on the grid.** -/
theorem grid_common_field {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (W : Set X) (hW : MeasurableSet W) (t b₁ b₂ : X → ℝ) (F : X → Fin 2 → ℝ)
    (ht : Measurable t) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) (hF : Measurable F)
    (rowOpts colOpts : ℤ → Finset (Fin 3 → ℝ)) {ω u B E κ m : ℝ} {n : ℕ}
    (hω : 0 < ω) (hu : u ≠ 0) (hB : 1 ≤ B) (hE : 0 ≤ E) (hκ : 0 < κ) (hm : 0 < m) (hn : 1 ≤ n)
    (hωB : ω ≤ B)
    (hrel : ∀ p ∈ W, b₁ p - b₂ p = t p * u)
    (hbd : ∀ p ∈ W, |t p| ≤ 1 ∧ |b₁ p| ≤ B ∧ |b₂ p| ≤ B)
    (hrowN : ∀ j, (rowOpts j).card ≤ n) (hcolN : ∀ i, (colOpts i).card ≤ n)
    (hrowB : ∀ j, ∀ a ∈ rowOpts j, ∀ k, |a k| ≤ B)
    (hcolB : ∀ i, ∀ a ∈ colOpts i, ∀ k, |a k| ≤ B)
    (hrowFit : ∀ p ∈ W, ∃ a ∈ rowOpts ⌊b₁ p / ω⌋,
      |F p 0 - a 0 - a 1 * t p| ≤ E ∧ |F p 1 - a 2| ≤ E)
    (hcolFit : ∀ p ∈ W, ∃ a ∈ colOpts ⌊b₂ p / ω⌋,
      |F p 0 - a 0 - a 1 * t p| ≤ E ∧ |F p 1 - a 2| ≤ E)
    (hcell : ∀ i j : ℤ,
      μ (W ∩ {p | ⌊b₁ p / ω⌋ = j ∧ ⌊b₂ p / ω⌋ = i}) ≤ ENNReal.ofReal (κ * ω ^ 2))
    (hmass : ENNReal.ofReal m ≤ μ W)
    (hωγ : ω ≤ gridGap m n κ B) :
    ∃ (β : Fin 4 → ℝ) (c : ℝ) (W' : Set X), MeasurableSet W' ∧ W' ⊆ W ∧
      (∀ k, |β k| ≤ 12 * B ^ 3 * (1 + 1 / |u|) * (1 + 1 / gridGap m n κ B)) ∧ |c| ≤ B ∧
      ENNReal.ofReal (gridMass m n κ B) ≤ μ W' ∧
      ∀ p ∈ W', |F p 0 - bilEval β (b₁ p) (b₂ p)| ≤ gridErr E ω u B (gridGap m n κ B) ∧
        |F p 1 - c| ≤ gridErr E ω u B (gridGap m n κ B) := by
  classical
  set γ := gridGap m n κ B with hγdef
  set m₂ : ℝ := m / (n : ℝ) ^ 2 with hm₂
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm₂pos : 0 < m₂ := by positivity
  have hB0 : 0 < B := by linarith
  have hγpos : 0 < γ := by rw [hγdef, gridGap]; positivity
  have hupos : 0 < |u| := abs_pos.mpr hu
  -- indices
  let row : X → ℤ := fun p => ⌊b₁ p / ω⌋
  let col : X → ℤ := fun p => ⌊b₂ p / ω⌋
  have hrowM : Measurable row := Int.measurable_floor.comp (hb₁.div_const ω)
  have hcolM : Measurable col := Int.measurable_floor.comp (hb₂.div_const ω)
  set Rg : Finset ℤ := Finset.Icc ⌊-B / ω⌋ ⌊B / ω⌋ with hRgdef
  have hmemRg : ∀ x : ℝ, |x| ≤ B → ⌊x / ω⌋ ∈ Rg := by
    intro x hx
    rw [hRgdef, Finset.mem_Icc]
    constructor
    · apply Int.floor_mono; apply div_le_div_of_nonneg_right _ hω.le
      linarith [neg_abs_le x]
    · apply Int.floor_mono; apply div_le_div_of_nonneg_right _ hω.le
      linarith [le_abs_self x]
  have hRgRow : ∀ p ∈ W, row p ∈ Rg := fun p hp => hmemRg _ (hbd p hp).2.1
  have hRgCol : ∀ p ∈ W, col p ∈ Rg := fun p hp => hmemRg _ (hbd p hp).2.2
  have hRgcard : (Rg.card : ℝ) ≤ 4 * B / ω := by
    rw [hRgdef, Int.card_Icc]
    have h1 := Int.floor_le (B / ω)
    have h2 := Int.lt_floor_add_one (-B / ω)
    have h3 : (0 : ℤ) ≤ ⌊B / ω⌋ + 1 - ⌊-B / ω⌋ := by
      have : (⌊-B / ω⌋ : ℝ) ≤ ⌊B / ω⌋ := by
        exact_mod_cast Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hω.le)
      have : ⌊-B / ω⌋ ≤ ⌊B / ω⌋ := by exact_mod_cast this
      omega
    rw [show ((⌊B / ω⌋ + 1 - ⌊-B / ω⌋).toNat : ℝ) = ((⌊B / ω⌋ + 1 - ⌊-B / ω⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h3]
    push_cast
    have h4 : 2 ≤ 2 * B / ω := by rw [le_div_iff₀ hω]; linarith
    have h5 : -B / ω = -(B / ω) := by ring
    have : 4 * B / ω = 2 * (B / ω) + 2 * B / ω := by ring
    linarith
  have hRgy : ∀ j ∈ Rg, |(j : ℝ) * ω| ≤ 2 * B := by
    intro j hj
    rw [hRgdef, Finset.mem_Icc] at hj
    have h1 : (j : ℝ) ≤ B / ω := le_trans (by exact_mod_cast hj.2) (Int.floor_le _)
    have h2 : -B / ω - 1 < (j : ℝ) := by
      have := Int.lt_floor_add_one (-B / ω)
      have h' : (⌊-B / ω⌋ : ℝ) ≤ j := by exact_mod_cast hj.1
      linarith
    rw [le_div_iff₀ hω] at h1
    have h2' : (-B / ω - 1) * ω < (j : ℝ) * ω := mul_lt_mul_of_pos_right h2 hω
    have h3 : (-B / ω - 1) * ω = -B - ω := by field_simp
    rw [abs_le]; constructor <;> nlinarith
  -- agreement sets
  let Ag : (Fin 3 → ℝ) → Set X := fun a =>
    {p | |F p 0 - a 0 - a 1 * t p| ≤ E ∧ |F p 1 - a 2| ≤ E}
  have hF0 : Measurable fun p => F p 0 := (measurable_pi_apply 0).comp hF
  have hF1 : Measurable fun p => F p 1 := (measurable_pi_apply 1).comp hF
  have hAg : ∀ a, MeasurableSet (Ag a) := by
    intro a
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le ((hF0.sub_const _).sub (ht.const_mul _)).abs measurable_const
    · exact measurableSet_le (hF1.sub_const _).abs measurable_const
  -- selection of one option per row, then per column
  obtain ⟨selR, hselR, hSR, hW1⟩ :=
    exists_measure_selection μ W hW row hrowM Rg hRgRow rowOpts hrowN Ag hAg hrowFit
  set W₁ := W ∩ {p | p ∈ Ag (selR (row p))} with hW₁def
  have hW₁ : MeasurableSet W₁ := hW.inter hSR
  obtain ⟨selC, hselC, hSC, hW2⟩ :=
    exists_measure_selection μ W₁ hW₁ col hcolM Rg (fun p hp => hRgCol p hp.1) colOpts hcolN Ag
      hAg (fun p hp => hcolFit p hp.1)
  set W₂ := W₁ ∩ {p | p ∈ Ag (selC (col p))} with hW₂def
  have hW₂ : MeasurableSet W₂ := hW₁.inter hSC
  have hW₂W : W₂ ⊆ W := fun p hp => hp.1.1
  -- the mass of `W₂`
  have hW₂mass : m₂ ≤ (μ W₂).toReal := by
    have h1 : μ W ≤ (n : ENNReal) ^ 2 * μ W₂ := by
      calc μ W ≤ n * μ W₁ := hW1
        _ ≤ n * (n * μ W₂) := by gcongr
        _ = (n : ENNReal) ^ 2 * μ W₂ := by ring
    have h2 : ENNReal.ofReal m ≤ ENNReal.ofReal ((n : ℝ) ^ 2) * μ W₂ := by
      rw [ENNReal.ofReal_pow hn0.le, ENNReal.ofReal_natCast]
      exact hmass.trans h1
    have h3 : m ≤ (n : ℝ) ^ 2 * (μ W₂).toReal := by
      have hfin : μ W₂ ≠ ⊤ := measure_ne_top μ W₂
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h2
      rwa [ENNReal.toReal_ofReal hm.le, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)] at this
    rw [hm₂, div_le_iff₀ (by positivity)]
    linarith
  -- the cell weights
  let w : ℤ → ℤ → ℝ := fun i j => (μ (W₂ ∩ {p | row p = j ∧ col p = i})).toReal
  have hw0 : ∀ i j, 0 ≤ w i j := fun _ _ => ENNReal.toReal_nonneg
  have hcellM : ∀ i j, MeasurableSet {p | row p = j ∧ col p = i} := fun i j =>
    (hrowM (measurableSet_singleton j)).inter (hcolM (measurableSet_singleton i))
  have hwM : ∀ i j, w i j ≤ κ * ω ^ 2 := by
    intro i j
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    exact (measure_mono (Set.inter_subset_inter_left _ hW₂W)).trans (hcell i j)
  have hcolsum : ∀ i, ∑ j ∈ Rg, w i j = (μ (W₂ ∩ col ⁻¹' {i})).toReal := by
    intro i
    rw [measure_eq_sum_fibers μ (W₂ ∩ col ⁻¹' {i}) (hW₂.inter (hcolM (measurableSet_singleton i)))
      row hrowM Rg (fun p hp => hRgRow p (hW₂W hp.1)),
      ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]
    apply Finset.sum_congr rfl
    intro j _
    have hset : W₂ ∩ col ⁻¹' {i} ∩ row ⁻¹' {j} = W₂ ∩ {p | row p = j ∧ col p = i} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      tauto
    rw [hset]
  have hwsum : ∑ i ∈ Rg, ∑ j ∈ Rg, w i j = (μ W₂).toReal := by
    rw [measure_eq_sum_fibers μ W₂ hW₂ col hcolM Rg (fun p hp => hRgCol p (hW₂W hp)),
      ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)]
    exact Finset.sum_congr rfl fun i _ => hcolsum i
  -- the anchor rows
  have hTm : m₂ ≤ ∑ i ∈ Rg, ∑ j ∈ Rg, w i j := by rw [hwsum]; exact hW₂mass
  have hcpos : (0 : ℝ) < Rg.card := by
    have : 0 < Rg.card := Finset.card_pos.mpr ⟨⌊B / ω⌋, by
      rw [hRgdef, Finset.mem_Icc]
      refine ⟨Int.floor_mono ?_, le_rfl⟩
      apply div_le_div_of_nonneg_right _ hω.le
      linarith⟩
    exact_mod_cast this
  have hG : ((2 * ⌊γ / ω⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * γ / ω := by
    push_cast
    have h1 : (⌊γ / ω⌋₊ : ℝ) ≤ γ / ω := Nat.floor_le (by positivity)
    have h2 : 1 ≤ γ / ω := by rw [le_div_iff₀ hω]; linarith
    have : 3 * γ / ω = 3 * (γ / ω) := by ring
    linarith
  have hγeq : γ = m₂ ^ 2 / (384 * κ ^ 2 * B ^ 3) := by rw [hγdef, gridGap]
  obtain ⟨hpos, hbound⟩ := anchor_numeric hm₂pos hTm hcpos hRgcard hκ hω hB0
    (Nat.cast_nonneg _) hγeq hG
  obtain ⟨j₁, hj₁, j₂, hj₂, hsep, hpw⟩ := exists_dense_anchor_rows Rg Rg w hw0
    (M := κ * ω ^ 2) (by positivity) hwM (fun j => (j : ℝ) * ω) (γ := γ)
    (G := 2 * ⌊γ / ω⌋₊ + 1) (fun j _ => card_near_rows Rg hω j) hpos
  -- the dense set of columns occupied at both anchor rows
  set Igood := Rg.filter (fun i => 0 < w i j₁ ∧ 0 < w i j₂) with hIgood
  set W' := W₂ ∩ {p | col p ∈ Igood} with hW'def
  have hW' : MeasurableSet W' := hW₂.inter (hcolM (Finset.measurableSet _))
  have hW'mass : gridMass m n κ B ≤ (μ W').toReal := by
    have hW'sum : (μ W').toReal = pairWeight Rg Rg w j₁ j₂ := by
      rw [measure_eq_sum_fibers μ W' hW' col hcolM Igood (fun p hp => hp.2),
        ENNReal.toReal_sum (fun i _ => measure_ne_top μ _), pairWeight, ← Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcolsum i]
      have hset : W' ∩ col ⁻¹' {i} = W₂ ∩ col ⁻¹' {i} := by
        ext p
        simp only [hW'def, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; refine ⟨⟨h1, ?_⟩, h3⟩; rw [h3]; exact hi
      rw [hset]
    rw [hW'sum]
    refine le_trans ?_ hpw
    refine le_trans (le_of_eq ?_) hbound
    rw [gridMass]
  have hW'pos : 0 < μ W' := by
    have : 0 < (μ W').toReal := lt_of_lt_of_le (by rw [gridMass]; positivity) hW'mass
    exact ENNReal.toReal_pos_iff.mp this |>.1
  -- anchors
  have hanchor : ∀ i ∈ Igood, ∀ j, 0 < w i j → ∃ q ∈ W₂, row q = j ∧ col q = i := by
    intro i _ j hw
    have hne : μ (W₂ ∩ {p | row p = j ∧ col p = i}) ≠ 0 := by
      intro h0
      have : w i j = 0 := by simp only [w, h0, ENNReal.toReal_zero]
      linarith
    obtain ⟨q, hq⟩ := nonempty_of_measure_ne_zero hne
    exact ⟨q, hq.1, hq.2.1, hq.2.2⟩
  obtain ⟨p₀, hp₀⟩ := nonempty_of_measure_ne_zero hW'pos.ne'
  have hi₀ : col p₀ ∈ Igood := hp₀.2
  obtain ⟨q₀₁, hq₀₁, hq₀₁r, -⟩ := hanchor _ hi₀ j₁ (Finset.mem_filter.mp hi₀).2.1
  obtain ⟨q₀₂, hq₀₂, hq₀₂r, -⟩ := hanchor _ hi₀ j₂ (Finset.mem_filter.mp hi₀).2.2
  have hh₁mem : selR j₁ ∈ rowOpts j₁ := by
    have := hselR q₀₁ (hW₂W hq₀₁); rwa [hq₀₁r] at this
  have hh₂mem : selR j₂ ∈ rowOpts j₂ := by
    have := hselR q₀₂ (hW₂W hq₀₂); rwa [hq₀₂r] at this
  have hy₁ : |(j₁ : ℝ) * ω| ≤ 2 * B := hRgy j₁ hj₁
  have hy₂ : |(j₂ : ℝ) * ω| ≤ 2 * B := hRgy j₂ hj₂
  have hyne : (j₁ : ℝ) * ω ≠ (j₂ : ℝ) * ω := by
    intro h; rw [h, sub_self, abs_zero] at hsep; linarith
  refine ⟨bilCoeffs (selR j₁) (selR j₂) ((j₁ : ℝ) * ω) ((j₂ : ℝ) * ω) u, selR j₁ 2, W', hW',
    fun p hp => hW₂W hp.1, ?_, hrowB j₁ _ hh₁mem 2, ?_, ?_⟩
  · intro k
    exact abs_bilCoeffs_le _ _ hu hγpos hB (hrowB j₁ _ hh₁mem) (hrowB j₂ _ hh₂mem) hy₁ hy₂ hsep k
  · rw [← ENNReal.ofReal_toReal (measure_ne_top μ W')]
    exact ENNReal.ofReal_le_ofReal hW'mass
  · intro p hp
    have hpW₂ : p ∈ W₂ := hp.1
    have hi : col p ∈ Igood := hp.2
    obtain ⟨q₁, hq₁, hq₁r, hq₁c⟩ := hanchor _ hi j₁ (Finset.mem_filter.mp hi).2.1
    obtain ⟨q₂, hq₂, hq₂r, hq₂c⟩ := hanchor _ hi j₂ (Finset.mem_filter.mp hi).2.2
    -- fits at the target and the anchors
    have hpV : p ∈ Ag (selC (col p)) := hpW₂.2
    have hq₁V : q₁ ∈ Ag (selC (col p)) := by
      have h : q₁ ∈ Ag (selC (col q₁)) := hq₁.2; rwa [hq₁c] at h
    have hq₂V : q₂ ∈ Ag (selC (col p)) := by
      have h : q₂ ∈ Ag (selC (col q₂)) := hq₂.2; rwa [hq₂c] at h
    have hq₁h : q₁ ∈ Ag (selR j₁) := by
      have h : q₁ ∈ Ag (selR (row q₁)) := hq₁.1.2; rwa [hq₁r] at h
    have hq₂h : q₂ ∈ Ag (selR j₂) := by
      have h : q₂ ∈ Ag (selR (row q₂)) := hq₂.1.2; rwa [hq₂r] at h
    have hVmem : selC (col p) ∈ colOpts (col p) := hselC p hpW₂.1
    have hVB : |selC (col p) 1| ≤ B := hcolB _ _ hVmem 1
    have hpbd := hbd p (hW₂W hpW₂)
    -- anchor geometry
    have hb₁q₁ : |b₁ q₁ - (j₁ : ℝ) * ω| ≤ ω := abs_sub_floor_mul_le hω hq₁r
    have hb₁q₂ : |b₁ q₂ - (j₂ : ℝ) * ω| ≤ ω := abs_sub_floor_mul_le hω hq₂r
    have hb₂q₁ : |b₂ q₁ - b₂ p| ≤ ω := abs_sub_le_of_floor_eq hω (by
      show col q₁ = col p; rw [hq₁c])
    have hb₂q₂ : |b₂ q₂ - b₂ p| ≤ ω := abs_sub_le_of_floor_eq hω (by
      show col q₂ = col p; rw [hq₂c])
    have hfit := anchor_fit (V := selC (col p)) (h₁ := selR j₁) (h₂ := selR j₂) hu hyne
      (hrel p (hW₂W hpW₂)) (hrel q₁ (hW₂W hq₁)) (hrel q₂ (hW₂W hq₂)) hpV.1 hq₁V.1 hq₁h.1 hq₂V.1
      hq₂h.1 hb₁q₁ hb₂q₁ hb₁q₂ hb₂q₂ hVB (hrowB j₁ _ hh₁mem 1) (hrowB j₂ _ hh₂mem 1)
    have hratio := interp_ratio_le hu hγpos hpbd.1 hy₁ hy₂ hpbd.2.2 hsep
    have hE2 : 0 ≤ 2 * E + 4 * B * ω / |u| := by positivity
    have hrest : 0 ≤ 2 * (2 * E + 4 * B * ω / |u|) * (|u| + 3 * B) / γ := by positivity
    constructor
    · refine hfit.trans ?_
      rw [gridErr]
      have : (2 * E + 4 * B * ω / |u|) *
          (|t p - ((j₁ : ℝ) * ω - b₂ p) / u| + |t p - ((j₂ : ℝ) * ω - b₂ p) / u|) /
          |((j₂ : ℝ) * ω - b₂ p) / u - ((j₁ : ℝ) * ω - b₂ p) / u| ≤
          (2 * E + 4 * B * ω / |u|) * (2 * (|u| + 3 * B) / γ) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hratio hE2
      have h2 : (2 * E + 4 * B * ω / |u|) * (2 * (|u| + 3 * B) / γ) =
          2 * (2 * E + 4 * B * ω / |u|) * (|u| + 3 * B) / γ := by ring
      linarith
    · rw [gridErr]
      have h1 := hpV.2
      have h2 := hq₁V.2
      have h3 := hq₁h.2
      calc |F p 1 - selR j₁ 2| ≤ |F p 1 - selC (col p) 2| + |F q₁ 1 - selC (col p) 2| +
            |F q₁ 1 - selR j₁ 2| := by
            have := abs_sub_le (F p 1) (selC (col p) 2) (selR j₁ 2)
            have := abs_sub_le (selC (col p) 2) (F q₁ 1) (selR j₁ 2)
            rw [abs_sub_comm (selC (col p) 2) (F q₁ 1)] at this
            linarith
        _ ≤ E + E + E := by linarith
        _ ≤ 3 * E + 2 * (2 * E + 4 * B * ω / |u|) * (|u| + 3 * B) / γ := by linarith

end Submission.Obl.k4_conditional_common_affine_field
