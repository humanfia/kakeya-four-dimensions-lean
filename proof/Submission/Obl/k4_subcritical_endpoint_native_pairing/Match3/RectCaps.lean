/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/RectCaps.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation, session x0764, Match3/RectCaps.lean, commit2b232aca. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Wide.Grid

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Caps of rectangular slabs in parameter space

`rect_slab_cap` charges a set whose base points lie in a rectangular box and whose signal lies in
a window `[o, o + W]` moving with the base point to the fine joint caps (base cells of side `δ`,
signal bins of width `σ`); unlike `moving_slab_cap` the window may span several signal bins.

`param_cap_of_spatial_cap` turns the joint caps in the spatial coordinates `(t, Z, Y)` into joint
caps in the parameter coordinates `(t, p, q)` of a horizontal trajectory family, where
`Z = p + t v` up to the velocity bin `χ` and `Y = q - t p` up to the horizontal-equation error
`e`, at any mesh `δ ≥ χ, e`.
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open Set MeasureTheory

/-- Cells of side `δ` met by the box `|xᵢ - mᵢ| ≤ rᵢ`. -/
noncomputable def boxCells (δ : ℝ) (m r : Fin 3 → ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun i => intervalBins δ (m i) (r i)

theorem mem_boxCells {δ : ℝ} (hδ : 0 < δ) {m r x : Fin 3 → ℝ} (hx : ∀ i, |x i - m i| ≤ r i) :
    (fun i => ⌊x i / δ⌋) ∈ boxCells δ m r :=
  Fintype.mem_piFinset.mpr fun i => mem_intervalBins hδ (hx i)

theorem card_boxCells {δ : ℝ} (hδ : 0 < δ) {m r : Fin 3 → ℝ} (hr : ∀ i, δ ≤ r i) :
    ((boxCells δ m r).card : ℝ) ≤ 343 * (r 0 * r 1 * r 2) / δ ^ 3 := by
  rw [boxCells, Fintype.card_piFinset]
  push_cast
  rw [Fin.prod_univ_three]
  have hc : ∀ i, ((intervalBins δ (m i) (r i)).card : ℝ) ≤ 7 * r i / δ := by
    intro i
    have h1 := card_intervalBins hδ (hδ.le.trans (hr i)) (m i)
    have h2 : 1 ≤ r i / δ := (le_div_iff₀ hδ).mpr (by simpa using hr i)
    calc _ ≤ 2 * r i / δ + 5 := h1
      _ ≤ 7 * r i / δ := by rw [mul_div_assoc, mul_div_assoc]; linarith
  have hn : ∀ i, (0 : ℝ) ≤ ((intervalBins δ (m i) (r i)).card : ℝ) := fun i => Nat.cast_nonneg _
  calc _ ≤ (7 * r 0 / δ) * (7 * r 1 / δ) * (7 * r 2 / δ) := by
        apply mul_le_mul (mul_le_mul (hc 0) (hc 1) (hn 1) ((hn 0).trans (hc 0))) (hc 2) (hn 2)
        exact mul_nonneg ((hn 0).trans (hc 0)) ((hn 1).trans (hc 1))
    _ = 343 * (r 0 * r 1 * r 2) / δ ^ 3 := by field_simp; ring

/-- **Rectangular slab cap.** A set whose base points lie in the box `|xᵢ - mᵢ| ≤ rᵢ` and whose
signal lies in a window `[o, o + W]` moving with the base point is charged to the fine joint caps
(base cells of side `δ`, signal bins of width `σ`), provided the offset moves by at most `θ`
from a point of the set to any point within `δ` of it. -/
theorem rect_slab_cap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (x : Ω → Fin 3 → ℝ)
    (X : Ω → ℝ) (o : (Fin 3 → ℝ) → ℝ) (E : Set Ω) {δ σ W θ L : ℝ} (m r : Fin 3 → ℝ)
    (hδ : 0 < δ) (hσ : 0 < σ) (hθ : 0 ≤ θ) (hW : 0 ≤ W) (hr : ∀ i, δ ≤ r i) (hL : 0 ≤ L)
    (ho : ∀ z ∈ E, ∀ y' : Fin 3 → ℝ, (∀ i, |x z i - y' i| ≤ δ) → |o (x z) - o y'| ≤ θ)
    (hE : ∀ z ∈ E, (∀ i, |x z i - m i| ≤ r i) ∧ o (x z) ≤ X z ∧ X z ≤ o (x z) + W)
    (hcap : ∀ c j, μ {z | (fun i => ⌊x z i / δ⌋) = c ∧ ⌊X z / σ⌋ = j} ≤
      ENNReal.ofReal (L * δ ^ 3)) :
    μ E ≤ ENNReal.ofReal (343 * (r 0 * r 1 * r 2) * ((W + 2 * θ) / σ + 2) * L) := by
  have hr0 : 0 ≤ r 0 := hδ.le.trans (hr 0)
  have hr1 : 0 ≤ r 1 := hδ.le.trans (hr 1)
  have hr2 : 0 ≤ r 2 := hδ.le.trans (hr 2)
  have hrr : 0 ≤ r 0 * r 1 * r 2 := mul_nonneg (mul_nonneg hr0 hr1) hr2
  have hWθ : 0 ≤ (W + 2 * θ) / σ := div_nonneg (by linarith) hσ.le
  let corner : (Fin 3 → ℤ) → Fin 3 → ℝ := fun c i => (c i : ℝ) * δ
  let Q := boxCells δ m r
  let J : (Fin 3 → ℤ) → Finset ℤ := fun c =>
    windowBins ((o (corner c) - θ) / σ) ((W + 2 * θ) / σ)
  let nJ : ℕ := ⌊(W + 2 * θ) / σ + 2⌋₊
  have hJ : ∀ c ∈ Q, (J c).card ≤ nJ := by
    intro c _
    apply Nat.le_floor
    exact card_windowBins hWθ
  have hsub : ∀ z ∈ E, (fun i => ⌊x z i / δ⌋) ∈ Q ∧
      ⌊X z / σ⌋ ∈ J (fun i => ⌊x z i / δ⌋) := by
    intro z hz
    obtain ⟨hbox, hlo, hhi⟩ := hE z hz
    refine ⟨mem_boxCells hδ hbox, ?_⟩
    have hcell : ∀ i, |x z i - corner (fun i => ⌊x z i / δ⌋) i| ≤ δ := by
      intro i
      have h₀ := (le_div_iff₀ hδ).mp (Int.floor_le (x z i / δ))
      have h₁ := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x z i / δ))
      rw [abs_le]
      simp only [corner]
      constructor <;> nlinarith
    have hoc := ho z hz _ hcell
    rw [abs_le] at hoc
    apply mem_windowBins
    · rw [div_le_div_iff_of_pos_right hσ]; linarith
    · have : (o (corner fun i => ⌊x z i / δ⌋) - θ) / σ + (W + 2 * θ) / σ =
          (o (corner fun i => ⌊x z i / δ⌋) + θ + W) / σ := by field_simp; ring
      rw [this, div_le_div_iff_of_pos_right hσ]; linarith
  have hQ : (Q.card : ENNReal) ≤ ENNReal.ofReal (343 * (r 0 * r 1 * r 2) / δ ^ 3) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_boxCells hδ hr)
  have hnJ : (nJ : ENNReal) ≤ ENNReal.ofReal ((W + 2 * θ) / σ + 2) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (Nat.floor_le (by positivity))
  calc μ E ≤ (Q.card : ENNReal) * nJ * ENNReal.ofReal (L * δ ^ 3) :=
        moving_cell_cap μ (fun z i => ⌊x z i / δ⌋) (fun z => ⌊X z / σ⌋) Q J nJ hJ E hsub _ hcap
    _ ≤ ENNReal.ofReal (343 * (r 0 * r 1 * r 2) / δ ^ 3) *
          ENNReal.ofReal ((W + 2 * θ) / σ + 2) * ENNReal.ofReal (L * δ ^ 3) := by gcongr
    _ = ENNReal.ofReal (343 * (r 0 * r 1 * r 2) * ((W + 2 * θ) / σ + 2) * L) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- **Spatial to parameter caps.** Where `|t| ≤ 1`, `|p| ≤ Pm`, `|Z - (p + t v)| ≤ χ` and
`|Y - (q - t p)| ≤ e` with `χ, e ≤ δ ≤ 1`, a parameter cell of side `δ` meets at most
`(2|v| + 9)(2 Pm + 13)` spatial cells of side `δ`; the spatial joint caps give parameter caps. -/
theorem param_cap_of_spatial_cap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T P Q Z Y X : Ω → ℝ) {v χ e δ σ Pm : ℝ} (L : ENNReal) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hχ : χ ≤ δ) (he : e ≤ δ) (hPm : 0 ≤ Pm) (G : Set Ω)
    (hG : ∀ z ∈ G, |T z| ≤ 1 ∧ |P z| ≤ Pm ∧ |Z z - (P z + T z * v)| ≤ χ ∧
      |Y z - (Q z - T z * P z)| ≤ e)
    (hcap : ∀ (c : Fin 3 → ℤ) (j : ℤ),
      μ {z | (fun i => ⌊(![T z, Z z, Y z] : Fin 3 → ℝ) i / δ⌋) = c ∧ ⌊X z / σ⌋ = j} ≤ L)
    (c : Fin 3 → ℤ) (j : ℤ) :
    μ (G ∩ {z | (fun i => ⌊(![T z, P z, Q z] : Fin 3 → ℝ) i / δ⌋) = c ∧ ⌊X z / σ⌋ = j}) ≤
      ENNReal.ofReal ((2 * |v| + 9) * (2 * Pm + 13)) * L := by
  set t₀ : ℝ := (c 0 : ℝ) * δ
  set p₀ : ℝ := (c 1 : ℝ) * δ
  set q₀ : ℝ := (c 2 : ℝ) * δ
  let I1 := intervalBins δ (p₀ + t₀ * v) (δ * (2 + |v|))
  let I2 := intervalBins δ (q₀ - t₀ * p₀) (δ * (Pm + 4))
  let Qs : Finset (Fin 3 → ℤ) := Fintype.piFinset (![{c 0}, I1, I2] : Fin 3 → Finset ℤ)
  have hcell : ∀ (y : ℝ) (k : ℤ), ⌊y / δ⌋ = k → (k : ℝ) * δ ≤ y ∧ y < (k : ℝ) * δ + δ := by
    intro y k hk
    have h₀ := (le_div_iff₀ hδ).mp (Int.floor_le (y / δ))
    have h₁ := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (y / δ))
    rw [hk] at h₀ h₁
    constructor <;> nlinarith
  have hsub : ∀ z ∈ G ∩ {z | (fun i => ⌊(![T z, P z, Q z] : Fin 3 → ℝ) i / δ⌋) = c ∧
      ⌊X z / σ⌋ = j},
      (fun i => ⌊(![T z, Z z, Y z] : Fin 3 → ℝ) i / δ⌋) ∈ Qs ∧ ⌊X z / σ⌋ ∈ ({j} : Finset ℤ) := by
    intro z ⟨hzG, hcode, hj⟩
    obtain ⟨hT1, hPm, hZ, hY⟩ := hG z hzG
    have hc0 := congrFun hcode 0
    have hc1 := congrFun hcode 1
    have hc2 := congrFun hcode 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc0 hc1 hc2
    obtain ⟨ht0, ht1⟩ := hcell _ _ hc0
    obtain ⟨hp0, hp1⟩ := hcell _ _ hc1
    obtain ⟨hq0, hq1⟩ := hcell _ _ hc2
    refine ⟨?_, Finset.mem_singleton.mpr hj⟩
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Finset.mem_singleton]
      exact hc0
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      apply mem_intervalBins hδ
      have hTt : |T z - t₀| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
      have hPp : |P z - p₀| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
      have e1 : Z z - (p₀ + t₀ * v) = (Z z - (P z + T z * v)) + (P z - p₀) + (T z - t₀) * v := by
        ring
      rw [e1]
      calc _ ≤ |Z z - (P z + T z * v)| + |P z - p₀| + |(T z - t₀) * v| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ δ + δ + δ * |v| := by
            rw [abs_mul]
            gcongr
            exact hZ.trans hχ
        _ = δ * (2 + |v|) := by ring
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      apply mem_intervalBins hδ
      have hTt : |T z - t₀| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
      have hPp : |P z - p₀| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
      have hQq : |Q z - q₀| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
      have ht₀ : |t₀| ≤ 2 := by
        have := abs_le.mp hT1
        rw [abs_le]; constructor <;> linarith
      have e1 : Y z - (q₀ - t₀ * p₀) = (Y z - (Q z - T z * P z)) + (Q z - q₀) -
          (T z - t₀) * P z - t₀ * (P z - p₀) := by ring
      rw [e1]
      calc _ ≤ |Y z - (Q z - T z * P z)| + |Q z - q₀| + |(T z - t₀) * P z| +
            |t₀ * (P z - p₀)| := by
            refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
            exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ δ + δ + δ * Pm + 2 * δ := by
            rw [abs_mul, abs_mul]
            gcongr
            exact hY.trans he
        _ = δ * (Pm + 4) := by ring
  have hQs : ((Qs.card : ℝ)) ≤ (2 * |v| + 9) * (2 * Pm + 13) := by
    rw [Fintype.card_piFinset, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Finset.card_singleton,
      one_mul]
    push_cast
    have h1 : ((I1.card : ℕ) : ℝ) ≤ 2 * |v| + 9 := by
      have := card_intervalBins hδ (by positivity : (0 : ℝ) ≤ δ * (2 + |v|)) (p₀ + t₀ * v)
      calc _ ≤ 2 * (δ * (2 + |v|)) / δ + 5 := this
        _ = 2 * |v| + 9 := by field_simp; ring
    have h2 : ((I2.card : ℕ) : ℝ) ≤ 2 * Pm + 13 := by
      have := card_intervalBins hδ (mul_nonneg hδ.le (by linarith) : (0 : ℝ) ≤ δ * (Pm + 4))
        (q₀ - t₀ * p₀)
      calc _ ≤ 2 * (δ * (Pm + 4)) / δ + 5 := this
        _ = 2 * Pm + 13 := by field_simp; ring
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
  have hcap' : ∀ (c' : Fin 3 → ℤ) (j' : ℤ),
      μ {z | (fun i => ⌊(![T z, Z z, Y z] : Fin 3 → ℝ) i / δ⌋) = c' ∧ ⌊X z / σ⌋ = j'} ≤ L :=
    hcap
  calc _ ≤ (Qs.card : ENNReal) * (1 : ℕ) * L :=
        moving_cell_cap μ (fun z i => ⌊(![T z, Z z, Y z] : Fin 3 → ℝ) i / δ⌋)
          (fun z => ⌊X z / σ⌋) Qs (fun _ => {j}) 1 (fun _ _ => by simp) _ hsub L hcap'
    _ ≤ ENNReal.ofReal ((2 * |v| + 9) * (2 * Pm + 13)) * L := by
        rw [Nat.cast_one, mul_one]
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hQs

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
