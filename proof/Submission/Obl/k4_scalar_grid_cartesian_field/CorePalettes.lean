-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CorePalettes.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreCells
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreRowLists

/-!
# Local palettes: cell values and fiber polynomial bins

The graph row bins of the states of one frame cell lie in the coarse lists of
boundedly many coarse cubes; the witness polynomials of the states of one
fiber have boundedly many coefficient bins.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open scoped Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set
open scoped ENNReal

/-- Physical coordinates `(t, y, X)` of an incidence. -/
noncomputable def physPt (p : Incidence) : Fin 3 → ℝ :=
  ![p.2, scalarY p.1 p.2, scalarX p.1 p.2]

theorem physCube_eq_floor {N r ε : ℝ} (hε : ε = N ^ (-r)) (p : Incidence) :
    physCube N r p = fun j => ⌊physPt p j / ε⌋ := by
  subst hε; rfl

theorem abs_sub_le_of_floor_eq {x x' δ : ℝ} (hδ : 0 < δ) (h : ⌊x / δ⌋ = ⌊x' / δ⌋) :
    |x - x'| ≤ δ := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at h1
  exact h1.le

theorem physCube_close {N B : ℝ} (hδ : 0 < N ^ (-B)) {p p' : Incidence}
    (h : physCube N B p = physCube N B p') :
    |p.2 - p'.2| ≤ N ^ (-B) ∧ |scalarY p.1 p.2 - scalarY p'.1 p'.2| ≤ N ^ (-B) := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [physCube, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact ⟨abs_sub_le_of_floor_eq hδ h0, abs_sub_le_of_floor_eq hδ h1⟩

theorem coreBase_close {N B h a y₀ : ℝ} (hδ : 0 < N ^ (-B)) (hh : 0 < h) {p p' : Incidence}
    (hq : physCube N B p = physCube N B p') :
    |coreBase h a y₀ p 0 - coreBase h a y₀ p' 0| ≤ N ^ (-B) / h ∧
      |coreBase h a y₀ p 1 - coreBase h a y₀ p' 1| ≤ N ^ (-B) / h := by
  obtain ⟨h0, h1⟩ := physCube_close hδ hq
  rw [coreBase_zero, coreBase_zero, coreBase_one, coreBase_one]
  constructor
  · rw [show (p.2 - a) / h - (p'.2 - a) / h = (p.2 - p'.2) / h by ring, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right h0 hh.le
  · rw [show (scalarY p.1 p.2 - y₀) / h - (scalarY p'.1 p'.2 - y₀) / h =
      (scalarY p.1 p.2 - scalarY p'.1 p'.2) / h by ring, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right h1 hh.le

theorem coreBase_line {h a y₀ : ℝ} (hh : 0 < h) (l : Trajectory) (τ : ℝ) :
    coreBase h a y₀ (l, a + h * τ) = ![τ, (l.2 0 + a * l.2 1 - y₀) / h + l.2 1 * τ] := by
  funext e
  fin_cases e
  · show coreBase h a y₀ (l, a + h * τ) 0 = τ
    rw [coreBase_zero]; field_simp; ring
  · show coreBase h a y₀ (l, a + h * τ) 1 = (l.2 0 + a * l.2 1 - y₀) / h + l.2 1 * τ
    rw [coreBase_one]; simp only [scalarY]; field_simp; ring

theorem frameOf_swap (v₁ v₂ : ℝ) (u : Fin 2 → ℝ) : frameOf v₂ v₁ u 1 = frameOf v₁ v₂ u 0 := by
  rw [frameOf_one_eq, frameOf_zero_eq]
  by_cases h : v₂ = v₁
  · subst h; simp
  · have h1 : v₁ - v₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have h2 : v₂ - v₁ ≠ 0 := sub_ne_zero.mpr h
    field_simp
    ring

/-- The cell palettes. -/
theorem exists_cell_palettes (A₁ : Set Incidence) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (N B rT εT Λ h a y₀ v₁ v₂ Bf ξ : ℝ) (A : Set Trajectory) (hN : 0 < N)
    (hεT : εT = N ^ (-rT)) (hεpos : 0 < εT) (hΛ : 1 ≤ Λ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hξ : 0 < ξ) (hsep : v₂ ≠ v₁) (hv₁ : |v₁| ≤ Λ + 1) (hv₂ : |v₂| ≤ Λ + 1)
    (hlayer : Λ ^ 2 * N ^ (-(1 : ℝ)) ≤ εT) (hcellsmall : Λ ^ 4 * ξ ≤ εT)
    (hA₁ : ∀ p ∈ A₁, p.1 ∈ A ∧ p.2 ∈ Icc a (a + h))
    (hlip : ∀ l ∈ A, ∀ l' ∈ A, ∀ t ∈ Icc a (a + h), ∀ t' ∈ Icc a (a + h),
      |scalarX l t - scalarX l' t'| ≤
        Λ * N ^ (-(1 : ℝ)) + Λ / h * (|t - t'| + |scalarY l t - scalarY l' t'|))
    (hbox : ∀ p ∈ A₁, ∀ i, |frameOf v₁ v₂ (coreBase h a y₀ p) i| ≤ Bf)
    (L : (Fin 3 → ℤ) → Finset (Fin 2 → ℤ)) (hL : ∀ q, ((L q).card : ℝ) ≤ Λ)
    (hknown : ∀ p ∈ A₁, rowBin N rT (G (physCube N B p)) ∈ L (physCube N rT p)) :
    ∃ L₀ : Fin (gridSize Bf ξ) × Fin (gridSize Bf ξ) → Finset (Fin 2 → ℤ),
      (∀ c, ((L₀ c).card : ℝ) ≤ (4 * 141 + 11) ^ 3 * Λ) ∧
      ∀ p ∈ A₁, rowBin N rT (G (physCube N B p)) ∈ L₀ (coreCell h a y₀ v₁ v₂ Bf ξ p) := by
  classical
  set center : Fin (gridSize Bf ξ) × Fin (gridSize Bf ξ) → Fin 3 → ℝ := fun c =>
    if hc : ∃ p ∈ A₁, coreCell h a y₀ v₁ v₂ Bf ξ p = c then physPt hc.choose else 0
  have hΛ0 : 0 < Λ := by linarith
  have hnear : ∀ p ∈ A₁, ∀ j,
      |physPt p j - center (coreCell h a y₀ v₁ v₂ Bf ξ p) j| ≤ 141 * εT := by
    intro p hp j
    have hc : ∃ p' ∈ A₁, coreCell h a y₀ v₁ v₂ Bf ξ p' = coreCell h a y₀ v₁ v₂ Bf ξ p :=
      ⟨p, hp, rfl⟩
    have hcen : center (coreCell h a y₀ v₁ v₂ Bf ξ p) = physPt hc.choose := by
      simp only [center, dif_pos hc]
    rw [hcen]
    obtain ⟨hp'A, hp'c⟩ := hc.choose_spec
    set p' := hc.choose
    -- both frame points lie in the same cell
    have hs := coreCell_spec hξ p (hbox p hp)
    have hs' := coreCell_spec hξ p' (hbox p' hp'A)
    rw [hp'c] at hs'
    have hd0 : |frameOf v₁ v₂ (coreBase h a y₀ p) 0 - frameOf v₁ v₂ (coreBase h a y₀ p') 0| ≤ ξ := by
      rw [abs_le]; constructor <;> linarith [hs.1.1, hs.1.2, hs'.1.1, hs'.1.2]
    have hd1 : |frameOf v₁ v₂ (coreBase h a y₀ p) 1 - frameOf v₁ v₂ (coreBase h a y₀ p') 1| ≤ ξ := by
      rw [abs_le]; constructor <;> linarith [hs.2.1, hs.2.2, hs'.2.1, hs'.2.2]
    obtain ⟨hu0, hu1⟩ := base_close_of_frame_close hsep hv₁ hv₂ _ _ hd0 hd1
    rw [coreBase_zero, coreBase_zero] at hu0
    rw [coreBase_one, coreBase_one] at hu1
    have ht : |p.2 - p'.2| ≤ 2 * ξ * h := by
      have e : (p.2 - a) / h - (p'.2 - a) / h = (p.2 - p'.2) / h := by ring
      rw [e, abs_div, abs_of_pos hh, div_le_iff₀ hh] at hu0
      linarith
    have hy : |scalarY p.1 p.2 - scalarY p'.1 p'.2| ≤ 2 * (Λ + 1) * ξ * h := by
      have e : (scalarY p.1 p.2 - y₀) / h - (scalarY p'.1 p'.2 - y₀) / h =
          (scalarY p.1 p.2 - scalarY p'.1 p'.2) / h := by ring
      rw [e, abs_div, abs_of_pos hh, div_le_iff₀ hh] at hu1
      linarith
    have hξΛ : Λ ^ 2 * ξ ≤ εT := by
      have : Λ ^ 2 * ξ ≤ Λ ^ 4 * ξ := by
        apply mul_le_mul_of_nonneg_right _ hξ.le
        exact pow_le_pow_right₀ hΛ (by norm_num)
      linarith
    have hΛξ : Λ * ξ ≤ εT := by
      have : Λ * ξ ≤ Λ ^ 2 * ξ := by
        apply mul_le_mul_of_nonneg_right _ hξ.le
        nlinarith
      linarith
    have hξε : ξ ≤ εT := by nlinarith
    have hN1 : Λ * N ^ (-(1 : ℝ)) ≤ εT := by
      have h0 : 0 ≤ N ^ (-(1 : ℝ)) := Real.rpow_nonneg hN.le _
      have : Λ * N ^ (-(1 : ℝ)) ≤ Λ ^ 2 * N ^ (-(1 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ h0
        nlinarith
      linarith
    have hξh : ξ * h ≤ ξ := mul_le_of_le_one_right hξ.le hh1
    have hΛ1ξh : (Λ + 1) * ξ * h ≤ (Λ + 1) * ξ := mul_le_of_le_one_right (by positivity) hh1
    fin_cases j
    · simp only [physPt, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith
    · simp only [physPt, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons]
      linarith
    · simp only [physPt, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      have hX := hlip p.1 (hA₁ p hp).1 p'.1 (hA₁ p' hp'A).1 p.2 (hA₁ p hp).2 p'.2 (hA₁ p' hp'A).2
      have hX2 : Λ / h * (|p.2 - p'.2| + |scalarY p.1 p.2 - scalarY p'.1 p'.2|) ≤
          Λ * (2 * ξ + 2 * (Λ + 1) * ξ) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hh]
        have : |p.2 - p'.2| + |scalarY p.1 p.2 - scalarY p'.1 p'.2| ≤
            (2 * ξ + 2 * (Λ + 1) * ξ) * h := by nlinarith
        nlinarith
      nlinarith
  obtain ⟨F, hFcard, hFmem⟩ := Cart.exists_neighborhood_field_palettes 3 A₁
    (coreCell h a y₀ v₁ v₂ Bf ξ) physPt center (fun p => rowBin N rT (G (physCube N B p)))
    εT 141 Λ hεpos (by norm_num) hΛ0.le L hL
    (fun p hp => by rw [← physCube_eq_floor hεT]; exact hknown p hp) hnear
  exact ⟨F, hFcard, hFmem⟩


/-- A witness line drifts slowly in the transverse frame coordinate. -/
theorem witness_transverse_drift {N B h a y₀ v v' δv Λ : ℝ} (hδ : 0 < N ^ (-B)) (hh : 0 < h)
    (hΛ : 0 < Λ) (hsep : 1 / Λ ≤ |v' - v|) (hv : |v| ≤ Λ + 1)
    (p w : Incidence) (hpw : physCube N B w = physCube N B p)
    (hV : 0 ≤ w.1.2 1 - v ∧ w.1.2 1 - v < δv) (hw : w.2 ∈ Icc a (a + h))
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    |frameOf v v' (coreBase h a y₀ (w.1, a + h * τ)) 1 - frameOf v v' (coreBase h a y₀ p) 1| ≤
      Λ * (Λ + 2) * (N ^ (-B) / h) + Λ * δv := by
  have hsep' : v' ≠ v := by
    intro he; rw [he, sub_self, abs_zero] at hsep; exact absurd hsep (not_le.mpr (by positivity))
  set τw := (w.2 - a) / h with hτw
  have h2 : a + h * τw = w.2 := by rw [hτw]; field_simp; ring
  have hw' : w = (w.1, a + h * τw) := by rw [h2]
  -- moving along the witness line
  have hline := frameOf_one_line hsep' ((w.1.2 0 + a * w.1.2 1 - y₀) / h) (w.1.2 1) τw τ
  rw [← coreBase_line hh, ← coreBase_line hh, ← hw'] at hline
  have hτw01 : τw ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hw.1]) hh.le
    · rw [hτw, div_le_one hh]; linarith [hw.2]
  have hpos : 0 < |v' - v| := lt_of_lt_of_le (by positivity) hsep
  have hinv : 1 / |v' - v| ≤ Λ := by
    rw [div_le_iff₀ hpos]
    have := (div_le_iff₀ hΛ).mp (by simpa using hsep : 1 / Λ ≤ |v' - v|)
    linarith [mul_comm Λ |v' - v|]
  have hmove : |frameOf v v' (coreBase h a y₀ (w.1, a + h * τ)) 1 -
      frameOf v v' (coreBase h a y₀ w) 1| ≤ Λ * δv := by
    rw [hline, abs_div, abs_mul]
    have h1 : |w.1.2 1 - v| ≤ δv := by rw [abs_of_nonneg hV.1]; exact hV.2.le
    have h2 : |τ - τw| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2, hτw01.1, hτw01.2]
    have hδv : 0 ≤ δv := le_trans (abs_nonneg _) h1
    calc |w.1.2 1 - v| * |τ - τw| / |v' - v| = |w.1.2 1 - v| * |τ - τw| * (1 / |v' - v|) := by
          ring
      _ ≤ δv * 1 * Λ := by
          apply mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hδv) hinv (by positivity)
            (by positivity)
      _ = Λ * δv := by ring
  -- the witness and the state point share a fine cube
  have hclose := coreBase_close (a := a) (y₀ := y₀) hδ hh hpw
  have hcube := frame_one_close (v₁ := v) (v₂ := v') hsep hΛ hv _ _ hclose.1 hclose.2
  calc _ ≤ |frameOf v v' (coreBase h a y₀ (w.1, a + h * τ)) 1 -
        frameOf v v' (coreBase h a y₀ w) 1| +
        |frameOf v v' (coreBase h a y₀ w) 1 - frameOf v v' (coreBase h a y₀ p) 1| := by
        apply abs_sub_le
    _ ≤ Λ * δv + Λ * (Λ + 2) * (N ^ (-B) / h) := add_le_add hmove hcube
    _ = _ := by ring


/-- Two packet lines at the same time with transverse frame coordinates within
`ξ + 2 d` (`d ≤ 4 ξ`) are within `141 εT` in physical coordinates. -/
theorem same_time_close {N εT Λ h a y₀ v v' ξ d : ℝ} (hN : 0 < N) (hΛ : 1 ≤ Λ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hξ : 0 < ξ) (hd0 : 0 ≤ d) (hd4 : d ≤ 4 * ξ) (hsep' : v' ≠ v)
    (hv : |v| ≤ Λ + 1) (hv' : |v'| ≤ Λ + 1)
    (hlayer : Λ ^ 2 * N ^ (-(1 : ℝ)) ≤ εT) (hcellsmall : Λ ^ 4 * ξ ≤ εT)
    (l l' : Trajectory) (t : ℝ)
    (hX : |scalarX l t - scalarX l' t| ≤
      Λ * N ^ (-(1 : ℝ)) + Λ / h * |scalarY l t - scalarY l' t|)
    (hdtr : |frameOf v v' (coreBase h a y₀ (l, t)) 1 -
      frameOf v v' (coreBase h a y₀ (l', t)) 1| ≤ ξ + 2 * d) :
    ∀ j, |physPt (l, t) j - physPt (l', t) j| ≤ 141 * εT := by
  have hΛ0 : 0 < Λ := by linarith
  have hsame : coreBase h a y₀ (l, t) 0 = coreBase h a y₀ (l', t) 0 := by
    rw [coreBase_zero, coreBase_zero]
  have hu1 := base_close_of_same_time hsep' hv hv' _ _ hsame hdtr
  rw [coreBase_one, coreBase_one] at hu1
  have e : (scalarY l t - y₀) / h - (scalarY l' t - y₀) / h = (scalarY l t - scalarY l' t) / h := by
    ring
  rw [e, abs_div, abs_of_pos hh, div_le_iff₀ hh] at hu1
  -- scale facts
  have hΛ14 : Λ ≤ Λ ^ 4 := by
    calc Λ = Λ ^ 1 := (pow_one Λ).symm
      _ ≤ Λ ^ 4 := pow_le_pow_right₀ hΛ (by norm_num)
  have hΛ24 : Λ ^ 2 ≤ Λ ^ 4 := pow_le_pow_right₀ hΛ (by norm_num)
  have hΛξ : Λ * ξ ≤ εT := (mul_le_mul_of_nonneg_right hΛ14 hξ.le).trans hcellsmall
  have hΛ2ξ : Λ ^ 2 * ξ ≤ εT := (mul_le_mul_of_nonneg_right hΛ24 hξ.le).trans hcellsmall
  have hN0 : 0 ≤ N ^ (-(1 : ℝ)) := Real.rpow_nonneg hN.le _
  have hΛΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
  have hN1 : Λ * N ^ (-(1 : ℝ)) ≤ εT := (mul_le_mul_of_nonneg_right hΛΛ2 hN0).trans hlayer
  have h9 : ξ + 2 * d ≤ 9 * ξ := by linarith
  have h2Λ : 2 * (Λ + 1) ≤ 4 * Λ := by linarith
  have hK1 : 2 * (Λ + 1) * (ξ + 2 * d) ≤ 36 * (Λ * ξ) := by
    calc 2 * (Λ + 1) * (ξ + 2 * d) ≤ (4 * Λ) * (9 * ξ) :=
          mul_le_mul h2Λ h9 (by positivity) (by positivity)
      _ = 36 * (Λ * ξ) := by ring
  have hy : |scalarY l t - scalarY l' t| ≤ 36 * εT := by
    calc |scalarY l t - scalarY l' t| ≤ (ξ + 2 * d) * (2 * (Λ + 1)) * h := by linarith
      _ ≤ (ξ + 2 * d) * (2 * (Λ + 1)) := mul_le_of_le_one_right (by positivity) hh1
      _ = 2 * (Λ + 1) * (ξ + 2 * d) := by ring
      _ ≤ 36 * (Λ * ξ) := hK1
      _ ≤ 36 * εT := by linarith
  have hyh : Λ / h * |scalarY l t - scalarY l' t| ≤ 36 * εT := by
    have h1 : |scalarY l t - scalarY l' t| ≤ (2 * (Λ + 1) * (ξ + 2 * d)) * h := by linarith
    calc Λ / h * |scalarY l t - scalarY l' t| ≤ Λ / h * ((2 * (Λ + 1) * (ξ + 2 * d)) * h) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Λ * (2 * (Λ + 1) * (ξ + 2 * d)) := by field_simp
      _ ≤ Λ * (36 * (Λ * ξ)) := mul_le_mul_of_nonneg_left hK1 hΛ0.le
      _ = 36 * (Λ ^ 2 * ξ) := by ring
      _ ≤ 36 * εT := by linarith
  have hε0 : 0 ≤ εT := le_trans (by positivity) hcellsmall
  intro j
  fin_cases j
  · show |t - t| ≤ 141 * εT
    rw [sub_self, abs_zero]; positivity
  · show |scalarY l t - scalarY l' t| ≤ 141 * εT
    linarith
  · show |scalarX l t - scalarX l' t| ≤ 141 * εT
    linarith

set_option maxHeartbeats 1000000 in
/-- The fiber lists in one direction. Fibers are the levels of the transverse
frame coordinate `frameOf v v' _ 1`; `v = b δv` is the left end of the narrow
velocity bin of the witnesses. -/
theorem exists_fiber_lists (M : ℕ) : ∃ Cb : ℝ, 0 < Cb ∧ ∀
    (ρ : Measure Incidence) (E A₁ : Set Incidence) (hE : MeasurableSet E)
    (G : (Fin 3 → ℤ) → Fin 2 → ℝ) (N B rT εT Λ h a y₀ v v' δv Bf ξ Hp : ℝ) (A : Set Trajectory)
    (b : ℤ) (wit : (Fin 3 → ℤ) → Incidence) (Pw : (Fin 3 → ℤ) → Fin 2 → Polynomial ℝ),
    0 < N → εT = N ^ (-rT) → 0 < εT → 1 ≤ Λ → 0 < h → h ≤ 1 → 0 < ξ → 0 < δv → 0 ≤ Hp →
    1 / Λ ≤ |v' - v| → |v| ≤ Λ + 1 → |v'| ≤ Λ + 1 → v = b * δv →
    Λ ^ 2 * N ^ (-(1 : ℝ)) ≤ εT → Λ ^ 4 * ξ ≤ εT → Λ ^ 2 * δv ≤ ξ →
    Λ ^ 4 * N ^ (-B) ≤ ξ * h → h ^ M ≤ εT →
    (∀ p ∈ A₁, p.1 ∈ A ∧ p.2 ∈ Icc a (a + h)) →
    (∀ l ∈ A, ∀ l' ∈ A, ∀ t ∈ Icc a (a + h), ∀ t' ∈ Icc a (a + h),
      |scalarX l t - scalarX l' t'| ≤
        Λ * N ^ (-(1 : ℝ)) + Λ / h * (|t - t'| + |scalarY l t - scalarY l' t'|)) →
    (∀ p ∈ A₁, |frameOf v v' (coreBase h a y₀ p) 1| ≤ Bf) →
    (∀ p ∈ A₁, (wit (physCube N B p)).1 ∈ A ∧ (wit (physCube N B p)).2 ∈ Icc a (a + h) ∧
      physCube N B (wit (physCube N B p)) = physCube N B p ∧
      velBin δv (wit (physCube N B p)) = b ∧
      (wit (physCube N B p)).1 ∉ badLines ρ E (coreCode N B rT)) →
    (∀ p ∈ A₁, (∀ e, (Pw (physCube N B p) e).natDegree ≤ M) ∧
      (∀ e k, |(normPoly a h (Pw (physCube N B p) e)).coeff k| ≤ Hp) ∧
      ENNReal.ofReal (h / Λ) ≤ volume {t | ((wit (physCube N B p)).1, t) ∈ E ∧
        t ∈ Icc a (a + h) ∧ ∀ e, |G (physCube N B ((wit (physCube N B p)).1, t)) e -
          (Pw (physCube N B p) e).eval t| ≤ h ^ M}) →
    ∀ (L : (Fin 3 → ℤ) → Finset (Fin 2 → ℤ)), (∀ q, ((L q).card : ℝ) ≤ Λ) →
    (∀ p' : Incidence, ρ.restrict E {p'' | coreCode N B rT p'' = coreCode N B rT p'} ≠ 0 →
      rowBin N rT (G (physCube N B p')) ∈ L (physCube N rT p')) →
    ∃ Lf : Fin (gridSize Bf ξ) → Finset (Fin 2 → Fin (M + 1) → ℤ),
      (∀ y, ((Lf y).card : ℝ) ≤
        (Cb * (max Λ ((4 * 141 + 11) ^ 3 * Λ + 2)) ^ (3 * (M + 1) + (M + 1) ^ 2 * M)) ^ 2) ∧
      ∀ p ∈ A₁, polyBins M εT (fun e => normPoly a h (Pw (physCube N B p) e)) ∈
        Lf (gridIdx Bf ξ (frameOf v v' (coreBase h a y₀ p) 1)) := by
  classical
  obtain ⟨Cb, hCb, hfib⟩ := fiber_bins_card_le M
  refine ⟨Cb, hCb, ?_⟩
  intro ρ E A₁ hE G N B rT εT Λ h a y₀ v v' δv Bf ξ Hp A b wit Pw hN hεT hεpos hΛ hh hh1 hξ hδv
    hHp hsep hv hv' hvb hlayer hcellsmall hδvξ hfine hfitprec hA₁ hlip hbox hwit hPw L hL hLmem
  have hΛ0 : 0 < Λ := by linarith
  have hδ : 0 < N ^ (-B) := Real.rpow_pos_of_pos hN _
  have hsep' : v' ≠ v := by
    intro he; rw [he, sub_self, abs_zero] at hsep; exact absurd hsep (not_le.mpr (by positivity))
  -- scale facts
  have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
  have hΛ4 : Λ ^ 2 ≤ Λ ^ 4 := pow_le_pow_right₀ hΛ (by norm_num)
  have hΛξ : Λ * ξ ≤ εT := by nlinarith
  have hΛ2ξ : Λ ^ 2 * ξ ≤ εT := by nlinarith
  have hξε : ξ ≤ εT := by nlinarith
  have hN0 : 0 ≤ N ^ (-(1 : ℝ)) := Real.rpow_nonneg hN.le _
  have hN1 : Λ * N ^ (-(1 : ℝ)) ≤ εT := by nlinarith
  have hfine' : N ^ (-B) / h ≤ ξ / Λ ^ 4 := by
    rw [div_le_div_iff₀ hh (by positivity)]; linarith
  have hd1 : Λ * (Λ + 2) * (N ^ (-B) / h) ≤ 3 * ξ := by
    have h3 : Λ * (Λ + 2) ≤ 3 * Λ ^ 4 := by nlinarith
    calc Λ * (Λ + 2) * (N ^ (-B) / h) ≤ 3 * Λ ^ 4 * (ξ / Λ ^ 4) :=
          mul_le_mul h3 hfine' (by positivity) (by positivity)
      _ = 3 * ξ := by field_simp
  have hd2 : Λ * δv ≤ ξ := by nlinarith
  set d := Λ * (Λ + 2) * (N ^ (-B) / h) + Λ * δv with hd
  have hd4 : d ≤ 4 * ξ := by linarith
  have hd0 : 0 ≤ d := by positivity
  set fib : Incidence → Fin (gridSize Bf ξ) := fun p => gridIdx Bf ξ (frameOf v v' (coreBase h a y₀ p) 1)
  have hstep : ∀ y : Fin (gridSize Bf ξ), ∃ S : Finset (Fin 2 → Fin (M + 1) → ℤ),
      (∀ p ∈ A₁, fib p = y →
        polyBins M εT (fun e => normPoly a h (Pw (physCube N B p) e)) ∈ S) ∧
      (S.card : ℝ) ≤
        (Cb * (max Λ ((4 * 141 + 11) ^ 3 * Λ + 2)) ^ (3 * (M + 1) + (M + 1) ^ 2 * M)) ^ 2 := by
    intro y
    set Q : Set (Fin 3 → ℤ) := {q | ∃ p ∈ A₁, physCube N B p = q ∧ fib p = y}
    set Tw : (Fin 3 → ℤ) → Set ℝ := fun q =>
      witnessRow ρ E N B rT a h (h ^ M) G (wit q).1 (Pw q)
    set phys : (Fin 3 → ℤ) → ℝ → Fin 3 → ℝ := fun q τ => physPt ((wit q).1, a + h * τ)
    set lab : (Fin 3 → ℤ) → ℝ → Fin 2 → ℤ := fun q τ =>
      rowBin N rT (G (physCube N B ((wit q).1, a + h * τ)))
    set center : ℝ → Fin 3 → ℝ := fun τ =>
      if hc : ∃ q ∈ Q, τ ∈ Tw q then phys hc.choose τ else 0
    -- transverse position of a fiber witness at any time
    have htr : ∀ q ∈ Q, ∀ τ ∈ Icc (0 : ℝ) 1,
        gridPos Bf ξ y - d ≤ frameOf v v' (coreBase h a y₀ ((wit q).1, a + h * τ)) 1 ∧
        frameOf v v' (coreBase h a y₀ ((wit q).1, a + h * τ)) 1 ≤ gridPos Bf ξ y + ξ + d := by
      rintro q ⟨p, hp, rfl, hpy⟩ τ hτ
      obtain ⟨_, hw2, hwq, hwb, _⟩ := hwit p hp
      have hV : 0 ≤ (wit (physCube N B p)).1.2 1 - v ∧ (wit (physCube N B p)).1.2 1 - v < δv := by
        have hb := hwb
        simp only [velBin] at hb
        have h1 : (b : ℝ) ≤ (wit (physCube N B p)).1.2 1 / δv := by
          rw [← hb]; exact Int.floor_le _
        have h2 : (wit (physCube N B p)).1.2 1 / δv < b + 1 := by
          rw [← hb]; exact Int.lt_floor_add_one _
        rw [le_div_iff₀ hδv] at h1
        rw [div_lt_iff₀ hδv] at h2
        constructor <;> nlinarith
      have hdrift := witness_transverse_drift (y₀ := y₀) hδ hh hΛ0 hsep hv p
        (wit (physCube N B p)) hwq hV hw2 τ hτ
      have hspec := gridIdx_spec hξ (hbox p hp)
      have hpy' : gridIdx Bf ξ (frameOf v v' (coreBase h a y₀ p) 1) = y := hpy
      rw [hpy'] at hspec
      have habs := abs_le.mp hdrift
      constructor <;> linarith [hspec.1, hspec.2]
    -- the state data of a fiber state
    have hQdata : ∀ q ∈ Q, (wit q).1 ∈ A ∧ (∀ e, (Pw q e).natDegree ≤ M) ∧
        (∀ e k, |(normPoly a h (Pw q e)).coeff k| ≤ Hp) ∧
        (wit q).1 ∉ badLines ρ E (coreCode N B rT) ∧
        ENNReal.ofReal (h / Λ) ≤ volume {t | ((wit q).1, t) ∈ E ∧ t ∈ Icc a (a + h) ∧
          ∀ e, |G (physCube N B ((wit q).1, t)) e - (Pw q e).eval t| ≤ h ^ M} := by
      rintro q ⟨p, hp, rfl, _⟩
      obtain ⟨hwA, _, _, _, hwbad⟩ := hwit p hp
      obtain ⟨hdeg, hcoef, hrow⟩ := hPw p hp
      exact ⟨hwA, hdeg, hcoef, hwbad, hrow⟩
    -- two fiber witnesses at the same time are close
    have hnear : ∀ q ∈ Q, ∀ τ ∈ Tw q, ∀ j, |phys q τ j - center τ j| ≤ 141 * εT := by
      intro q hq τ hτ j
      have hc : ∃ q' ∈ Q, τ ∈ Tw q' := ⟨q, hq, hτ⟩
      have hcen : center τ = phys hc.choose τ := by simp only [center, dif_pos hc]
      rw [hcen]
      obtain ⟨hq'Q, _⟩ := hc.choose_spec
      have hτ01 : τ ∈ Icc (0 : ℝ) 1 := hτ.1
      have ht1 := htr q hq τ hτ01
      have ht2 := htr hc.choose hq'Q τ hτ01
      have hdtr : |frameOf v v' (coreBase h a y₀ ((wit q).1, a + h * τ)) 1 -
          frameOf v v' (coreBase h a y₀ ((wit hc.choose).1, a + h * τ)) 1| ≤ ξ + 2 * d := by
        rw [abs_le]; constructor <;> linarith [ht1.1, ht1.2, ht2.1, ht2.2]
      have htI : a + h * τ ∈ Icc a (a + h) := by
        constructor
        · have : 0 ≤ h * τ := mul_nonneg hh.le hτ01.1
          linarith
        · have : h * τ ≤ h := mul_le_of_le_one_right hh.le hτ01.2
          linarith
      have hX := hlip (wit q).1 (hQdata q hq).1 (wit hc.choose).1 (hQdata _ hq'Q).1 _ htI _ htI
      rw [sub_self, abs_zero, zero_add] at hX
      exact same_time_close hN hΛ hh hh1 hξ hd0 hd4 hsep' hv hv' hlayer hcellsmall _ _ _ hX
        hdtr j
    obtain ⟨S, hSmem, hScard⟩ := hfib Q (fun q e => normPoly a h (Pw q e)) Tw phys lab center L
      εT 141 Λ Hp Λ hεpos (by norm_num) hΛ hHp hΛ hL
      (fun q hq e => ⟨natDegree_normPoly_le a h _ M ((hQdata q hq).2.1 e),
        fun k => (hQdata q hq).2.2.1 e k⟩)
      (fun q hq => ⟨measurableSet_witnessRow ρ E hE N B rT a h _ G _ _,
        fun τ hτ => hτ.1,
        volume_witnessRow_ge ρ E N B rT a h _ Λ hh hΛ0 G _ _ (hQdata q hq).2.2.2.1
          (hQdata q hq).2.2.2.2⟩)
      (fun q hq τ hτ => by
        have hpos : ρ.restrict E {p'' | coreCode N B rT p'' =
            coreCode N B rT ((wit q).1, a + h * τ)} ≠ 0 := hτ.2.2.2
        have := hLmem _ hpos
        rw [physCube_eq_floor hεT] at this
        exact this)
      (fun q hq τ hτ e => by
        have hfit := hτ.2.2.1 e
        simp only [rowBin, lab]
        rw [eval_normPoly, ← hεT]
        have hfl1 : εT * (⌊G (physCube N B ((wit q).1, a + h * τ)) e / εT⌋ : ℝ) ≤
            G (physCube N B ((wit q).1, a + h * τ)) e := by
          have := Int.floor_le (G (physCube N B ((wit q).1, a + h * τ)) e / εT)
          rw [le_div_iff₀ hεpos] at this; linarith
        have hfl2 : G (physCube N B ((wit q).1, a + h * τ)) e <
            εT * (⌊G (physCube N B ((wit q).1, a + h * τ)) e / εT⌋ : ℝ) + εT := by
          have := Int.lt_floor_add_one (G (physCube N B ((wit q).1, a + h * τ)) e / εT)
          rw [div_lt_iff₀ hεpos] at this; linarith
        rw [abs_le] at hfit ⊢
        constructor <;> linarith [hfit.1, hfit.2])
      hnear
    refine ⟨S, ?_, hScard⟩
    intro p hp hpy
    exact hSmem _ ⟨p, hp, rfl, hpy⟩
  choose Lf hLf using hstep
  exact ⟨Lf, fun y => (hLf y).2, fun p hp => (hLf _).1 p hp rfl⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
