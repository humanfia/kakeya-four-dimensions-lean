/-
Adapted from: here:o266
Original: session x0947, branch x0947 of o266, file
Submission/Obl/k4_narrow_original_potential_atlas/Full7EntryPruning.lean (commit 49bc611e).
Moved into a library namespace; imports only Mathlib and modules already in lib.
-/

import Submission.Lib.K4ReferencePruning

/-! FULL7 PRIOR FLOORS → PHYSICAL-ENTRY PRUNING → `X'` LISTS (paper, §6, the paragraph before
display `a05:derivative-list`).

Lines carry bounded base data `y0, V : X → ℝ²` and scalar coefficients `a = (qc, qb, qa)`, all
coordinates `≤ K`, and a velocity code `vcode`. At mesh `p ≤ 1`:
- the PHYSICAL code of an event `(l, t)` is `(⌊t/p⌋, ⌊(y0 + tV)/p⌋, ⌊(qc + t qb + t² qa)/p⌋)`;
- the FULL7 code of a line is `(⌊y0/p⌋, ⌊V/p⌋, ⌊a/p⌋)`;
- `X' = qb + 2t qa`.

Steps:
1. A full7 block uses only the cells of `cellsOf K p b` over unit time, at most
   `cellConst K / p` of them (`physCode_mem_cellsOf`, `card_cellsOf_mul_le`).
2. Entries (full7 code, velocity code, physical cell) are deleted when their current mass is
   below `δ p θ(block)` (lib `K4ReferencePruning.referenceKeep`), and so are incidences of null
   palette bins. The cost is at most `δ cellConst K θ(univ)` (`retained_cost`), with no alphabet
   factor.
3. Under the prior floor `θ(block) ≥ ζ p² Fp π(v)` and the joint cap
   `μ{cell = w, vcode = v} ≤ Kcap p³ Fp π(v)`, each (cell, velocity bin) keeps at most
   `Kcap/(δζ)` full7 blocks (`card_survivors_le`).
4. Hence `⌊X'/p⌋` has at most `(4K + 12) Kcap/(δζ)` options given (cell, velocity bin), on every
   retained incidence (`card_xList_le`, `floor_derivX_mem_xList`). The amplitude `Fp` cancels. -/

namespace Submission.Lib.K4ThreeBaseRows

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Full7EntryPruning

open Submission.Lib.K4ReferencePruning (referenceKeep measurableSet_referenceKeep
  reference_light_mass_le)

/-! ### Integer bins of an interval -/

/-- The integer bins at mesh `p` of the interval `[c - r, c + r]`. -/
def binsAround (p c r : ℝ) : Finset ℤ := Finset.Icc ⌊(c - r) / p⌋ ⌊(c + r) / p⌋

theorem floor_mem_binsAround {p c r x : ℝ} (hp : 0 < p) (hx : |x - c| ≤ r) :
    ⌊x / p⌋ ∈ binsAround p c r := by
  have h := abs_le.mp hx
  simp only [binsAround, Finset.mem_Icc]
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hp.le),
    Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hp.le)⟩

theorem card_binsAround_le {p c r : ℝ} (hp : 0 < p) (hr : 0 ≤ r) :
    ((binsAround p c r).card : ℝ) ≤ 2 * r / p + 2 := by
  simp only [binsAround, Int.card_Icc]
  have h1 : (⌊(c + r) / p⌋ : ℝ) ≤ (c + r) / p := Int.floor_le _
  have h2 : (c - r) / p - 1 < (⌊(c - r) / p⌋ : ℝ) := by
    have := Int.lt_floor_add_one ((c - r) / p)
    linarith
  have h3 : 0 ≤ 2 * r / p + 2 := by positivity
  have hcast : (((⌊(c + r) / p⌋ + 1 - ⌊(c - r) / p⌋).toNat : ℕ) : ℝ) =
      (((max (⌊(c + r) / p⌋ + 1 - ⌊(c - r) / p⌋) 0 : ℤ)) : ℝ) := by
    rw [← Int.toNat_eq_max]
    push_cast
    rfl
  rw [hcast]
  push_cast
  refine max_le ?_ h3
  have h4 : (c + r) / p - (c - r) / p = 2 * r / p := by ring
  linarith

/-- Floor bounds: `p ⌊x/p⌋ ≤ x < p ⌊x/p⌋ + p`. -/
theorem floor_bounds {x p : ℝ} (hp : 0 < p) :
    p * (⌊x / p⌋ : ℝ) ≤ x ∧ x < p * (⌊x / p⌋ : ℝ) + p := by
  constructor
  · have h := Int.floor_le (x / p)
    rw [le_div_iff₀ hp] at h
    linarith
  · have h := Int.lt_floor_add_one (x / p)
    rw [div_lt_iff₀ hp] at h
    linarith

/-! ### Codes -/

/-- Physical cell codes: time bin, two spatial bins, scalar bin. -/
abbrev PhysC := ℤ × (Fin 2 → ℤ) × ℤ

/-- Full7 coefficient codes: base bins, velocity bins, scalar coefficient bins. -/
abbrev Full7C := (Fin 2 → ℤ) × (Fin 2 → ℤ) × (Fin 3 → ℤ)

variable {X : Type*}

/-- The physical code of an event. -/
def physCode (y0 V : X → Fin 2 → ℝ) (a : X → Fin 3 → ℝ) (p : ℝ) (z : X × ℝ) : PhysC :=
  (⌊z.2 / p⌋, fun i => ⌊(y0 z.1 i + z.2 * V z.1 i) / p⌋,
    ⌊(a z.1 0 + z.2 * a z.1 1 + z.2 ^ 2 * a z.1 2) / p⌋)

/-- The full7 code of a line. -/
def full7 (y0 V : X → Fin 2 → ℝ) (a : X → Fin 3 → ℝ) (p : ℝ) (l : X) : Full7C :=
  (fun i => ⌊y0 l i / p⌋, fun i => ⌊V l i / p⌋, fun j => ⌊a l j / p⌋)

/-- `X' = qb + 2 t qa`, the time derivative of the scalar quadratic. -/
def derivX (a : X → Fin 3 → ℝ) (z : X × ℝ) : ℝ := a z.1 1 + 2 * z.2 * a z.1 2

/-- The physical cells a full7 block can use over unit time. -/
def cellsOf (K p : ℝ) (b : Full7C) : Finset PhysC :=
  (Finset.Icc (0 : ℤ) ⌊1 / p⌋).biUnion fun k =>
    {k} ×ˢ (Fintype.piFinset (fun i => binsAround p (p * b.1 i + k * p * (p * b.2.1 i)) (p * (K + 3)))
      ×ˢ binsAround p (p * b.2.2 0 + k * p * (p * b.2.2 1) + (k * p) ^ 2 * (p * b.2.2 2))
        (p * (3 * K + 6)))

/-- The `X'` bins of a full7 block in the time bin `k`. -/
def xBins (K p : ℝ) (b : Full7C) (k : ℤ) : Finset ℤ :=
  binsAround p (p * b.2.2 1 + 2 * (k * p) * (p * b.2.2 2)) (p * (2 * K + 5))

/-- The full7 codes of lines with all coordinates `≤ K`. -/
def full7Box (K p : ℝ) : Finset Full7C :=
  Fintype.piFinset (fun _ : Fin 2 => Finset.Icc ⌊-K / p⌋ ⌊K / p⌋) ×ˢ
    (Fintype.piFinset (fun _ : Fin 2 => Finset.Icc ⌊-K / p⌋ ⌊K / p⌋) ×ˢ
      Fintype.piFinset (fun _ : Fin 3 => Finset.Icc ⌊-K / p⌋ ⌊K / p⌋))

/-- The constant of the cell count: `p · #cellsOf ≤ cellConst K`. -/
def cellConst (K : ℝ) : ℝ := 2 * (2 * K + 8) ^ 2 * (6 * K + 14)

section Geometry

variable {y0 V : X → Fin 2 → ℝ} {a : X → Fin 3 → ℝ} {K p : ℝ}

theorem floor_mem_Icc_box {K p x : ℝ} (hp : 0 < p) (hx : |x| ≤ K) :
    ⌊x / p⌋ ∈ Finset.Icc ⌊-K / p⌋ ⌊K / p⌋ := by
  have h := abs_le.mp hx
  simp only [Finset.mem_Icc]
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right h.1 hp.le),
    Int.floor_mono (div_le_div_of_nonneg_right h.2 hp.le)⟩

theorem full7_mem_full7Box (hp : 0 < p)
    (hbound : ∀ l, (∀ i, |y0 l i| ≤ K) ∧ (∀ i, |V l i| ≤ K) ∧ (∀ j, |a l j| ≤ K)) (l : X) :
    full7 y0 V a p l ∈ full7Box K p := by
  simp only [full7, full7Box, Finset.mem_product, Fintype.mem_piFinset]
  exact ⟨fun i => floor_mem_Icc_box hp ((hbound l).1 i),
    fun i => floor_mem_Icc_box hp ((hbound l).2.1 i),
    fun j => floor_mem_Icc_box hp ((hbound l).2.2 j)⟩

/-- A bin corner `p ⌊x/p⌋` of a coordinate `|x| ≤ K` has size `≤ K + 1` (for `p ≤ 1`). -/
theorem abs_corner_le {x p K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hx : |x| ≤ K) :
    |p * (⌊x / p⌋ : ℝ)| ≤ K + 1 := by
  obtain ⟨h1, h2⟩ := floor_bounds (x := x) hp
  have h := abs_le.mp hx
  rw [abs_le]
  constructor <;> linarith

/-- The common time-bin estimates: with `T = p ⌊t/p⌋`, `0 ≤ t ≤ 1`: `T ≤ t < T + p`, `|T| ≤ 1`. -/
theorem time_bounds {t p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    p * (⌊t / p⌋ : ℝ) ≤ t ∧ t < p * (⌊t / p⌋ : ℝ) + p ∧ |p * (⌊t / p⌋ : ℝ)| ≤ 1 := by
  obtain ⟨h1, h2⟩ := floor_bounds (x := t) hp
  refine ⟨h1, h2, abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

theorem spatial_estimate {y v t p K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hv : |v| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |y + t * v - (p * (⌊y / p⌋ : ℝ) + (⌊t / p⌋ : ℝ) * p * (p * (⌊v / p⌋ : ℝ)))| ≤ p * (K + 3) := by
  obtain ⟨hy1, hy2⟩ := floor_bounds (x := y) hp
  obtain ⟨hv1, hv2⟩ := floor_bounds (x := v) hp
  obtain ⟨hT1, hT2, -⟩ := time_bounds hp hp1 ht
  have hB1 := abs_corner_le hp hp1 hv
  set B0 := p * (⌊y / p⌋ : ℝ)
  set B1 := p * (⌊v / p⌋ : ℝ)
  set T := p * (⌊t / p⌋ : ℝ)
  have hk : (⌊t / p⌋ : ℝ) * p * B1 = T * B1 := by simp only [T]; ring
  rw [hk]
  have e : y + t * v - (B0 + T * B1) = (y - B0) + t * (v - B1) + (t - T) * B1 := by ring
  rw [e]
  have h1 : 0 ≤ t * (v - B1) := mul_nonneg ht.1 (by linarith)
  have h2 : t * (v - B1) ≤ p := by
    calc t * (v - B1) ≤ 1 * (v - B1) := mul_le_mul_of_nonneg_right ht.2 (by linarith)
      _ ≤ p := by linarith
  have h3 : |(t - T) * B1| ≤ p * (K + 1) := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩) hB1 (abs_nonneg _) hp.le
  have h3' := abs_le.mp h3
  rw [abs_le]
  constructor <;> nlinarith

theorem scalar_estimate {a0 a1 a2 t p K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha1 : |a1| ≤ K)
    (ha2 : |a2| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) :
    |a0 + t * a1 + t ^ 2 * a2 - (p * (⌊a0 / p⌋ : ℝ) + (⌊t / p⌋ : ℝ) * p * (p * (⌊a1 / p⌋ : ℝ)) +
      ((⌊t / p⌋ : ℝ) * p) ^ 2 * (p * (⌊a2 / p⌋ : ℝ)))| ≤ p * (3 * K + 6) := by
  obtain ⟨h01, h02⟩ := floor_bounds (x := a0) hp
  obtain ⟨h11, h12⟩ := floor_bounds (x := a1) hp
  obtain ⟨h21, h22⟩ := floor_bounds (x := a2) hp
  obtain ⟨hT1, hT2, hTabs⟩ := time_bounds hp hp1 ht
  have hA1 := abs_corner_le hp hp1 ha1
  have hA2 := abs_corner_le hp hp1 ha2
  set A0 := p * (⌊a0 / p⌋ : ℝ)
  set A1 := p * (⌊a1 / p⌋ : ℝ)
  set A2 := p * (⌊a2 / p⌋ : ℝ)
  set T := p * (⌊t / p⌋ : ℝ)
  have hk1 : (⌊t / p⌋ : ℝ) * p * A1 = T * A1 := by simp only [T]; ring
  have hk2 : ((⌊t / p⌋ : ℝ) * p) ^ 2 * A2 = T ^ 2 * A2 := by simp only [T]; ring
  rw [hk1, hk2]
  have e : a0 + t * a1 + t ^ 2 * a2 - (A0 + T * A1 + T ^ 2 * A2) =
      (a0 - A0) + t * (a1 - A1) + t ^ 2 * (a2 - A2) + (t - T) * A1 + ((t - T) * (t + T)) * A2 := by
    ring
  rw [e]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have h1 : 0 ≤ t * (a1 - A1) := mul_nonneg ht.1 (by linarith)
  have h2 : t * (a1 - A1) ≤ p := by
    calc t * (a1 - A1) ≤ 1 * (a1 - A1) := mul_le_mul_of_nonneg_right ht.2 (by linarith)
      _ ≤ p := by linarith
  have h3 : 0 ≤ t ^ 2 * (a2 - A2) := mul_nonneg (sq_nonneg t) (by linarith)
  have h4 : t ^ 2 * (a2 - A2) ≤ p := by
    calc t ^ 2 * (a2 - A2) ≤ 1 * (a2 - A2) := mul_le_mul_of_nonneg_right ht2 (by linarith)
      _ ≤ p := by linarith
  have h5 : |(t - T) * A1| ≤ p * (K + 1) := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩) hA1 (abs_nonneg _) hp.le
  have hsum : |t + T| ≤ 2 := by
    have := abs_le.mp hTabs
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h6 : |((t - T) * (t + T)) * A2| ≤ p * 2 * (K + 1) := by
    rw [abs_mul, abs_mul]
    have hd : |t - T| ≤ p := abs_le.mpr ⟨by linarith, by linarith⟩
    apply mul_le_mul (mul_le_mul hd hsum (abs_nonneg _) hp.le) hA2 (abs_nonneg _)
    positivity
  have h5' := abs_le.mp h5
  have h6' := abs_le.mp h6
  rw [abs_le]
  constructor <;> nlinarith

theorem derivX_estimate {a1 a2 t p K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha2 : |a2| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |a1 + 2 * t * a2 - (p * (⌊a1 / p⌋ : ℝ) + 2 * ((⌊t / p⌋ : ℝ) * p) * (p * (⌊a2 / p⌋ : ℝ)))| ≤
      p * (2 * K + 5) := by
  obtain ⟨h11, h12⟩ := floor_bounds (x := a1) hp
  obtain ⟨h21, h22⟩ := floor_bounds (x := a2) hp
  obtain ⟨hT1, hT2, -⟩ := time_bounds hp hp1 ht
  have hA2 := abs_corner_le hp hp1 ha2
  set A1 := p * (⌊a1 / p⌋ : ℝ)
  set A2 := p * (⌊a2 / p⌋ : ℝ)
  set T := p * (⌊t / p⌋ : ℝ)
  have hk : 2 * ((⌊t / p⌋ : ℝ) * p) * A2 = 2 * T * A2 := by simp only [T]; ring
  rw [hk]
  have e : a1 + 2 * t * a2 - (A1 + 2 * T * A2) = (a1 - A1) + 2 * (t * (a2 - A2)) +
      2 * ((t - T) * A2) := by ring
  rw [e]
  have h1 : 0 ≤ t * (a2 - A2) := mul_nonneg ht.1 (by linarith)
  have h2 : t * (a2 - A2) ≤ p := by
    calc t * (a2 - A2) ≤ 1 * (a2 - A2) := mul_le_mul_of_nonneg_right ht.2 (by linarith)
      _ ≤ p := by linarith
  have h3 : |(t - T) * A2| ≤ p * (K + 1) := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩) hA2 (abs_nonneg _) hp.le
  have h3' := abs_le.mp h3
  rw [abs_le]
  constructor <;> nlinarith

/-- **Step 1.** An event of a line in full7 block `b`, at a time in `[0,1]`, has its physical
cell in `cellsOf K p b`. -/
theorem physCode_mem_cellsOf (hp : 0 < p) (hp1 : p ≤ 1)
    (hbound : ∀ l, (∀ i, |y0 l i| ≤ K) ∧ (∀ i, |V l i| ≤ K) ∧ (∀ j, |a l j| ≤ K))
    {z : X × ℝ} (ht : z.2 ∈ Icc (0 : ℝ) 1) :
    physCode y0 V a p z ∈ cellsOf K p (full7 y0 V a p z.1) := by
  simp only [cellsOf, Finset.mem_biUnion, Finset.mem_product, Finset.mem_singleton,
    Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨⌊z.2 / p⌋, ⟨Int.floor_nonneg.mpr (div_nonneg ht.1 hp.le),
    Int.floor_mono (div_le_div_of_nonneg_right ht.2 hp.le)⟩, ?_⟩
  refine ⟨rfl, fun i => ?_, ?_⟩
  · exact floor_mem_binsAround hp (spatial_estimate hp hp1 ((hbound z.1).2.1 i) ht)
  · exact floor_mem_binsAround hp
      (scalar_estimate hp hp1 ((hbound z.1).2.2 1) ((hbound z.1).2.2 2) ht)

theorem card_cellsOf_mul_le (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 ≤ K) (b : Full7C) :
    p * ((cellsOf K p b).card : ℝ) ≤ cellConst K := by
  have hterm : ∀ k : ℤ, (({k} ×ˢ (Fintype.piFinset (fun i => binsAround p
      (p * b.1 i + k * p * (p * b.2.1 i)) (p * (K + 3))) ×ˢ binsAround p
      (p * b.2.2 0 + k * p * (p * b.2.2 1) + (k * p) ^ 2 * (p * b.2.2 2))
        (p * (3 * K + 6)))).card : ℝ) ≤ (2 * K + 8) ^ 2 * (6 * K + 14) := by
    intro k
    rw [Finset.card_product, Finset.card_singleton, Finset.card_product,
      Fintype.card_piFinset]
    push_cast
    have hb1 : ∀ c : ℝ, ((binsAround p c (p * (K + 3))).card : ℝ) ≤ 2 * K + 8 := by
      intro c
      have h := card_binsAround_le (c := c) hp (by positivity : 0 ≤ p * (K + 3))
      have : 2 * (p * (K + 3)) / p + 2 = 2 * K + 8 := by field_simp; ring
      linarith
    have hb2 : ∀ c : ℝ, ((binsAround p c (p * (3 * K + 6))).card : ℝ) ≤ 6 * K + 14 := by
      intro c
      have h := card_binsAround_le (c := c) hp (by positivity : 0 ≤ p * (3 * K + 6))
      have : 2 * (p * (3 * K + 6)) / p + 2 = 6 * K + 14 := by field_simp; ring
      linarith
    have hprod : (∏ i : Fin 2, ((binsAround p (p * b.1 i + k * p * (p * b.2.1 i))
        (p * (K + 3))).card : ℝ)) ≤ (2 * K + 8) ^ 2 := by
      rw [Fin.prod_univ_two, sq]
      exact mul_le_mul (hb1 _) (hb1 _) (Nat.cast_nonneg _) (by positivity)
    rw [one_mul]
    exact mul_le_mul hprod (hb2 _) (Nat.cast_nonneg _) (by positivity)
  have hcardk : ((Finset.Icc (0 : ℤ) ⌊1 / p⌋).card : ℝ) ≤ 2 / p := by
    rw [Int.card_Icc]
    have hfl : (0 : ℤ) ≤ ⌊1 / p⌋ := Int.floor_nonneg.mpr (by positivity)
    have hcast : (((⌊1 / p⌋ + 1 - 0).toNat : ℕ) : ℝ) = (⌊1 / p⌋ : ℝ) + 1 := by
      have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ ⌊1 / p⌋ + 1 by omega)
      have h' : (((⌊1 / p⌋ + 1).toNat : ℤ) : ℝ) = ((⌊1 / p⌋ + 1 : ℤ) : ℝ) := by rw [h]
      push_cast at h'
      rw [sub_zero]
      exact_mod_cast h'
    rw [hcast]
    have h1 : (⌊1 / p⌋ : ℝ) ≤ 1 / p := Int.floor_le _
    have h2 : 1 ≤ 1 / p := by rw [le_div_iff₀ hp]; linarith
    have h3 : 2 / p = 1 / p + 1 / p := by ring
    linarith
  have hsum : ((cellsOf K p b).card : ℝ) ≤
      ((Finset.Icc (0 : ℤ) ⌊1 / p⌋).card : ℝ) * ((2 * K + 8) ^ 2 * (6 * K + 14)) := by
    calc ((cellsOf K p b).card : ℝ)
        ≤ ∑ k ∈ Finset.Icc (0 : ℤ) ⌊1 / p⌋, (({k} ×ˢ (Fintype.piFinset (fun i => binsAround p
          (p * b.1 i + k * p * (p * b.2.1 i)) (p * (K + 3))) ×ˢ binsAround p
          (p * b.2.2 0 + k * p * (p * b.2.2 1) + (k * p) ^ 2 * (p * b.2.2 2))
            (p * (3 * K + 6)))).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Finset.Icc (0 : ℤ) ⌊1 / p⌋, (2 * K + 8) ^ 2 * (6 * K + 14) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hC0 : 0 ≤ (2 * K + 8) ^ 2 * (6 * K + 14) := by positivity
  calc p * ((cellsOf K p b).card : ℝ)
      ≤ p * (((Finset.Icc (0 : ℤ) ⌊1 / p⌋).card : ℝ) * ((2 * K + 8) ^ 2 * (6 * K + 14))) :=
        mul_le_mul_of_nonneg_left hsum hp.le
    _ ≤ p * (2 / p * ((2 * K + 8) ^ 2 * (6 * K + 14))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcardk hC0) hp.le
    _ = cellConst K := by unfold cellConst; field_simp

/-- **Step 4 (geometry).** `⌊X'/p⌋` lies in the `X'` bins of the event's block and time bin. -/
theorem floor_derivX_mem_xBins (hp : 0 < p) (hp1 : p ≤ 1)
    (hbound : ∀ l, (∀ i, |y0 l i| ≤ K) ∧ (∀ i, |V l i| ≤ K) ∧ (∀ j, |a l j| ≤ K))
    {z : X × ℝ} (ht : z.2 ∈ Icc (0 : ℝ) 1) :
    ⌊derivX a z / p⌋ ∈ xBins K p (full7 y0 V a p z.1) (physCode y0 V a p z).1 :=
  floor_mem_binsAround hp (derivX_estimate hp hp1 ((hbound z.1).2.2 2) ht)

theorem card_xBins_le (hp : 0 < p) (hK : 0 ≤ K) (b : Full7C) (k : ℤ) :
    ((xBins K p b k).card : ℝ) ≤ 4 * K + 12 := by
  have h := card_binsAround_le (c := p * b.2.2 1 + 2 * (k * p) * (p * b.2.2 2)) hp
    (by positivity : 0 ≤ p * (2 * K + 5))
  have : 2 * (p * (2 * K + 5)) / p + 2 = 4 * K + 12 := by field_simp; ring
  unfold xBins
  linarith

end Geometry

/-! ### Measurability -/

section Measurability

variable [MeasurableSpace X] {y0 V : X → Fin 2 → ℝ} {a : X → Fin 3 → ℝ} {p : ℝ}

theorem measurable_physCode (hy0 : Measurable y0) (hV : Measurable V) (ha : Measurable a) :
    Measurable (physCode y0 V a p) := by
  have hc (f : X → Fin 2 → ℝ) (hf : Measurable f) (i : Fin 2) :
      Measurable fun z : X × ℝ => f z.1 i := (measurable_pi_apply i).comp (hf.comp measurable_fst)
  have ha' (j : Fin 3) : Measurable fun z : X × ℝ => a z.1 j :=
    (measurable_pi_apply j).comp (ha.comp measurable_fst)
  refine Measurable.prodMk (measurable_snd.div_const p).floor (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.mpr fun i =>
      ((hc y0 hy0 i).add (measurable_snd.mul (hc V hV i))).div_const p |>.floor
  · exact (((ha' 0).add (measurable_snd.mul (ha' 1))).add
      ((measurable_snd.pow_const 2).mul (ha' 2))).div_const p |>.floor

theorem measurable_full7 (hy0 : Measurable y0) (hV : Measurable V) (ha : Measurable a) :
    Measurable (full7 y0 V a p) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.mpr fun i => (((measurable_pi_apply i).comp hy0).div_const p).floor
  · exact measurable_pi_iff.mpr fun i => (((measurable_pi_apply i).comp hV).div_const p).floor
  · exact measurable_pi_iff.mpr fun j => (((measurable_pi_apply j).comp ha).div_const p).floor

end Measurability

/-! ### Pruning -/

section Pruning

variable [MeasurableSpace X] {Vc : Type*} [MeasurableSpace Vc] [MeasurableSingletonClass Vc]
  [Countable Vc]

/-- The entry of an event: (full7 code, velocity code), physical cell. -/
def entry (y0 V : X → Fin 2 → ℝ) (a : X → Fin 3 → ℝ) (vcode : X → Vc) (p : ℝ) (z : X × ℝ) :
    (Full7C × Vc) × PhysC :=
  ((full7 y0 V a p z.1, vcode z.1), physCode y0 V a p z)

/-- The prior block of a (full7 code, velocity code). -/
def block (y0 V : X → Fin 2 → ℝ) (a : X → Fin 3 → ℝ) (vcode : X → Vc) (p : ℝ)
    (B : Full7C × Vc) : Set X :=
  {l | full7 y0 V a p l = B.1 ∧ vcode l = B.2}

/-- Reference weight of an entry: `p θ(block)` on the block's own cells, `0` elsewhere. -/
def refWeight (θ : Measure X) (y0 V : X → Fin 2 → ℝ) (a : X → Fin 3 → ℝ) (vcode : X → Vc)
    (K p : ℝ) (e : (Full7C × Vc) × PhysC) : ℝ≥0∞ :=
  if e.2 ∈ cellsOf K p e.1.1 then ENNReal.ofReal p * θ (block y0 V a vcode p e.1) else 0

/-- The retained incidences: entries of current mass `≥ δ p θ(block)`, outside null palette
bins. -/
def retained (μ : Measure (X × ℝ)) (θ : Measure X) (E : Set (X × ℝ)) (y0 V : X → Fin 2 → ℝ)
    (a : X → Fin 3 → ℝ) (vcode : X → Vc) (π : Vc → ℝ≥0∞) (K p δ : ℝ) : Set (X × ℝ) :=
  E ∩ referenceKeep (μ.restrict E) (entry y0 V a vcode p) (refWeight θ y0 V a vcode K p)
    (ENNReal.ofReal δ) ∩ {z | π (vcode z.1) ≠ 0}

variable {y0 V : X → Fin 2 → ℝ} {a : X → Fin 3 → ℝ} {vcode : X → Vc} {K p : ℝ}

theorem measurable_entry (hy0 : Measurable y0) (hV : Measurable V) (ha : Measurable a)
    (hvc : Measurable vcode) : Measurable (entry y0 V a vcode p) :=
  ((measurable_full7 hy0 hV ha).comp measurable_fst |>.prodMk (hvc.comp measurable_fst)).prodMk
    (measurable_physCode hy0 hV ha)

theorem measurableSet_block (hy0 : Measurable y0) (hV : Measurable V) (ha : Measurable a)
    (hvc : Measurable vcode) (B : Full7C × Vc) : MeasurableSet (block y0 V a vcode p B) := by
  have hm : Measurable fun l => (full7 y0 V a p l, vcode l) :=
    (measurable_full7 hy0 hV ha).prodMk hvc
  have h := hm (measurableSet_singleton B)
  convert h using 1
  ext l
  simp only [block, mem_setOf_eq, mem_preimage, mem_singleton_iff, Prod.ext_iff]

theorem measurableSet_retained (μ : Measure (X × ℝ)) (θ : Measure X) {E : Set (X × ℝ)}
    (hE : MeasurableSet E) (hy0 : Measurable y0) (hV : Measurable V) (ha : Measurable a)
    (hvc : Measurable vcode) (π : Vc → ℝ≥0∞) (δ : ℝ) :
    MeasurableSet (retained μ θ E y0 V a vcode π K p δ) := by
  refine (hE.inter (measurableSet_referenceKeep _ _ (measurable_entry hy0 hV ha hvc) _ _)).inter ?_
  have h : {z : X × ℝ | π (vcode z.1) ≠ 0} = (fun z : X × ℝ => vcode z.1) ⁻¹' {v | π v ≠ 0} := rfl
  rw [h]
  exact (hvc.comp measurable_fst) (Set.to_countable _).measurableSet

/-- The total reference weight is at most `cellConst K · θ(univ)`. -/
theorem tsum_refWeight_le (θ : Measure X) (hy0 : Measurable y0) (hV : Measurable V)
    (ha : Measurable a) (hvc : Measurable vcode) (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 ≤ K) :
    ∑' e, refWeight θ y0 V a vcode K p e ≤ ENNReal.ofReal (cellConst K) * θ univ := by
  classical
  rw [ENNReal.tsum_prod']
  have hinner : ∀ B : Full7C × Vc, ∑' w : PhysC, refWeight θ y0 V a vcode K p (B, w) ≤
      ENNReal.ofReal (cellConst K) * θ (block y0 V a vcode p B) := by
    intro B
    rw [tsum_eq_sum (s := cellsOf K p B.1) (fun w hw => by simp [refWeight, hw])]
    have hs : ∑ w ∈ cellsOf K p B.1, refWeight θ y0 V a vcode K p (B, w) =
        ∑ _w ∈ cellsOf K p B.1, ENNReal.ofReal p * θ (block y0 V a vcode p B) :=
      Finset.sum_congr rfl fun w hw => by simp [refWeight, hw]
    rw [hs, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
    gcongr
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm]
    exact card_cellsOf_mul_le hp hp1 hK B.1
  calc ∑' B, ∑' w, refWeight θ y0 V a vcode K p (B, w)
      ≤ ∑' B, ENNReal.ofReal (cellConst K) * θ (block y0 V a vcode p B) :=
        ENNReal.tsum_le_tsum hinner
    _ = ENNReal.ofReal (cellConst K) * ∑' B, θ (block y0 V a vcode p B) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (cellConst K) * θ (⋃ B, block y0 V a vcode p B) := by
        rw [measure_iUnion]
        · intro B B' hBB'
          refine Set.disjoint_left.mpr fun l hl hl' => hBB' ?_
          exact Prod.ext (hl.1.symm.trans hl'.1) (hl.2.symm.trans hl'.2)
        · exact measurableSet_block hy0 hV ha hvc
    _ ≤ ENNReal.ofReal (cellConst K) * θ univ := by gcongr; exact subset_univ _

/-- **Step 2.** The deleted incidences cost at most `δ · cellConst K · θ(univ)`. -/
theorem retained_cost (μ : Measure (X × ℝ)) (θ : Measure X) {E : Set (X × ℝ)}
    (hE : MeasurableSet E) (hy0 : Measurable y0) (hV : Measurable V) (ha : Measurable a)
    (hvc : Measurable vcode) (π : Vc → ℝ≥0∞) {δ Kcap Fp : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hK : 0 ≤ K)
    (hcap : ∀ (w : PhysC) (v : Vc), μ (E ∩ {z | physCode y0 V a p z = w ∧ vcode z.1 = v}) ≤
      ENNReal.ofReal (Kcap * p ^ 3 * Fp) * π v) :
    μ (E \ retained μ θ E y0 V a vcode π K p δ) ≤
      ENNReal.ofReal δ * (ENNReal.ofReal (cellConst K) * θ univ) := by
  classical
  set keep := referenceKeep (μ.restrict E) (entry y0 V a vcode p) (refWeight θ y0 V a vcode K p)
    (ENNReal.ofReal δ)
  have hsub : E \ retained μ θ E y0 V a vcode π K p δ ⊆
      (E ∩ keepᶜ) ∪ (E ∩ {z | π (vcode z.1) = 0}) := by
    intro z hz
    by_cases hk : z ∈ keep
    · right
      refine ⟨hz.1, ?_⟩
      by_contra hπ
      exact hz.2 ⟨⟨hz.1, hk⟩, hπ⟩
    · left
      exact ⟨hz.1, hk⟩
  have hnull : μ (E ∩ {z | π (vcode z.1) = 0}) = 0 := by
    have hsub' : E ∩ {z | π (vcode z.1) = 0} ⊆
        ⋃ w : PhysC, ⋃ v : {v : Vc // π v = 0},
          E ∩ {z | physCode y0 V a p z = w ∧ vcode z.1 = v.1} := by
      intro z hz
      exact mem_iUnion.mpr ⟨physCode y0 V a p z, mem_iUnion.mpr
        ⟨⟨vcode z.1, hz.2⟩, hz.1, rfl, rfl⟩⟩
    refine measure_mono_null hsub' (measure_iUnion_null fun w => measure_iUnion_null fun v => ?_)
    have h := hcap w v.1
    rw [v.2, mul_zero] at h
    exact le_antisymm h zero_le
  have hkeep : μ (E ∩ keepᶜ) ≤ ENNReal.ofReal δ * (ENNReal.ofReal (cellConst K) * θ univ) := by
    have hk : MeasurableSet keep :=
      measurableSet_referenceKeep _ _ (measurable_entry hy0 hV ha hvc) _ _
    calc μ (E ∩ keepᶜ) = (μ.restrict E) keepᶜ := by
          rw [Measure.restrict_apply hk.compl, inter_comm]
      _ ≤ ENNReal.ofReal δ * ∑' e, refWeight θ y0 V a vcode K p e :=
          reference_light_mass_le _ _ _ _
      _ ≤ _ := by gcongr; exact tsum_refWeight_le θ hy0 hV ha hvc hp hp1 hK
  calc μ (E \ retained μ θ E y0 V a vcode π K p δ)
      ≤ μ ((E ∩ keepᶜ) ∪ (E ∩ {z | π (vcode z.1) = 0})) := measure_mono hsub
    _ ≤ μ (E ∩ keepᶜ) + μ (E ∩ {z | π (vcode z.1) = 0}) := measure_union_le _ _
    _ ≤ _ := by rw [hnull, add_zero]; exact hkeep

/-- The full7 blocks kept at a physical cell `w` and velocity code `v`. -/
def survivors (μ : Measure (X × ℝ)) (θ : Measure X) (E : Set (X × ℝ)) (y0 V : X → Fin 2 → ℝ)
    (a : X → Fin 3 → ℝ) (vcode : X → Vc) (π : Vc → ℝ≥0∞) (K p δ : ℝ) (w : PhysC) (v : Vc) :
    Finset Full7C := by
  classical
  exact (full7Box K p).filter fun b =>
    ∃ z ∈ retained μ θ E y0 V a vcode π K p δ, entry y0 V a vcode p z = ((b, v), w)

/-- **Step 3.** At most `Kcap/(δζ)` full7 blocks survive at each (physical cell, velocity
code). -/
theorem card_survivors_le (μ : Measure (X × ℝ)) (θ : Measure X) {E : Set (X × ℝ)}
    (hE : MeasurableSet E) (hy0 : Measurable y0) (hV : Measurable V) (ha : Measurable a)
    (hvc : Measurable vcode) (π : Vc → ℝ≥0∞) (hπ : ∀ v, π v ≠ ∞) {δ ζ Fp Kcap : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ) (hζ : 0 < ζ) (hFp : 0 < Fp) (hKcap : 0 ≤ Kcap)
    (hbound : ∀ l, (∀ i, |y0 l i| ≤ K) ∧ (∀ i, |V l i| ≤ K) ∧ (∀ j, |a l j| ≤ K))
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hfloor : ∀ z ∈ E, ENNReal.ofReal (ζ * p ^ 2 * Fp) * π (vcode z.1) ≤
      θ (block y0 V a vcode p (full7 y0 V a p z.1, vcode z.1)))
    (hcap : ∀ (w : PhysC) (v : Vc), μ (E ∩ {z | physCode y0 V a p z = w ∧ vcode z.1 = v}) ≤
      ENNReal.ofReal (Kcap * p ^ 3 * Fp) * π v) (w : PhysC) (v : Vc) :
    ((survivors μ θ E y0 V a vcode π K p δ w v).card : ℝ) ≤ Kcap / (δ * ζ) := by
  classical
  set S := survivors μ θ E y0 V a vcode π K p δ w v with hSdef
  set keep := referenceKeep (μ.restrict E) (entry y0 V a vcode p) (refWeight θ y0 V a vcode K p)
    (ENNReal.ofReal δ)
  let fiber : Full7C → Set (X × ℝ) := fun b => E ∩ entry y0 V a vcode p ⁻¹' {((b, v), w)}
  have hfiber_meas : ∀ b, MeasurableSet (fiber b) := fun b =>
    hE.inter (measurable_entry hy0 hV ha hvc (measurableSet_singleton _))
  by_cases hS : S = ∅
  · rw [hS, Finset.card_empty, Nat.cast_zero]
    positivity
  -- a witness in each surviving block
  have hwit : ∀ b ∈ S, ∃ z ∈ retained μ θ E y0 V a vcode π K p δ,
      entry y0 V a vcode p z = ((b, v), w) := fun b hb => (Finset.mem_filter.mp hb).2
  obtain ⟨b₀, hb₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  obtain ⟨z₀, hz₀, hz₀e⟩ := hwit b₀ hb₀
  have hπv : π v ≠ 0 := by
    have h := hz₀.2
    have hv : vcode z₀.1 = v := congrArg (fun e => e.1.2) hz₀e
    simpa only [mem_setOf_eq, hv] using h
  -- each surviving fiber carries mass `≥ δ ζ p³ Fp π v`
  have hlow : ∀ b ∈ S, ENNReal.ofReal (δ * ζ * p ^ 3 * Fp) * π v ≤ μ (fiber b) := by
    intro b hb
    obtain ⟨z, hz, hze⟩ := hwit b hb
    have hzE : z ∈ E := hz.1.1
    have hzk : z ∈ keep := hz.1.2
    have hb' : full7 y0 V a p z.1 = b := congrArg (fun e => e.1.1) hze
    have hv' : vcode z.1 = v := congrArg (fun e => e.1.2) hze
    have hw' : physCode y0 V a p z = w := congrArg (fun e => e.2) hze
    have hcell : w ∈ cellsOf K p b := by
      rw [← hw', ← hb']
      exact physCode_mem_cellsOf hp hp1 hbound (hunit hzE).2
    have hkeep : ENNReal.ofReal δ * refWeight θ y0 V a vcode K p ((b, v), w) ≤
        (μ.restrict E) (entry y0 V a vcode p ⁻¹' {((b, v), w)}) := by
      have h : ENNReal.ofReal δ * refWeight θ y0 V a vcode K p (entry y0 V a vcode p z) ≤
          (μ.restrict E) (entry y0 V a vcode p ⁻¹' {entry y0 V a vcode p z}) := hzk
      rwa [hze] at h
    have hrw : refWeight θ y0 V a vcode K p ((b, v), w) =
        ENNReal.ofReal p * θ (block y0 V a vcode p (b, v)) := by
      simp [refWeight, hcell]
    have hfl : ENNReal.ofReal (ζ * p ^ 2 * Fp) * π v ≤ θ (block y0 V a vcode p (b, v)) := by
      have h := hfloor z hzE
      rwa [hb', hv'] at h
    have hres : (μ.restrict E) (entry y0 V a vcode p ⁻¹' {((b, v), w)}) = μ (fiber b) := by
      rw [Measure.restrict_apply (measurable_entry hy0 hV ha hvc (measurableSet_singleton _)),
        inter_comm]
    calc ENNReal.ofReal (δ * ζ * p ^ 3 * Fp) * π v
        = ENNReal.ofReal δ * (ENNReal.ofReal p * (ENNReal.ofReal (ζ * p ^ 2 * Fp) * π v)) := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hδ.le,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
      _ ≤ ENNReal.ofReal δ * (ENNReal.ofReal p * θ (block y0 V a vcode p (b, v))) := by
          gcongr
      _ = ENNReal.ofReal δ * refWeight θ y0 V a vcode K p ((b, v), w) := by rw [hrw]
      _ ≤ _ := hkeep
      _ = μ (fiber b) := hres
  -- the fibers are disjoint inside the joint cell
  have hdisj : Set.PairwiseDisjoint (↑S : Set Full7C) fiber := by
    intro b _ b' _ hbb'
    refine Set.disjoint_left.mpr fun z hz hz' => hbb' ?_
    have h1 : entry y0 V a vcode p z = ((b, v), w) := hz.2
    have h2 : entry y0 V a vcode p z = ((b', v), w) := hz'.2
    have := h1.symm.trans h2
    exact congrArg (fun e => e.1.1) this
  have hunion : (⋃ b ∈ S, fiber b) ⊆ E ∩ {z | physCode y0 V a p z = w ∧ vcode z.1 = v} := by
    intro z hz
    obtain ⟨b, -, hzb⟩ := mem_iUnion₂.mp hz
    have he : entry y0 V a vcode p z = ((b, v), w) := hzb.2
    exact ⟨hzb.1, congrArg (fun e => e.2) he, congrArg (fun e => e.1.2) he⟩
  have hsum : (S.card : ℝ≥0∞) * (ENNReal.ofReal (δ * ζ * p ^ 3 * Fp) * π v) ≤
      ENNReal.ofReal (Kcap * p ^ 3 * Fp) * π v := by
    calc (S.card : ℝ≥0∞) * (ENNReal.ofReal (δ * ζ * p ^ 3 * Fp) * π v)
        = ∑ _b ∈ S, ENNReal.ofReal (δ * ζ * p ^ 3 * Fp) * π v := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ S, μ (fiber b) := Finset.sum_le_sum hlow
      _ = μ (⋃ b ∈ S, fiber b) := (measure_biUnion_finset hdisj fun b _ => hfiber_meas b).symm
      _ ≤ _ := (measure_mono hunion).trans (hcap w v)
  rw [← mul_assoc] at hsum
  have hsum' := (ENNReal.mul_le_mul_iff_left hπv (hπ v)).mp hsum
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hsum'
  have hpos : 0 < p ^ 3 * Fp := by positivity
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum'
  rw [le_div_iff₀ (mul_pos hδ hζ)]
  have h1 : (S.card : ℝ) * (δ * ζ * p ^ 3 * Fp) = ((S.card : ℝ) * (δ * ζ)) * (p ^ 3 * Fp) := by
    ring
  have h2 : Kcap * p ^ 3 * Fp = Kcap * (p ^ 3 * Fp) := by ring
  rw [h1, h2] at hreal
  exact le_of_mul_le_mul_right hreal hpos

/-- The `X'` list at a physical cell and velocity code. -/
def xList (μ : Measure (X × ℝ)) (θ : Measure X) (E : Set (X × ℝ)) (y0 V : X → Fin 2 → ℝ)
    (a : X → Fin 3 → ℝ) (vcode : X → Vc) (π : Vc → ℝ≥0∞) (K p δ : ℝ) (w : PhysC) (v : Vc) :
    Finset ℤ :=
  (survivors μ θ E y0 V a vcode π K p δ w v).biUnion fun b => xBins K p b w.1

/-- **Step 4.** On every retained incidence, `⌊X'/p⌋` lies in the list of its (physical cell,
velocity code). -/
theorem floor_derivX_mem_xList (μ : Measure (X × ℝ)) (θ : Measure X) {E : Set (X × ℝ)}
    (π : Vc → ℝ≥0∞) {δ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hbound : ∀ l, (∀ i, |y0 l i| ≤ K) ∧ (∀ i, |V l i| ≤ K) ∧ (∀ j, |a l j| ≤ K))
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {z : X × ℝ}
    (hz : z ∈ retained μ θ E y0 V a vcode π K p δ) :
    ⌊derivX a z / p⌋ ∈ xList μ θ E y0 V a vcode π K p δ (physCode y0 V a p z) (vcode z.1) := by
  classical
  simp only [xList, Finset.mem_biUnion]
  refine ⟨full7 y0 V a p z.1, ?_, floor_derivX_mem_xBins hp hp1 hbound (hunit hz.1.1).2⟩
  simp only [survivors, Finset.mem_filter]
  exact ⟨full7_mem_full7Box hp hbound z.1, z, hz, rfl⟩

theorem card_xList_le (μ : Measure (X × ℝ)) (θ : Measure X) {E : Set (X × ℝ)}
    (hE : MeasurableSet E) (hy0 : Measurable y0) (hV : Measurable V) (ha : Measurable a)
    (hvc : Measurable vcode) (π : Vc → ℝ≥0∞) (hπ : ∀ v, π v ≠ ∞) {δ ζ Fp Kcap : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 ≤ K) (hδ : 0 < δ) (hζ : 0 < ζ) (hFp : 0 < Fp)
    (hKcap : 0 ≤ Kcap) (hbound : ∀ l, (∀ i, |y0 l i| ≤ K) ∧ (∀ i, |V l i| ≤ K) ∧ (∀ j, |a l j| ≤ K))
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hfloor : ∀ z ∈ E, ENNReal.ofReal (ζ * p ^ 2 * Fp) * π (vcode z.1) ≤
      θ (block y0 V a vcode p (full7 y0 V a p z.1, vcode z.1)))
    (hcap : ∀ (w : PhysC) (v : Vc), μ (E ∩ {z | physCode y0 V a p z = w ∧ vcode z.1 = v}) ≤
      ENNReal.ofReal (Kcap * p ^ 3 * Fp) * π v) (w : PhysC) (v : Vc) :
    ((xList μ θ E y0 V a vcode π K p δ w v).card : ℝ) ≤ (4 * K + 12) * (Kcap / (δ * ζ)) := by
  classical
  have hS := card_survivors_le μ θ hE hy0 hV ha hvc π hπ hp hp1 hδ hζ hFp hKcap hbound hunit
    hfloor hcap w v
  calc ((xList μ θ E y0 V a vcode π K p δ w v).card : ℝ)
      ≤ ∑ b ∈ survivors μ θ E y0 V a vcode π K p δ w v, ((xBins K p b w.1).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ survivors μ θ E y0 V a vcode π K p δ w v, (4 * K + 12) :=
        Finset.sum_le_sum fun b _ => card_xBins_le hp hK b w.1
    _ = ((survivors μ θ E y0 V a vcode π K p δ w v).card : ℝ) * (4 * K + 12) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Kcap / (δ * ζ)) * (4 * K + 12) :=
        mul_le_mul_of_nonneg_right hS (by positivity)
    _ = _ := by ring

end Pruning

end Full7EntryPruning

end

end Submission.Lib.K4ThreeBaseRows
