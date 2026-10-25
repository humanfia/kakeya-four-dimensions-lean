import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedMass

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced fit: bins, cells and the confinement of starting scalars

* `vBins`, `cap_sum_v`: summing the sliced cap over the `v`-bins of `|v| ≤ K`;
* `cellRef`, `dot_near_cellRef`: on a `(u, v, v')` cell of side `p` the collision dot product is
  within `12K²p` of a reference value;
* `startBins`, `start_bin_confined`: a colliding second trajectory's starting scalar lies in
  `36K² + 3` bins determined by the first starting bin and the cell (paper: "The equation confines
  the second starting scalar value to `K` bins").
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `v`-bins of trajectories with `|v| ≤ K`. -/
def vBins (K p : ℝ) : Finset ℤ := Finset.Icc ⌊-K / p⌋ ⌊K / p⌋

theorem mem_vBins {K p x : ℝ} (hp : 0 < p) (hx : |x| ≤ K) : ⌊x / p⌋ ∈ vBins K p := by
  rw [vBins, Finset.mem_Icc]
  constructor
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right (neg_le_of_abs_le hx) hp.le)
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right (le_of_abs_le hx) hp.le)

theorem card_vBins {K p : ℝ} (hp : 0 < p) (hK : 0 ≤ K) : ((vBins K p).card : ℝ) ≤ 2 * K / p + 2 := by
  rw [vBins, Int.card_Icc]
  have h1 := Int.floor_le (K / p)
  have h2 := Int.lt_floor_add_one (-K / p)
  have h3 : (0 : ℤ) ≤ ⌊K / p⌋ + 1 - ⌊-K / p⌋ := by
    have : ⌊-K / p⌋ ≤ ⌊K / p⌋ := Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hp.le)
    omega
  have hcast : (((⌊K / p⌋ + 1 - ⌊-K / p⌋).toNat : ℕ) : ℝ) = ((⌊K / p⌋ + 1 - ⌊-K / p⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h3
  rw [hcast]
  push_cast
  have e1 : -K / p = -(K / p) := by ring
  have e2 : 2 * K / p = 2 * (K / p) := by ring
  rw [e1] at h2 ⊢
  rw [e2]
  linarith

/-- Summing the sliced cap over the `v`-bins: `ν{(l,u) ∈ E, L l u ∈ bin b} ≤ (2K/p+2) K p^(1+d)`. -/
theorem cap_sum_v {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hp : 0 < p) (hK : 0 ≤ K)
    (u : ℝ) (b : ℤ) (P : Ω → Prop) :
    D.ν {l | (l, u) ∈ D.E ∧ ⌊D.L l u / p⌋ = b ∧ P l} ≤
      ENNReal.ofReal ((2 * K / p + 2) * (K * p ^ (1 + d))) := by
  have hsub : {l | (l, u) ∈ D.E ∧ ⌊D.L l u / p⌋ = b ∧ P l} ⊆
      ⋃ c ∈ vBins K p, {l | (l, u) ∈ D.E ∧ ⌊D.v l / p⌋ = c ∧ ⌊D.L l u / p⌋ = b} := by
    rintro l ⟨hl, hb, -⟩
    exact mem_iUnion₂.2 ⟨_, mem_vBins hp (H.vbound l), hl, rfl, hb⟩
  calc D.ν {l | (l, u) ∈ D.E ∧ ⌊D.L l u / p⌋ = b ∧ P l}
      ≤ ∑ c ∈ vBins K p, D.ν {l | (l, u) ∈ D.E ∧ ⌊D.v l / p⌋ = c ∧ ⌊D.L l u / p⌋ = b} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _c ∈ vBins K p, ENNReal.ofReal (K * p ^ (1 + d)) :=
        Finset.sum_le_sum (fun c _ => H.cap u c b)
    _ = (vBins K p).card * ENNReal.ofReal (K * p ^ (1 + d)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((2 * K / p + 2) * (K * p ^ (1 + d))) := by
        rw [ENNReal.ofReal_mul (p := 2 * K / p + 2) (by positivity)]
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (card_vBins hp hK)

/-- The reference value of the collision dot product on a `(u, v, v')` cell. -/
def cellRef (D : SlicedData Ω) (p u₀ : ℝ) (i c₁ c₂ : ℤ) : ℝ :=
  ((i : ℝ) * p - u₀) * (D.G ((c₁ : ℝ) * p) - D.G ((c₂ : ℝ) * p)) -
    (D.φ ((i : ℝ) * p) - D.φ u₀) * ((c₁ : ℝ) * p - (c₂ : ℝ) * p)

/-- Inside a cell, the collision dot product is within `12K²p` of its reference value. -/
theorem dot_near_cellRef {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hp : 0 < p)
    (hK : 1 ≤ K) {u₀ u : ℝ} (hu₀ : u₀ ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) {l l' : Ω} :
    |((u - u₀) * (D.G (D.v l) - D.G (D.v l')) - (D.φ u - D.φ u₀) * (D.v l - D.v l')) -
      cellRef D p u₀ ⌊u / p⌋ ⌊D.v l / p⌋ ⌊D.v l' / p⌋| ≤ 12 * K ^ 2 * p := by
  set i := ⌊u / p⌋
  set c₁ := ⌊D.v l / p⌋
  set c₂ := ⌊D.v l' / p⌋
  -- the corner values
  have hi1 : (i : ℝ) * p ≤ u := by
    have := Int.floor_le (u / p); rwa [le_div_iff₀ hp] at this
  have hi2 : u < ((i : ℝ) + 1) * p := by
    have := Int.lt_floor_add_one (u / p); rwa [div_lt_iff₀ hp] at this
  have hi0 : 0 ≤ (i : ℝ) * p := by
    have : (0 : ℤ) ≤ i := Int.floor_nonneg.2 (div_nonneg hu.1 hp.le)
    have : (0 : ℝ) ≤ i := by exact_mod_cast this
    positivity
  have hip : (i : ℝ) * p ∈ Icc (0:ℝ) 1 := ⟨hi0, hi1.trans hu.2⟩
  have hc₁ : |D.v l - (c₁ : ℝ) * p| ≤ p := by
    have a := Int.floor_le (D.v l / p); have b := Int.lt_floor_add_one (D.v l / p)
    rw [le_div_iff₀ hp] at a; rw [div_lt_iff₀ hp] at b
    rw [abs_le]; constructor <;> nlinarith
  have hc₂ : |D.v l' - (c₂ : ℝ) * p| ≤ p := by
    have a := Int.floor_le (D.v l' / p); have b := Int.lt_floor_add_one (D.v l' / p)
    rw [le_div_iff₀ hp] at a; rw [div_lt_iff₀ hp] at b
    rw [abs_le]; constructor <;> nlinarith
  have hvl := H.vbound l
  have hvl' := H.vbound l'
  have hGll : |D.G (D.v l) - D.G (D.v l')| ≤ 2 * K ^ 2 := by
    calc _ ≤ K * |D.v l - D.v l'| := H.Glip _ _
      _ ≤ K * (2 * K) := by
          gcongr
          calc |D.v l - D.v l'| ≤ |D.v l| + |D.v l'| := abs_sub _ _
            _ ≤ 2 * K := by linarith
      _ = 2 * K ^ 2 := by ring
  have hG1 : |D.G (D.v l) - D.G ((c₁ : ℝ) * p)| ≤ K * p :=
    (H.Glip _ _).trans (mul_le_mul_of_nonneg_left hc₁ (by linarith))
  have hG2 : |D.G (D.v l') - D.G ((c₂ : ℝ) * p)| ≤ K * p :=
    (H.Glip _ _).trans (mul_le_mul_of_nonneg_left hc₂ (by linarith))
  have hφu : |D.φ u - D.φ ((i : ℝ) * p)| ≤ 2 * K * p := by
    calc _ ≤ K * (|u - (i : ℝ) * p| + p) := H.φlip u hu _ hip
      _ ≤ K * (p + p) := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ = 2 * K * p := by ring
  have hφi : |D.φ ((i : ℝ) * p) - D.φ u₀| ≤ 2 * K := by
    calc _ ≤ |D.φ ((i : ℝ) * p)| + |D.φ u₀| := abs_sub _ _
      _ ≤ K + K := add_le_add (H.φbound _ hip) (H.φbound _ hu₀)
      _ = 2 * K := by ring
  have hu1 : |u - (i : ℝ) * p| ≤ p := by rw [abs_le]; constructor <;> linarith
  have hiu : |(i : ℝ) * p - u₀| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hip.1, hip.2, hu₀.1, hu₀.2]
  have hv : |D.v l - D.v l'| ≤ 2 * K := by
    calc |D.v l - D.v l'| ≤ |D.v l| + |D.v l'| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  have key : ((u - u₀) * (D.G (D.v l) - D.G (D.v l')) - (D.φ u - D.φ u₀) * (D.v l - D.v l')) -
      cellRef D p u₀ i c₁ c₂ =
      (u - (i : ℝ) * p) * (D.G (D.v l) - D.G (D.v l')) +
      ((i : ℝ) * p - u₀) * ((D.G (D.v l) - D.G ((c₁ : ℝ) * p)) - (D.G (D.v l') - D.G ((c₂ : ℝ) * p))) -
      ((D.φ u - D.φ ((i : ℝ) * p)) * (D.v l - D.v l') +
        (D.φ ((i : ℝ) * p) - D.φ u₀) * ((D.v l - (c₁ : ℝ) * p) - (D.v l' - (c₂ : ℝ) * p))) := by
    simp only [cellRef]; ring
  rw [key]
  have t1 : |(u - (i : ℝ) * p) * (D.G (D.v l) - D.G (D.v l'))| ≤ p * (2 * K ^ 2) := by
    rw [abs_mul]; exact mul_le_mul hu1 hGll (abs_nonneg _) hp.le
  have t2 : |((i : ℝ) * p - u₀) * ((D.G (D.v l) - D.G ((c₁ : ℝ) * p)) -
      (D.G (D.v l') - D.G ((c₂ : ℝ) * p)))| ≤ 1 * (K * p + K * p) := by
    rw [abs_mul]
    exact mul_le_mul hiu ((abs_sub _ _).trans (add_le_add hG1 hG2)) (abs_nonneg _) zero_le_one
  have t3 : |(D.φ u - D.φ ((i : ℝ) * p)) * (D.v l - D.v l')| ≤ 2 * K * p * (2 * K) := by
    rw [abs_mul]; exact mul_le_mul hφu hv (abs_nonneg _) (by positivity)
  have t4 : |(D.φ ((i : ℝ) * p) - D.φ u₀) * ((D.v l - (c₁ : ℝ) * p) - (D.v l' - (c₂ : ℝ) * p))| ≤
      2 * K * (p + p) := by
    rw [abs_mul]
    exact mul_le_mul hφi ((abs_sub _ _).trans (add_le_add hc₁ hc₂)) (abs_nonneg _) (by linarith)
  have tri := abs_sub ((u - (i : ℝ) * p) * (D.G (D.v l) - D.G (D.v l')) +
      ((i : ℝ) * p - u₀) * ((D.G (D.v l) - D.G ((c₁ : ℝ) * p)) - (D.G (D.v l') - D.G ((c₂ : ℝ) * p))))
    ((D.φ u - D.φ ((i : ℝ) * p)) * (D.v l - D.v l') +
        (D.φ ((i : ℝ) * p) - D.φ u₀) * ((D.v l - (c₁ : ℝ) * p) - (D.v l' - (c₂ : ℝ) * p)))
  have tri1 := abs_add_le ((u - (i : ℝ) * p) * (D.G (D.v l) - D.G (D.v l')))
    (((i : ℝ) * p - u₀) * ((D.G (D.v l) - D.G ((c₁ : ℝ) * p)) - (D.G (D.v l') - D.G ((c₂ : ℝ) * p))))
  have tri2 := abs_add_le ((D.φ u - D.φ ((i : ℝ) * p)) * (D.v l - D.v l'))
    ((D.φ ((i : ℝ) * p) - D.φ u₀) * ((D.v l - (c₁ : ℝ) * p) - (D.v l' - (c₂ : ℝ) * p)))
  have hlin : |(u - (i : ℝ) * p) * (D.G (D.v l) - D.G (D.v l')) +
      ((i : ℝ) * p - u₀) * ((D.G (D.v l) - D.G ((c₁ : ℝ) * p)) - (D.G (D.v l') - D.G ((c₂ : ℝ) * p))) -
      ((D.φ u - D.φ ((i : ℝ) * p)) * (D.v l - D.v l') +
        (D.φ ((i : ℝ) * p) - D.φ u₀) * ((D.v l - (c₁ : ℝ) * p) - (D.v l' - (c₂ : ℝ) * p)))| ≤
      p * (2 * K ^ 2) + 1 * (K * p + K * p) + (2 * K * p * (2 * K) + 2 * K * (p + p)) := by
    linarith
  have hKp : K * p ≤ K ^ 2 * p := by
    have : K ≤ K ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hp.le
  calc _ ≤ p * (2 * K ^ 2) + 1 * (K * p + K * p) + (2 * K * p * (2 * K) + 2 * K * (p + p)) := hlin
    _ = 6 * K ^ 2 * p + 6 * (K * p) := by ring
    _ ≤ 6 * K ^ 2 * p + 6 * (K ^ 2 * p) := by linarith
    _ = 12 * K ^ 2 * p := by ring

/-- Floors of nearby reals are close. -/
theorem floor_mem_Icc_of_abs_le {x y r : ℝ} (h : |x - y| ≤ r) :
    ⌊x⌋ ∈ Finset.Icc (⌊y⌋ - (⌈r⌉₊ : ℤ)) (⌊y⌋ + (⌈r⌉₊ : ℤ)) := by
  rw [Finset.mem_Icc]
  have hr : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have ha := (abs_le.1 h).1
  have hb := (abs_le.1 h).2
  constructor
  · have : ((⌊y⌋ - (⌈r⌉₊ : ℤ) : ℤ) : ℝ) < (⌊x⌋ : ℝ) + 1 := by push_cast; linarith
    have : ⌊y⌋ - (⌈r⌉₊ : ℤ) < ⌊x⌋ + 1 := by exact_mod_cast this
    omega
  · have : (⌊x⌋ : ℝ) < ((⌊y⌋ + (⌈r⌉₊ : ℤ) : ℤ) : ℝ) + 1 := by push_cast; linarith
    have : ⌊x⌋ < ⌊y⌋ + (⌈r⌉₊ : ℤ) + 1 := by exact_mod_cast this
    omega

/-- The bins allowed for a second trajectory's starting scalar on a cell. -/
def startBins (D : SlicedData Ω) (p K u₀ : ℝ) (β₀ i c₁ c₂ : ℤ) : Finset ℤ :=
  Finset.Icc (⌊((β₀ : ℝ) * p + cellRef D p u₀ i c₁ c₂) / p⌋ - (⌈18 * K ^ 2⌉₊ : ℤ))
    (⌊((β₀ : ℝ) * p + cellRef D p u₀ i c₁ c₂) / p⌋ + (⌈18 * K ^ 2⌉₊ : ℤ))

theorem card_startBins (D : SlicedData Ω) (p K u₀ : ℝ) (β₀ i c₁ c₂ : ℤ) (hK : 0 ≤ K) :
    ((startBins D p K u₀ β₀ i c₁ c₂).card : ℝ) ≤ 36 * K ^ 2 + 3 := by
  rw [startBins, Int.card_Icc]
  have h : (0:ℤ) ≤ ⌊((β₀ : ℝ) * p + cellRef D p u₀ i c₁ c₂) / p⌋ + (⌈18 * K ^ 2⌉₊ : ℤ) + 1 -
      (⌊((β₀ : ℝ) * p + cellRef D p u₀ i c₁ c₂) / p⌋ - (⌈18 * K ^ 2⌉₊ : ℤ)) := by omega
  have hcast : (((⌊((β₀ : ℝ) * p + cellRef D p u₀ i c₁ c₂) / p⌋ + (⌈18 * K ^ 2⌉₊ : ℤ) + 1 -
      (⌊((β₀ : ℝ) * p + cellRef D p u₀ i c₁ c₂) / p⌋ - (⌈18 * K ^ 2⌉₊ : ℤ))).toNat : ℕ) : ℝ) =
      2 * (⌈18 * K ^ 2⌉₊ : ℝ) + 1 := by
    rw [show (⌊((β₀ : ℝ) * p + cellRef D p u₀ i c₁ c₂) / p⌋ + (⌈18 * K ^ 2⌉₊ : ℤ) + 1 -
      (⌊((β₀ : ℝ) * p + cellRef D p u₀ i c₁ c₂) / p⌋ - (⌈18 * K ^ 2⌉₊ : ℤ))) =
      2 * (⌈18 * K ^ 2⌉₊ : ℤ) + 1 by ring]
    have : (0:ℤ) ≤ 2 * (⌈18 * K ^ 2⌉₊ : ℤ) + 1 := by positivity
    rw [show ((2 * (⌈18 * K ^ 2⌉₊ : ℤ) + 1).toNat : ℝ) = ((2 * (⌈18 * K ^ 2⌉₊ : ℤ) + 1 : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg this]
    push_cast; ring
  rw [hcast]
  have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 18 * K ^ 2 by positivity)
  linarith

/-- **Confinement of the second starting scalar.** -/
theorem start_bin_confined {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hp : 0 < p)
    (hK : 1 ≤ K) {u₀ u : ℝ} (hu₀ : u₀ ∈ Icc (0:ℝ) 1) {l l' : Ω} {β₀ : ℤ}
    (h0 : (l, u₀) ∈ D.E) (h0' : (l', u₀) ∈ D.E) (h1 : (l, u) ∈ D.E) (h1' : (l', u) ∈ D.E)
    (hbin : ⌊D.L l u / p⌋ = ⌊D.L l' u / p⌋) (hβ : ⌊D.L l u₀ / p⌋ = β₀) :
    ⌊D.L l' u₀ / p⌋ ∈ startBins D p K u₀ β₀ ⌊u / p⌋ ⌊D.v l / p⌋ ⌊D.v l' / p⌋ := by
  have hu : u ∈ Icc (0:ℝ) 1 := H.E01 _ h1
  have hclose : |D.L l u - D.L l' u| ≤ p := by
    have := Int.abs_sub_lt_one_of_floor_eq_floor hbin
    rw [← sub_div, abs_div, abs_of_pos hp, div_lt_one hp] at this
    exact this.le
  have hdot := collision_dot H h0 h0' h1 h1' hclose
  have href := dot_near_cellRef H hp hK hu₀ hu (l := l) (l' := l')
  have hb1 : (β₀ : ℝ) * p ≤ D.L l u₀ := by
    have := Int.floor_le (D.L l u₀ / p); rw [hβ, le_div_iff₀ hp] at this; exact this
  have hb2 : D.L l u₀ < (β₀ : ℝ) * p + p := by
    have := Int.lt_floor_add_one (D.L l u₀ / p); rw [hβ, div_lt_iff₀ hp] at this; linarith
  apply floor_mem_Icc_of_abs_le
  set ref := cellRef D p u₀ ⌊u / p⌋ ⌊D.v l / p⌋ ⌊D.v l' / p⌋
  set X := (u - u₀) * (D.G (D.v l) - D.G (D.v l')) - (D.φ u - D.φ u₀) * (D.v l - D.v l')
  have e1 : D.L l' u₀ / p - ((β₀ : ℝ) * p + ref) / p =
      ((D.L l u₀ - (β₀ : ℝ) * p) + (X - ref) - (X - (D.L l' u₀ - D.L l u₀))) / p := by ring
  rw [e1, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  have hθ : |D.L l u₀ - (β₀ : ℝ) * p| ≤ p := by rw [abs_le]; constructor <;> linarith
  have t := abs_sub ((D.L l u₀ - (β₀ : ℝ) * p) + (X - ref)) (X - (D.L l' u₀ - D.L l u₀))
  have t2 := abs_add_le (D.L l u₀ - (β₀ : ℝ) * p) (X - ref)
  have hK2 : (4 * K + 1) * p + p ≤ 6 * K ^ 2 * p := by
    have : 4 * K + 2 ≤ 6 * K ^ 2 := by nlinarith
    nlinarith
  calc |(D.L l u₀ - (β₀ : ℝ) * p) + (X - ref) - (X - (D.L l' u₀ - D.L l u₀))|
      ≤ p + 12 * K ^ 2 * p + (4 * K + 1) * p := by linarith
    _ ≤ 18 * K ^ 2 * p := by linarith

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
