import Mathlib

namespace Submission.Obl.k4_horizontal_three_traversal_spreading

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- The local law, with its scales and its finite occupied-cell table. -/
structure Law (α : Type) [MeasurableSpace α] where
  σ : Measure (α × ℝ)
  π : Measure ℝ
  x : α → ℝ → Fin 3 → ℝ
  vel : α → ℝ
  bin : α → ℤ
  state : α × ℝ → ℕ
  G : Set (α × ℝ)
  F : Finset (ℤ × (Fin 3 → ℤ))
  h : ℝ
  ω : ℝ
  L : ℝ
  B : ℝ

namespace Law

variable {α : Type} [MeasurableSpace α] (D : Law α)

structure Valid : Prop where
  prob_σ : IsProbabilityMeasure D.σ
  prob_π : IsProbabilityMeasure D.π
  meas_x : Measurable (Function.uncurry D.x)
  meas_vel : Measurable D.vel
  meas_bin : Measurable D.bin
  meas_state : Measurable D.state
  meas_G : MeasurableSet D.G
  full_G : D.σ D.Gᶜ = 0
  density : D.σ ≤ ENNReal.ofReal D.L • ((D.σ.map Prod.fst).prod volume)
  geometry : ∀ p ∈ D.G,
    p.2 ∈ Icc (0 : ℝ) 1 ∧ |D.vel p.1| ≤ D.B ∧
    (∀ t ∈ Icc (0 : ℝ) 1, D.x p.1 t 0 = t ∧ ∀ e, |D.x p.1 t e| ≤ D.B) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      D.x p.1 u 1 = D.x p.1 t 1 + D.vel p.1 * (u - t) ∧
      |D.x p.1 u 2 - D.x p.1 t 2 - (-D.x p.1 t 1 + t * D.vel p.1) * (u - t)| ≤ D.h
  state_geometry : ∀ p ∈ D.G, ∀ q ∈ D.G, D.state p = D.state q →
    D.bin p.1 = D.bin q.1 ∧ ∀ e, |D.x p.1 p.2 e - D.x q.1 q.2 e| ≤ D.h
  palette : ∀ q j,
    D.σ {p | D.state p = q ∧ ⌊D.vel p.1 / D.h⌋ = j} ≤
      ENNReal.ofReal D.L * D.σ {p | D.state p = q} * D.π {w | ⌊w / D.h⌋ = j}
  support : ∀ᵐ p ∂D.σ, (D.bin p.1, fun e => ⌊D.x p.1 p.2 e / D.ω⌋) ∈ D.F
  h_pos : 0 < D.h
  ω_pos : 0 < D.ω
  L_nonneg : 0 ≤ D.L
  B_nonneg : 0 ≤ D.B

def Z0 : α → ℝ := fun l => D.x l 0 1

def Y0 : α → ℝ := fun l => D.x l 0 2

def vb : α → ℤ := fun l => ⌊D.vel l / D.h⌋

def palMass (z : ℤ) : ℝ := (D.π {w | ⌊w / D.h⌋ = z}).toReal

theorem meas_Z0 (hD : D.Valid) : Measurable D.Z0 :=
  (measurable_pi_apply 1).comp (hD.meas_x.comp (measurable_id.prodMk measurable_const))

theorem meas_Y0 (hD : D.Valid) : Measurable D.Y0 :=
  (measurable_pi_apply 2).comp (hD.meas_x.comp (measurable_id.prodMk measurable_const))

theorem meas_vb (hD : D.Valid) : Measurable D.vb :=
  Int.measurable_floor.comp (hD.meas_vel.div_const D.h)

theorem ae_mem_G (hD : D.Valid) : ∀ᵐ p ∂D.σ, p ∈ D.G := by
  exact ae_iff.mpr hD.full_G

theorem coeff_bounds (hD : D.Valid) {p : α × ℝ} (hp : p ∈ D.G) :
    |D.Z0 p.1| ≤ D.B ∧ |D.Y0 p.1| ≤ D.B := by
  have h := (hD.geometry p hp).2.2.1 0 (by norm_num)
  exact ⟨h.2 1, h.2 2⟩

/-- The approximate trajectories differ from exact horizontal lines only in
one coordinate, by the specified fine error. -/
theorem exact_line_close (hD : D.Valid) {p : α × ℝ} (hp : p ∈ D.G) :
    ∀ i, |D.x p.1 p.2 i -
      (![p.2, D.Z0 p.1 + D.vel p.1 * p.2, D.Y0 p.1 - D.Z0 p.1 * p.2] : Fin 3 → ℝ) i| ≤ D.h := by
  have ht := (hD.geometry p hp).1
  have hline := (hD.geometry p hp).2.2.2 0 (by norm_num) p.2 ht
  intro i
  fin_cases i
  · change |D.x p.1 p.2 0 - p.2| ≤ D.h
    rw [(hD.geometry p hp).2.2.1 p.2 ht |>.1, sub_self, abs_zero]
    exact hD.h_pos.le
  · change |D.x p.1 p.2 1 - (D.Z0 p.1 + D.vel p.1 * p.2)| ≤ D.h
    simpa [Z0, sub_zero, hline.1] using hD.h_pos.le
  · change |D.x p.1 p.2 2 - (D.Y0 p.1 - D.Z0 p.1 * p.2)| ≤ D.h
    convert hline.2 using 1 <;> dsimp [Z0, Y0] <;> congr 1 <;> ring

/-- Time has no atom at the endpoint, as a consequence of the original
conditional density bound. -/
theorem ae_time_ne_one (hD : D.Valid) : ∀ᵐ p ∂D.σ, p.2 ≠ 1 := by
  letI := hD.prob_σ
  have hle := Measure.le_iff.mp hD.density
    (univ ×ˢ ({1} : Set ℝ)) (MeasurableSet.univ.prod (measurableSet_singleton 1))
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, Real.volume_singleton,
    mul_zero] at hle
  rw [ae_iff]
  have hset : {p : α × ℝ | ¬p.2 ≠ 1} = univ ×ˢ ({1} : Set ℝ) := by ext p; simp
  rw [hset]
  exact le_antisymm hle (zero_le)

/-- A finite initial collection of whole states retains at least half of the
probability. No geometric or conditional restriction is made within a state. -/
theorem exists_state_truncation (hD : D.Valid) :
    ∃ n : ℕ, (1 / 2 : ENNReal) ≤ D.σ {p | D.state p < n} := by
  letI := hD.prob_σ
  have hm : Monotone (fun n : ℕ => {p | D.state p < n}) := by
    intro m n hmn p hp
    exact lt_of_lt_of_le hp hmn
  have hu : (⋃ n : ℕ, {p | D.state p < n}) = univ := by
    ext p
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨D.state p + 1, Nat.lt_succ_self _⟩
  have hs := hm.measure_iUnion (μ := D.σ)
  rw [hu, measure_univ] at hs
  by_contra hn
  push Not at hn
  have h : (1 : ENNReal) ≤ 1 / 2 := by
    calc
      (1 : ENNReal) = ⨆ n, D.σ {p | D.state p < n} := hs
      _ ≤ 1 / 2 := iSup_le (fun n => (hn n).le)
  norm_num at h

/-- Adding the invariant bin to a state key preserves its palette ceiling. -/
theorem state_bin_palette (hD : D.Valid) (q : ℕ) (j z : ℤ) :
    D.σ {p | D.state p = q ∧ D.bin p.1 = j ∧ D.vb p.1 = z} ≤
      ENNReal.ofReal D.L * D.σ {p | D.state p = q ∧ D.bin p.1 = j} *
        D.π {w | ⌊w / D.h⌋ = z} := by
  by_cases hex : ∃ p ∈ D.G, D.state p = q ∧ D.bin p.1 = j
  · obtain ⟨p, hp, hq, hj⟩ := hex
    have hbin : ∀ᵐ r ∂D.σ, D.state r = q → D.bin r.1 = j := by
      filter_upwards [D.ae_mem_G hD] with r hr heq
      exact ((hD.state_geometry r hr p hp (heq.trans hq.symm)).1).trans hj
    have hmass : D.σ {r | D.state r = q ∧ D.bin r.1 = j} = D.σ {r | D.state r = q} := by
      apply measure_congr
      filter_upwards [hbin] with r hr
      apply propext
      exact and_iff_left_of_imp hr
    have hnum : D.σ {r | D.state r = q ∧ D.bin r.1 = j ∧ D.vb r.1 = z} =
        D.σ {r | D.state r = q ∧ ⌊D.vel r.1 / D.h⌋ = z} := by
      apply measure_congr
      filter_upwards [hbin] with r hr
      apply propext
      change (D.state r = q ∧ D.bin r.1 = j ∧ D.vb r.1 = z) ↔ _
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, hr h.1, h.2⟩
    rw [hmass, hnum]
    exact hD.palette q z
  · have hz : D.σ {p | D.state p = q ∧ D.bin p.1 = j} = 0 := by
      apply measure_mono_null (t := D.Gᶜ) ?_ hD.full_G
      intro p hp hG
      exact hex ⟨p, hG, hp⟩
    rw [hz, mul_zero, zero_mul]
    have hsub : {p : α × ℝ | D.state p = q ∧ D.bin p.1 = j ∧ D.vb p.1 = z} ⊆
        {p | D.state p = q ∧ D.bin p.1 = j} := fun p hp => ⟨hp.1, hp.2.1⟩
    exact (measure_mono_null hsub hz).le

end Law
end
end Submission.Obl.k4_horizontal_three_traversal_spreading
