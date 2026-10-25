import Submission.Obl.k4_horizontal_coefficient_count.Common


/-!
# Single-depth setup for the light-mass estimate

This file fixes, at one index `k` of the frozen sequence and one depth `s`,
the facts of the prepared horizontal data used by the light-mass estimate
(paper, Lemma `a06:horizontal-coefficient-count`).  Everything is stated
with real parameters:

* `a = N^(-s)` is the scalar width and the parameter width `D`;
* `χ = N^(-e₀)` is the velocity width and the horizontal-equation error;
* `q = 2^(-T)` is the true time-block length at depth `s`, `g = N^(-κ s)`;
* `w = N^(-2 κ s)` is the cell width used to integrate the base cap over the
  common horizontal box of a true time block.
-/

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The horizontal trajectory coordinates of a coefficient vector. -/
def X1 (β : Fin 6 → ℝ) (t : ℝ) : ℝ := β 0 + t * β 3
/-- The transverse trajectory coordinate. -/
def X2 (β : Fin 6 → ℝ) (t : ℝ) : ℝ := β 1 + t * β 4
/-- The scalar (hidden) trajectory coordinate. -/
def X3 (β : Fin 6 → ℝ) (t : ℝ) : ℝ := β 2 + t * β 5

/-- Time block `j` of length `q`. -/
def tblock (q : ℝ) (j : ℕ) : Set ℝ := Icc ((j : ℝ) * q) (((j : ℝ) + 1) * q)

/-- Labels with bounded coefficients satisfying the horizontal equation to
accuracy `E`. -/
def goodSet {α : Type*} (b : α → Fin 6 → ℝ) (K E : ℝ) : Set α :=
  {l | |b l 0| + |b l 1| + |b l 3| + |b l 4| ≤ K ∧ |b l 4 + b l 0| ≤ E ∧
    |b l 2| ≤ K ∧ |b l 2 + b l 5| ≤ K}

/-- The group of a label: velocity bin at width `χ`, parameter bins at width
`a`. -/
def groupSet {α : Type*} (b : α → Fin 6 → ℝ) (χ a : ℝ) (g : ℤ × ℤ × ℤ) : Set α :=
  {l | ⌊b l 3 / χ⌋ = g.1 ∧ ⌊b l 0 / a⌋ = g.2.1 ∧ ⌊b l 1 / a⌋ = g.2.2}

theorem measurableSet_goodSet {α : Type*} [MeasurableSpace α] {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (K E : ℝ) : MeasurableSet (goodSet b K E) := by
  have h0 : Measurable fun l => b l 0 := (measurable_pi_apply 0).comp hb
  have h1 : Measurable fun l => b l 1 := (measurable_pi_apply 1).comp hb
  have h2 : Measurable fun l => b l 2 := (measurable_pi_apply 2).comp hb
  have h3 : Measurable fun l => b l 3 := (measurable_pi_apply 3).comp hb
  have h4 : Measurable fun l => b l 4 := (measurable_pi_apply 4).comp hb
  have h5 : Measurable fun l => b l 5 := (measurable_pi_apply 5).comp hb
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · exact measurableSet_le
      (f := fun l => |b l 0| + |b l 1| + |b l 3| + |b l 4|) (by fun_prop) measurable_const
  · exact measurableSet_le (f := fun l => |b l 4 + b l 0|) (by fun_prop) measurable_const
  · exact measurableSet_le (f := fun l => |b l 2|) (by fun_prop) measurable_const
  · exact measurableSet_le (f := fun l => |b l 2 + b l 5|) (by fun_prop) measurable_const

theorem measurableSet_groupSet {α : Type*} [MeasurableSpace α] {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (χ a : ℝ) (g : ℤ × ℤ × ℤ) :
    MeasurableSet (groupSet b χ a g) := by
  have h0 : Measurable fun l => b l 0 := (measurable_pi_apply 0).comp hb
  have h1 : Measurable fun l => b l 1 := (measurable_pi_apply 1).comp hb
  have h3 : Measurable fun l => b l 3 := (measurable_pi_apply 3).comp hb
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact (Int.measurable_floor.comp (h3.div_const χ)) (measurableSet_singleton _)
  · exact (Int.measurable_floor.comp (h0.div_const a)) (measurableSet_singleton _)
  · exact (Int.measurable_floor.comp (h1.div_const a)) (measurableSet_singleton _)

/-- The data at one index and one depth. -/
structure DepthData (α : Type) [MeasurableSpace α] where
  ν : Measure α
  μ : Measure (α × ℝ)
  ρ : Measure (α × ℝ)
  π : Measure ℝ
  b : α → Fin 6 → ℝ
  K : ℝ
  d : ℝ
  a : ℝ
  χ : ℝ
  q : ℝ
  g : ℝ
  w : ℝ
  T : ℕ
  n : ℕ
  j : Fin n → Fin (2 ^ T)
  A : Fin n → Set α
  B : Fin n → Set α
  c : Fin n → Fin 5 → ℝ
  L : Fin n → Fin 4 → ℝ

/-- The facts of the prepared horizontal data at one index and depth. -/
structure DepthData.Hyp {α : Type} [MeasurableSpace α] (H : DepthData α) : Prop where
  hK : 1 ≤ H.K
  hd0 : 0 ≤ H.d
  hd1 : H.d < 1
  ha0 : 0 < H.a
  hχ0 : 0 < H.χ
  hχa : H.χ ≤ H.a
  haq : H.a ≤ H.q ^ 2
  hqT : H.q * 2 ^ H.T = 1
  hgq : H.g ≤ H.K * H.q
  hqg : H.q ≤ H.K * H.g
  hw0 : 0 < H.w
  hqw : H.q ^ 2 ≤ H.K ^ 2 * H.w
  hwq : H.w ≤ H.K ^ 2 * H.q ^ 2
  hb : Measurable H.b
  hν : IsProbabilityMeasure H.ν
  hπ : IsProbabilityMeasure H.π
  hμν : H.μ ≤ ENNReal.ofReal H.K • H.ν.prod volume
  hρμ : H.ρ ≤ H.μ
  hμsupp : H.μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0
  /-- The base cap at width `w` (summed over unit scalar bins). -/
  cap0 : ∀ n0 n1 n2 : ℤ, H.μ {p | ⌊p.2 / H.w⌋ = n0 ∧ ⌊X1 (H.b p.1) p.2 / H.w⌋ = n1 ∧
      ⌊X2 (H.b p.1) p.2 / H.w⌋ = n2} ≤ ENNReal.ofReal (4 * H.K ^ 2 * H.w ^ 3)
  /-- The joint cap at base width `a`, scalar width `r` and velocity width `χ`. -/
  capB : ∀ r : ℝ, H.a ≤ r → r ≤ 1 → ∀ n0 n1 n2 m v₀ : ℤ,
    H.μ {p | ⌊p.2 / H.a⌋ = n0 ∧ ⌊X1 (H.b p.1) p.2 / H.a⌋ = n1 ∧
      ⌊X2 (H.b p.1) p.2 / H.a⌋ = n2 ∧ ⌊X3 (H.b p.1) p.2 / r⌋ = m ∧
      ⌊H.b p.1 3 / H.χ⌋ = v₀} ≤
      ENNReal.ofReal (H.K * H.a ^ 3 * r ^ H.d) * H.π {x | ⌊x / H.χ⌋ = v₀}
  hA : ∀ i, MeasurableSet (H.A i)
  hB : ∀ i, MeasurableSet (H.B i)
  hBA : ∀ i, H.B i ⊆ H.A i
  hdisj : ∀ i i', i ≠ i' → H.j i = H.j i' → Disjoint (H.A i) (H.A i')
  hνA : ∀ i, ENNReal.ofReal (H.a ^ H.d * H.q ^ 2 * H.g / H.K) ≤ H.ν (H.A i)
  hμB : ∀ i, ENNReal.ofReal (H.q / H.K) * H.ν (H.A i) ≤
    H.μ (H.B i ×ˢ tblock H.q (H.j i))
  hc : ∀ i e, |H.c i e| ≤ H.K
  h1 : ∀ i, ∀ l ∈ H.A i, ∀ t ∈ tblock H.q (H.j i),
    |X1 (H.b l) t - H.c i 0 - t * H.c i 1| ≤ H.K * H.q
  h2 : ∀ i, ∀ l ∈ H.A i, ∀ t ∈ tblock H.q (H.j i),
    |X2 (H.b l) t - H.c i 2 - t * H.c i 3 - H.c i 4 * X1 (H.b l) t| ≤ H.K * H.q * H.g
  h3 : ∀ i, |H.c i 3 + H.c i 0 + (((H.j i : ℕ) : ℝ) + 1 / 2) * H.q * H.c i 1| +
    |H.c i 4 - (((H.j i : ℕ) : ℝ) + 1 / 2) * H.q| ≤ H.K * H.q
  hfit : ∀ i, ∀ l ∈ H.B i, ∀ t ∈ tblock H.q (H.j i),
    |X3 (H.b l) t - (H.L i 0 + H.L i 1 * t + H.L i 2 * X1 (H.b l) t +
      H.L i 3 * X2 (H.b l) t)| ≤ H.K * H.a
  hL3 : ∀ i, |H.L i 3| ≤ H.K * (1 + H.a / H.q ^ 2)
  hL12 : ∀ i, ∀ l ∈ H.B i, ∀ t ∈ tblock H.q (H.j i),
    |H.L i 1 - X1 (H.b l) t * H.L i 3| + |H.L i 2 + t * H.L i 3| ≤ H.K * (1 + H.a / H.q)
  hcov : H.μ {p | ¬ ∃ i, p.1 ∈ H.B i ∧ p.2 ∈ tblock H.q (H.j i)} = 0

/-- The scalar support of each group's covered incidences needs at most
`C * a^(-1-d)` squares of side `a` in the `(t, x₃)` plane (paper: "Counting
support by whole true boxes").  This is the input of scalar clustering. -/
def DepthData.SupportCount {α : Type} [MeasurableSpace α] (H : DepthData α) (C : ℝ) :
    Prop :=
  ∀ g : ℤ × ℤ × ℤ, ∃ F : Finset (ℤ × ℤ), (F.card : ℝ) ≤ C * H.a ^ (-1 - H.d) ∧
    ∀ l ∈ groupSet H.b H.χ H.a g ∩ goodSet H.b H.K H.χ, ∀ t ∈ Icc (0 : ℝ) 1,
      (∃ i, l ∈ H.B i ∧ t ∈ tblock H.q (H.j i)) →
        (⌊t / H.a⌋, ⌊X3 (H.b l) t / H.a⌋) ∈ F

end

end Submission.Obl.k4_horizontal_coefficient_count
