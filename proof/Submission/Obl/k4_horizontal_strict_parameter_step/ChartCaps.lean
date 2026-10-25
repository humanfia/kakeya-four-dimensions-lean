import Submission.Obl.k4_horizontal_strict_parameter_step.RawCharts
import Submission.Obl.k4_horizontal_strict_parameter_step.ChartMixedGeometry
import Submission.Obl.k4_horizontal_strict_parameter_step.ParameterCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.PredictorBounds

/-!
# Integrated mixed caps of one old chart

The joint caps of the original incidence law at one fine mesh, integrated over the moving
graph band of an old full-time predictor in a smaller static square (x0852's
`integrated_parameter_graph_cap`), and then divided by the original assignment mass of the
chart (the fixed conditional prior). The old floor `D² a^d π(bin)/M ≤ K ν(A)` cancels the
static area, the hidden width and the velocity palette.
-/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

/-- The joint caps of one sample at one mesh `m`, for every scalar width in `[m, 1]`, with
the original velocity palette at width `χ`. -/
def MeshCapAt {α : Type} [MeasurableSpace α] (μ : Measure (α × ℝ)) (π : Measure ℝ)
    (b : α → Fin 6 → ℝ) (d K χ m : ℝ) : Prop :=
  ∀ ω : ℝ, m ≤ ω → ω ≤ 1 → ∀ (z : Fin 3 → ℤ) (j v : ℤ),
    μ {p | baseMesh m (basePoint (b p.1) p.2) = z ∧
      ⌊(b p.1 2 + p.2 * b p.1 5) / ω⌋ = j ∧ ⌊b p.1 3 / χ⌋ = v} ≤
      ENNReal.ofReal (K * m ^ 3 * ω ^ d) * π (Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ))

/-- A point of the velocity bin `v` is within `χ` of the bin center. -/
theorem abs_sub_bin_center_le {x χ : ℝ} {v : ℤ} (hχ : 0 < χ) (hx : ⌊x / χ⌋ = v) :
    |x - ((v : ℝ) + 1 / 2) * χ| ≤ χ := by
  have h1 := Int.floor_le (x / χ)
  have h2 := Int.lt_floor_add_one (x / χ)
  rw [hx] at h1 h2
  rw [le_div_iff₀ hχ] at h1
  rw [div_lt_iff₀ hχ] at h2
  rw [abs_le]
  constructor <;> nlinarith

/-- A point of the static bin `q` lies in the closed square cell. -/
theorem mem_Icc_of_floor_eq {x D : ℝ} {q : ℤ} (hD : 0 < D) (hx : ⌊x / D⌋ = q) :
    x ∈ Icc ((q : ℝ) * D) (((q : ℝ) + 1) * D) := by
  have h1 := Int.floor_le (x / D)
  have h2 := Int.lt_floor_add_one (x / D)
  rw [hx] at h1 h2
  rw [le_div_iff₀ hD] at h1
  rw [div_lt_iff₀ hD] at h2
  exact ⟨h1, h2.le⟩

/-- The physical incidence mass of one old chart in a time bin, a smaller static square and
a scalar band of width `2 a w` about its predictor, from the mesh caps. -/
theorem chart_physical_cap {α : Type} [MeasurableSpace α] {μ : Measure (α × ℝ)}
    {π : Measure ℝ} [IsFiniteMeasure π] {b : α → Fin 6 → ℝ} {A : Set α} {qc : Fin 3 → ℤ}
    {h : Fin 6 → ℝ} {d K M χ D a ζ m τ left r w x₀ : ℝ} {y₀ : Fin 2 → ℝ}
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M) (hD : 0 < D) (hD1 : D ≤ 1)
    (ha : 0 < a) (hm : 0 < m) (hτ : 0 < τ) (hχ : 0 < χ)
    (hr : ζ ≤ r) (hr1 : r ≤ 1) (hw : ζ ≤ w) (hw1 : w ≤ 1)
    (hmτ : m ≤ τ / 2) (hmD : (K + 2) * m ≤ D * ζ) (hχD : χ ≤ D * ζ)
    (hma : m ≤ 2 * a * ζ) (ha1 : 2 * a ≤ 1)
    (hround : 2 * M * m + (6 * M / D) * (χ + (K + 2) * m) ≤ 2 * a * ζ)
    (hgood : ∀ᵐ p ∂μ, |b p.1 4 + b p.1 0| ≤ χ ∧ |b p.1 0| ≤ K ∧ |b p.1 3| ≤ K)
    (hgrid : ∀ l ∈ A, ⌊b l 3 / χ⌋ = qc 0 ∧ ⌊b l 0 / D⌋ = qc 1 ∧ ⌊b l 1 / D⌋ = qc 2)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc ((qc 1 : ℝ) * D) (((qc 1 : ℝ) + 1) * D),
      ∀ q ∈ Icc ((qc 2 : ℝ) * D) (((qc 2 : ℝ) + 1) * D), |predictor h t p q| ≤ M)
    (hcap : MeshCapAt μ π b d K χ m) :
    μ {p | p.1 ∈ A ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc left (left + τ) ∧
      |b p.1 0 - ((qc 1 : ℝ) * D + D * y₀ 0)| ≤ D * r ∧
      |b p.1 1 - ((qc 2 : ℝ) * D + D * y₀ 1)| ≤ D * r ∧
      |b p.1 2 + p.2 * b p.1 5 - (predictor h p.2 (b p.1 0) (b p.1 1) + a * x₀)| ≤
        2 * a * w} ≤
      ENNReal.ofReal (25200 * K * a ^ d * D ^ 2 * r ^ 2 * w ^ d * τ) *
        π (Ico ((qc 0 : ℝ) * χ) (((qc 0 : ℝ) + 1) * χ)) := by
  classical
  set S : Set (α × ℝ) := {p | p.1 ∈ A ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc left (left + τ) ∧
      |b p.1 0 - ((qc 1 : ℝ) * D + D * y₀ 0)| ≤ D * r ∧
      |b p.1 1 - ((qc 2 : ℝ) * D + D * y₀ 1)| ≤ D * r ∧
      |b p.1 2 + p.2 * b p.1 5 - (predictor h p.2 (b p.1 0) (b p.1 1) + a * x₀)| ≤
        2 * a * w} with hS
  set G : Set (α × ℝ) := {p | |b p.1 4 + b p.1 0| ≤ χ ∧ |b p.1 0| ≤ K ∧ |b p.1 3| ≤ K}
    with hG
  set bin : Set ℝ := Ico ((qc 0 : ℝ) * χ) (((qc 0 : ℝ) + 1) * χ) with hbin
  have hSG : μ S ≤ μ (S ∩ G) := by
    apply measure_mono_ae
    filter_upwards [hgood] with p hp hpS
    exact ⟨hpS, hp⟩
  refine hSG.trans ?_
  rcases (S ∩ G).eq_empty_or_nonempty with hempty | ⟨p₁, hp₁S, hp₁G⟩
  · rw [hempty, measure_empty]
    exact bot_le
  -- one witness bounds the moving centers
  have hζ : 0 < ζ := by
    by_contra hcon
    push Not at hcon
    have : D * ζ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD.le hcon
    linarith
  have hr0 : 0 < r := hζ.trans_le hr
  have hw0 : 0 < w := hζ.trans_le hw
  have hDr : D * ζ ≤ D * r := mul_le_mul_of_nonneg_left hr hD.le
  have hDr1 : D * r ≤ 1 := by nlinarith
  have hχ1 : χ ≤ 1 := by linarith
  have hp₁A : p₁.1 ∈ A := hp₁S.1
  obtain ⟨hv₁, -, -⟩ := hgrid p₁.1 hp₁A
  set v : ℝ := ((qc 0 : ℝ) + 1 / 2) * χ with hv
  have hb3v : |b p₁.1 3 - v| ≤ χ := abs_sub_bin_center_le hχ hv₁
  have hvK : |v| ≤ K + 1 := by
    have h3 : |b p₁.1 3| ≤ K := hp₁G.2.2
    have heq : v = b p₁.1 3 - (b p₁.1 3 - v) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  set p₀' : ℝ := (qc 1 : ℝ) * D + D * y₀ 0 with hp₀'
  set q₀' : ℝ := (qc 2 : ℝ) * D + D * y₀ 1 with hq₀'
  have hpL : |p₀'| ≤ K + 1 := by
    have h1 : |b p₁.1 0 - p₀'| ≤ D * r := hp₁S.2.2.2.1
    have h2 : |b p₁.1 0| ≤ K := hp₁G.2.1
    have heq : p₀' = b p₁.1 0 - (b p₁.1 0 - p₀') := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  set condition : α × ℝ → Prop := fun p => p.1 ∈ A ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
    |b p.1 4 + b p.1 0| ≤ χ ∧ |b p.1 0| ≤ K + 1 with hcondition_def
  have hcondition : ∀ p, condition p → p.2 ∈ Icc (0 : ℝ) 1 ∧
      |b p.1 3 - v| ≤ χ ∧ |b p.1 4 + b p.1 0| ≤ χ ∧ |b p.1 0| ≤ K + 1 ∧
      |predictorTimeSlope h (b p.1 0) (b p.1 1)| ≤ 2 * M := by
    intro p hp
    obtain ⟨hpA, hpt, hph, hp0⟩ := hp
    obtain ⟨hg3, hg0, hg1⟩ := hgrid p.1 hpA
    refine ⟨hpt, abs_sub_bin_center_le hχ hg3, hph, hp0, ?_⟩
    exact predictor_timeSlope_bound (fun t ht =>
      hnorm t ht _ (mem_Icc_of_floor_eq hD hg0) _ (mem_Icc_of_floor_eq hD hg1))
  have hgrad : ∀ τ' ∈ Icc (0 : ℝ) 1,
      |h 2 + h 3 * τ'| ≤ 2 * M / D ∧ |h 4 + h 5 * τ'| ≤ 2 * M / D := by
    intro τ' hτ'
    apply predictor_gradients (p₀ := (qc 1 : ℝ) * D) (q₀ := (qc 2 : ℝ) * D) hD
    intro p hp q hq
    apply hnorm τ' hτ' p ⟨hp.1, by linarith [hp.2]⟩ q ⟨hq.1, by linarith [hq.2]⟩
  have h2aw : 0 < 2 * a * w := by positivity
  have hm2aw : m ≤ 2 * a * w := hma.trans (by nlinarith)
  have h2aw1 : 2 * a * w ≤ 1 := by nlinarith
  set πr : ℝ := (π bin).toReal with hπr
  have hπr0 : 0 ≤ πr := ENNReal.toReal_nonneg
  have hπbin : π bin = ENNReal.ofReal πr := (ENNReal.ofReal_toReal (measure_ne_top π bin)).symm
  set C : ℝ := K * (2 * a * w) ^ d * πr with hC
  have hC0 : 0 ≤ C := by positivity
  have hcell : ∀ (z : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh m (basePoint (b p.1) p.2) = z ∧
        ⌊(b p.1 2 + p.2 * b p.1 5) / (2 * a * w)⌋ = j ∧ condition p} ≤
        ENNReal.ofReal (C * m ^ 3) := by
    intro z j
    have hsub : {p : α × ℝ | baseMesh m (basePoint (b p.1) p.2) = z ∧
        ⌊(b p.1 2 + p.2 * b p.1 5) / (2 * a * w)⌋ = j ∧ condition p} ⊆
        {p | baseMesh m (basePoint (b p.1) p.2) = z ∧
          ⌊(b p.1 2 + p.2 * b p.1 5) / (2 * a * w)⌋ = j ∧ ⌊b p.1 3 / χ⌋ = qc 0} := by
      rintro p ⟨h1, h2, hpA, -⟩
      exact ⟨h1, h2, (hgrid p.1 hpA).1⟩
    refine (measure_mono hsub).trans ((hcap (2 * a * w) hm2aw h2aw1 z j (qc 0)).trans ?_)
    rw [← hbin, hπbin, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hC]
    ring_nf
    exact le_rfl
  have hK1 : (0 : ℝ) ≤ K + 1 := by linarith
  have hmD' : m ≤ D * ζ := by nlinarith
  have hmove : (K + 1) * m ≤ D * ζ := by nlinarith
  have hcapped := integrated_parameter_graph_cap μ b h condition (δ := m) (a := 2 * a * w)
    (radius := τ / 2) (L := K + 1) (C := C) (χ := χ) (K := K + 1) (M := M) (D := D)
    hm h2aw hmτ hK1 hC0 hM hD (left + τ / 2) p₀' q₀' v (D * r) (a * x₀)
    hvK hvK hpL ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hcondition hgrad
    (by
      have : 2 * a * ζ ≤ 2 * a * w := by nlinarith
      have heq : K + 1 + 1 = K + 2 := by ring
      rw [heq]
      linarith)
    hcell
  have hsubset : S ∩ G ⊆ {p | |p.2 - (left + τ / 2)| ≤ τ / 2 ∧ |b p.1 0 - p₀'| ≤ D * r ∧
      |b p.1 1 - q₀'| ≤ D * r ∧
      |b p.1 2 + p.2 * b p.1 5 - (predictor h p.2 (b p.1 0) (b p.1 1) + a * x₀)| ≤
        2 * a * w ∧ condition p} := by
    rintro p ⟨⟨hpA, hpt, hpI, hp0, hp1, hpx⟩, hph, hpb0, -⟩
    refine ⟨?_, hp0, hp1, hpx, hpA, hpt, hph, by linarith⟩
    rw [abs_le]
    constructor <;> linarith [hpI.1, hpI.2]
  refine (measure_mono hsubset).trans (hcapped.trans ?_)
  rw [hπbin, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hpow : (2 * a * w) ^ d ≤ 2 * (a ^ d * w ^ d) := by
    rw [Real.mul_rpow (by positivity) hw0.le, Real.mul_rpow (by norm_num) ha.le]
    have h2 : (2 : ℝ) ^ d ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hd1
    have : 0 ≤ a ^ d * w ^ d := by positivity
    calc (2 : ℝ) ^ d * a ^ d * w ^ d = 2 ^ d * (a ^ d * w ^ d) := by ring
      _ ≤ 2 * (a ^ d * w ^ d) := mul_le_mul_of_nonneg_right h2 this
  have hsum1 : D * r + χ ≤ 2 * (D * r) := by linarith
  have hsum2 : 2 * (D * r) + χ ≤ 3 * (D * r) := by linarith
  have hDr0 : 0 ≤ D * r := by positivity
  have hKad : 0 ≤ K * πr := by positivity
  calc 4200 * C * (τ / 2) * (D * r + χ) * (2 * (D * r) + χ)
      = 2100 * τ * (K * πr) * (2 * a * w) ^ d * ((D * r + χ) * (2 * (D * r) + χ)) := by
        rw [hC]; ring
    _ ≤ 2100 * τ * (K * πr) * (2 * (a ^ d * w ^ d)) * ((2 * (D * r)) * (3 * (D * r))) := by
        gcongr
    _ = 25200 * K * a ^ d * D ^ 2 * r ^ 2 * w ^ d * τ * πr := by ring

/-- The integrated mixed cap of one old chart in normalized coordinates, under its fixed
conditional prior: the per-bin hypothesis of `affine_mixed_cap_from_duration`. The old floor
cancels the static area, the hidden width and the velocity palette. -/
theorem chart_bin_cap {α : Type} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {μ σ : Measure (α × ℝ)} {π : Measure ℝ} [IsFiniteMeasure π] {b : α → Fin 6 → ℝ}
    (C : RawChart α) {d K M χ D a ζ m τ left r w x₀ : ℝ} {y₀ : Fin 2 → ℝ}
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hK : 0 ≤ K) (hM : 0 < M) (hD : 0 < D) (hD1 : D ≤ 1)
    (ha : 0 < a) (hm : 0 < m) (hτ : 0 < τ) (hχ : 0 < χ)
    (hr : ζ ≤ r) (hr1 : r ≤ 1) (hw : ζ ≤ w) (hw1 : w ≤ 1)
    (hmτ : m ≤ τ / 2) (hmD : (K + 2) * m ≤ D * ζ) (hχD : χ ≤ D * ζ)
    (hma : m ≤ 2 * a * ζ) (ha1 : 2 * a ≤ 1)
    (hround : 2 * M * m + (6 * M / D) * (χ + (K + 2) * m) ≤ 2 * a * ζ)
    (hσ : σ ≤ μ) (hA : MeasurableSet C.A) (hA0 : ν C.A ≠ 0)
    (hgood : ∀ᵐ p ∂μ, |b p.1 4 + b p.1 0| ≤ χ ∧ |b p.1 0| ≤ K ∧ |b p.1 3| ≤ K)
    (hgrid : ∀ l ∈ C.A, ⌊b l 3 / χ⌋ = C.q 0 ∧ ⌊b l 0 / D⌋ = C.q 1 ∧ ⌊b l 1 / D⌋ = C.q 2)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc ((C.q 1 : ℝ) * D) (((C.q 1 : ℝ) + 1) * D),
      ∀ q ∈ Icc ((C.q 2 : ℝ) * D) (((C.q 2 : ℝ) + 1) * D), |predictor C.h t p q| ≤ M)
    (hcap : MeshCapAt μ π b d K χ m)
    (hfloor : ENNReal.ofReal (D ^ 2 * a ^ d / M) *
      π (Ico ((C.q 0 : ℝ) * χ) (((C.q 0 : ℝ) + 1) * χ)) ≤ ENNReal.ofReal K * ν C.A) :
    ((ν C.A)⁻¹ • σ.restrict (C.A ×ˢ Icc (0 : ℝ) 1))
      {p | p.2 ∈ Icc left (left + τ) ∧
        |FirstJet.xbar (C.β b a D) (C.γ b a D) p.1 p.2 - x₀| ≤ 2 * w ∧
        |C.y b a D p.1 0 - y₀ 0| ≤ r ∧ |C.y b a D p.1 1 - y₀ 1| ≤ r} ≤
      ENNReal.ofReal ((25200 * K ^ 2 * M * r ^ 2 * w ^ d) * τ) := by
  classical
  have hAI : MeasurableSet (C.A ×ˢ Icc (0 : ℝ) 1) := hA.prod measurableSet_Icc
  set T : Set (α × ℝ) := {p | p.2 ∈ Icc left (left + τ) ∧
        |FirstJet.xbar (C.β b a D) (C.γ b a D) p.1 p.2 - x₀| ≤ 2 * w ∧
        |C.y b a D p.1 0 - y₀ 0| ≤ r ∧ |C.y b a D p.1 1 - y₀ 1| ≤ r} with hT
  have hphys := chart_physical_cap (μ := μ) (π := π) (b := b) (A := C.A) (qc := C.q) (h := C.h)
    (left := left) (x₀ := x₀) (y₀ := y₀) hd hd1 hK hM.le hD hD1 ha hm hτ hχ hr hr1 hw hw1
    hmτ hmD hχD hma ha1 hround hgood hgrid hnorm hcap
  have hsub : T ∩ (C.A ×ˢ Icc (0 : ℝ) 1) ⊆ {p | p.1 ∈ C.A ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
      p.2 ∈ Icc left (left + τ) ∧
      |b p.1 0 - ((C.q 1 : ℝ) * D + D * y₀ 0)| ≤ D * r ∧
      |b p.1 1 - ((C.q 2 : ℝ) * D + D * y₀ 1)| ≤ D * r ∧
      |b p.1 2 + p.2 * b p.1 5 - (predictor C.h p.2 (b p.1 0) (b p.1 1) + a * x₀)| ≤
        2 * a * w} := by
    rintro p ⟨⟨hpI, hpx, hpy0, hpy1⟩, hpA, hpt⟩
    have hmix := chartCoordinates_mixed_test (A := C.A) (b := b) (h := C.h)
      (p₀ := (C.q 1 : ℝ) * D) (q₀ := (C.q 2 : ℝ) * D) (t := p.2) (x₀ := x₀) (r := r) (w := w)
      (y₀ := y₀) ha hD hpA hpx hpy0 hpy1
    exact ⟨hpA, hpt, hpI, hmix.1, hmix.2.1, hmix.2.2⟩
  set bin : Set ℝ := Ico ((C.q 0 : ℝ) * χ) (((C.q 0 : ℝ) + 1) * χ) with hbin
  have hAtop : ν C.A ≠ ⊤ := measure_ne_top ν C.A
  have hX : ENNReal.ofReal (25200 * K * a ^ d * D ^ 2 * r ^ 2 * w ^ d * τ) =
      ENNReal.ofReal (25200 * K * M * r ^ 2 * w ^ d * τ) *
        ENNReal.ofReal (D ^ 2 * a ^ d / M) := by
    have hr0 : 0 ≤ r := (le_trans (by
      have : 0 < D * ζ := lt_of_lt_of_le hχ hχD
      exact (pos_of_mul_pos_right this hD.le).le) hr)
    have hw0 : 0 ≤ w := (le_trans (by
      have : 0 < D * ζ := lt_of_lt_of_le hχ hχD
      exact (pos_of_mul_pos_right this hD.le).le) hw)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hAI]
  calc (ν C.A)⁻¹ * σ (T ∩ (C.A ×ˢ Icc (0 : ℝ) 1))
      ≤ (ν C.A)⁻¹ * (ENNReal.ofReal (25200 * K * a ^ d * D ^ 2 * r ^ 2 * w ^ d * τ) *
          π bin) := by
        gcongr
        exact (hσ _).trans ((measure_mono hsub).trans hphys)
    _ = (ν C.A)⁻¹ * (ENNReal.ofReal (25200 * K * M * r ^ 2 * w ^ d * τ) *
          (ENNReal.ofReal (D ^ 2 * a ^ d / M) * π bin)) := by rw [hX, mul_assoc]
    _ ≤ (ν C.A)⁻¹ * (ENNReal.ofReal (25200 * K * M * r ^ 2 * w ^ d * τ) *
          (ENNReal.ofReal K * ν C.A)) := by gcongr
    _ = ENNReal.ofReal (25200 * K * M * r ^ 2 * w ^ d * τ) * ENNReal.ofReal K *
          ((ν C.A)⁻¹ * ν C.A) := by ring
    _ = ENNReal.ofReal ((25200 * K ^ 2 * M * r ^ 2 * w ^ d) * τ) := by
        rw [ENNReal.inv_mul_cancel hA0 hAtop, mul_one, ← ENNReal.ofReal_mul (by
          have hr0 : 0 ≤ r := (le_trans (by
            have : 0 < D * ζ := lt_of_lt_of_le hχ hχD
            exact (pos_of_mul_pos_right this hD.le).le) hr)
          have hw0 : 0 ≤ w := (le_trans (by
            have : 0 < D * ζ := lt_of_lt_of_le hχ hχD
            exact (pos_of_mul_pos_right this hD.le).le) hw)
          positivity)]
        congr 1
        ring

end

end Submission.Obl.k4_horizontal_strict_parameter_step
