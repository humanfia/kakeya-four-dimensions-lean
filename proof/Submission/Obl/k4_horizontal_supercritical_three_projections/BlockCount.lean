import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartDefs
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.CellGeometry
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.PredictorCells
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Boxes
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Mass

/-!
# Counting the true labels that meet one scalar cell

All true blocks at one depth meeting a scalar cell of a chart lie in one
common enlarged horizontal box (`horizontal_box_from_contact`). Their whole
assignment floors are disjoint within a time block, and the fine original
cube caps bound the mass of the box (`horizontal_box_joint_bound`). Hence
at most `C K^17 a^(-d)` true labels meet a cell (paper, Proposition 9.7,
"The common box bounds the number of contributing true labels").
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Parent
open scoped ENNReal

noncomputable section

/-- The true blocks at one depth and one index `k`, with exactly the estimates
of the frozen cover hypothesis that the support count uses. -/
structure BlockHyp {α : Type*} [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) (K a q g d : ℝ) (T n : ℕ) (j : Fin n → Fin (2 ^ T))
    (A B : Fin n → Set α) (c : Fin n → Fin 5 → ℝ) (L : Fin n → Fin 4 → ℝ) : Prop where
  q_eq : q = (2 : ℝ) ^ (-(T : ℤ))
  meas : ∀ i, MeasurableSet (A i) ∧ MeasurableSet (B i) ∧ B i ⊆ A i
  disj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')
  floor_ν : ∀ i, ENNReal.ofReal (a ^ d * q ^ 2 * g / K) ≤ ν (A i)
  floor_μ : ∀ i, ENNReal.ofReal (q / K) * ν (A i) ≤ μ (B i ×ˢ blockTime T (j i))
  coeff : ∀ i e, |c i e| ≤ K
  box : ∀ i, ∀ l ∈ A i, ∀ t ∈ blockTime T (j i),
    |(b l 0 + t * b l 3) - c i 0 - t * c i 1| ≤ K * q ∧
    |(b l 1 + t * b l 4) - c i 2 - t * c i 3 - c i 4 * (b l 0 + t * b l 3)| ≤ K * q * g
  fit : ∀ i, ∀ l ∈ B i, ∀ t ∈ blockTime T (j i),
    |(b l 2 + t * b l 5) -
      affineValue (L i) t (b l 0 + t * b l 3) (b l 1 + t * b l 4)| ≤ K * a
  horizontal : ∀ i, |c i 3 + c i 0 + ((j i : ℕ) + (1 : ℝ) / 2) * q * c i 1| +
    |c i 4 - ((j i : ℕ) + (1 : ℝ) / 2) * q| ≤ K * q
  slope₃ : ∀ i, |L i 3| ≤ K * (1 + a / q ^ 2)
  slope : ∀ i, ∀ l ∈ B i, ∀ t ∈ blockTime T (j i),
    |L i 1 - (b l 0 + t * b l 3) * L i 3| + |L i 2 + t * L i 3| ≤ K * (1 + a / q)

/-- The frozen block `I T j` in terms of the block length. -/
theorem blockTime_eq {T : ℕ} {q : ℝ} (hq : q = (2 : ℝ) ^ (-(T : ℤ))) (j : ℕ) :
    blockTime T j = Icc ((j : ℝ) * q) (((j : ℝ) + 1) * q) := by
  have h2 : (2 : ℝ) ^ (-(T : ℤ)) = 1 / (2 : ℝ) ^ T := by
    rw [zpow_neg, zpow_natCast, one_div]
  rw [hq, h2, blockTime]
  congr 1 <;> ring

theorem blockTime_bounds {T : ℕ} {q : ℝ} (hq : q = (2 : ℝ) ^ (-(T : ℤ))) {j : ℕ}
    {t : ℝ} (ht : t ∈ blockTime T j) :
    (j : ℝ) * q ≤ t ∧ t ≤ ((j : ℝ) + 1) * q := by
  rw [blockTime_eq hq] at ht
  exact ht

/-- Two times of one block are `q`-close, and so is its midpoint. -/
theorem blockTime_close {T : ℕ} {q : ℝ} (hq : q = (2 : ℝ) ^ (-(T : ℤ))) {j : ℕ}
    {t t' : ℝ} (ht : t ∈ blockTime T j) (ht' : t' ∈ blockTime T j) :
    |t - t'| ≤ q ∧ |((j : ℝ) + 1 / 2) * q - t'| ≤ q / 2 := by
  obtain ⟨h₀, h₁⟩ := blockTime_bounds hq ht
  obtain ⟨h₀', h₁'⟩ := blockTime_bounds hq ht'
  constructor
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

end

end Submission.Obl.k4_horizontal_supercritical_three_projections

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Parent
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- A chart incidence in the scalar cell `z` sits at the cell corner up to `σ`. -/
theorem chartCell_corner {b : Fin 6 → ℝ} {D σ t : ℝ} {P Q : ℤ} {z : Fin 2 → ℤ}
    (hσ : 0 < σ) (hz : chartCell D σ P Q b t = z) :
    (z 0 : ℝ) * σ ≤ t ∧ t < ((z 0 : ℝ) + 1) * σ ∧
      (z 1 : ℝ) * σ ≤ scalarParameter t ((b 0 - P * D) / D) ((b 1 - Q * D) / D) ∧
      scalarParameter t ((b 0 - P * D) / D) ((b 1 - Q * D) / D) < ((z 1 : ℝ) + 1) * σ := by
  have h0 : ⌊t / σ⌋ = z 0 := by rw [← hz]; rfl
  have h1 : ⌊scalarParameter t ((b 0 - P * D) / D) ((b 1 - Q * D) / D) / σ⌋ = z 1 := by
    rw [← hz]; rfl
  obtain ⟨a₀, a₁⟩ := floor_cell_mem (x := t) hσ
  obtain ⟨b₀, b₁⟩ := floor_cell_mem
    (x := scalarParameter t ((b 0 - P * D) / D) ((b 1 - Q * D) / D)) hσ
  rw [h0] at a₀ a₁
  rw [h1] at b₀ b₁
  exact ⟨a₀, a₁, b₀, b₁⟩

/-- Every true block meeting a scalar cell lies, with its whole domain, in one
common enlarged horizontal box around the cell (paper, Proposition 9.7).
The reference motion of the cell is `Z = pc + t v`, `Y = r - t pc` with tilt `τ`. -/
theorem block_in_common_box {ν : Measure α} {μ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ}
    {K a q g d D χ ζ σ : ℝ} {T n : ℕ} {j : Fin n → Fin (2 ^ T)}
    {A B : Fin n → Set α} {c : Fin n → Fin 5 → ℝ} {L : Fin n → Fin 4 → ℝ}
    (H : BlockHyp ν μ b K a q g d T n j A B c L)
    (hK : 1 ≤ K) (hq : 0 < q) (hD : 0 < D) (hχ : 0 < χ) (hσ : 0 < σ)
    (hgq : g ≤ K * q) (hσq : σ ≤ q / 2) (hDq : D ≤ q / 8) (hχD : χ ≤ D)
    (hsmall : 2 * D * σ + ζ + χ ≤ q ^ 2 / 2)
    {P Q β : ℤ} {z : Fin 2 → ℤ} {τ r pc v : ℝ}
    (hτ : τ = (z 0 : ℝ) * σ) (hr : r = (Q : ℝ) * D + D * ((z 1 : ℝ) * σ))
    (hpc : pc = (P : ℝ) * D) (hv : v = (β : ℝ) * χ) (i : Fin n)
    {l₀ : α} {t₀ : ℝ} (hl₀ : l₀ ∈ B i) (hc₀ : l₀ ∈ chartSet b K ζ D χ P Q β)
    (ht₀ : t₀ ∈ blockTime T (j i)) (ht₀' : t₀ ∈ Icc (0 : ℝ) 1)
    (hz : chartCell D σ P Q (b l₀) t₀ = z)
    {l : α} {t : ℝ} (hl : l ∈ A i) (ht : t ∈ blockTime T (j i)) :
    |t - τ| ≤ 2 * q ∧
      |(b l 0 + t * b l 3) - (pc + t * v)| ≤ 5 * (2 * K ^ 2) ^ 2 * (2 * q) ∧
      |(b l 1 + t * b l 4) - (r - t * pc) - τ * ((b l 0 + t * b l 3) - (pc + t * v))| ≤
        5 * (2 * K ^ 2) ^ 2 * (2 * q) ^ 2 := by
  obtain ⟨K₃, hK₃def⟩ : ∃ K₃ : ℝ, K₃ = 2 * K ^ 2 := ⟨_, rfl⟩
  rw [← hK₃def]
  obtain ⟨τb, hτbdef⟩ : ∃ τb : ℝ, τb = ((j i : ℕ) + (1 : ℝ) / 2) * q := ⟨_, rfl⟩
  have hK₀ : 0 ≤ K := by linarith
  have hK₃ : 2 ≤ K₃ := by rw [hK₃def]; nlinarith
  have hK₃K : K ≤ K₃ := by rw [hK₃def]; nlinarith
  have hK₃K2 : K ^ 2 ≤ K₃ := by rw [hK₃def]; nlinarith
  have hK₃sq : K₃ ≤ K₃ ^ 2 := by nlinarith
  -- the contact lies in the cell
  obtain ⟨hτ₀, hτ₁, hR₀, hR₁⟩ := chartCell_corner hσ hz
  have hτ₀' : τ ≤ t₀ := by rw [hτ]; exact hτ₀
  have hτ₁' : t₀ < τ + σ := by rw [hτ]; linarith
  obtain ⟨-, -, -, -, hp, hvb, -, hv', -, -, he⟩ := chartSet_bounds hD hχ hc₀
  rw [← hpc] at hp
  rw [← hv] at hvb hv'
  have hτmem : τ ∈ Icc (0 : ℝ) 1 := by
    have hz0 : (0 : ℤ) ≤ z 0 := by
      have h0 : ⌊t₀ / σ⌋ = z 0 := by rw [← hz]; rfl
      rw [← h0]
      exact Int.floor_nonneg.mpr (div_nonneg ht₀'.1 hσ.le)
    have : (0 : ℝ) ≤ (z 0 : ℝ) := by exact_mod_cast hz0
    exact ⟨hτ ▸ mul_nonneg this hσ.le, le_trans hτ₀' ht₀'.2⟩
  have htτ : |t₀ - τ| ≤ σ := by rw [abs_le]; constructor <;> linarith
  have hRr : |scalarParameter t₀ ((b l₀ 0 - pc) / D) ((b l₀ 1 - Q * D) / D) -
      (z 1 : ℝ) * σ| ≤ σ := by
    rw [hpc]; rw [abs_le]; constructor <;> linarith
  have hcell := scalar_cell_physical_box (b l₀) (pc := pc) (qc := (Q : ℝ) * D) (pa := pc)
    (r₀ := (z 1 : ℝ) * σ) (v := v) (β := 1) hD ht₀' hτmem htτ (by simpa using hp) hvb he hRr
  obtain ⟨hcZ, hcY⟩ := hcell
  have hrw : (Q : ℝ) * D + D * ((z 1 : ℝ) * σ) - t₀ * (2 * pc - pc) = r - t₀ * pc := by
    rw [hr]; ring
  rw [hrw, mul_one] at hcY
  rw [mul_one] at hcZ
  -- block geometry
  obtain ⟨hclose, -⟩ := blockTime_close H.q_eq ht ht₀
  obtain ⟨-, hmid'⟩ := blockTime_close H.q_eq ht₀ ht₀
  rw [← hτbdef] at hmid'
  have hτbτ : |τb - τ| ≤ q := by
    have h1 : |τb - τ| ≤ |τb - t₀| + |t₀ - τ| := abs_sub_le _ _ _
    linarith
  have hhor := H.horizontal i
  rw [← hτbdef] at hhor
  have hKq : K * q ≤ K₃ * q := mul_le_mul_of_nonneg_right hK₃K hq.le
  have halign : |c i 3 + c i 0 + τb * c i 1| ≤ K₃ * q :=
    ((le_add_of_nonneg_right (abs_nonneg _)).trans hhor).trans hKq
  have htilt : |c i 4 - τb| ≤ K₃ * q :=
    ((le_add_of_nonneg_left (abs_nonneg _)).trans hhor).trans hKq
  have hboxY (l' : α) (hl' : l' ∈ A i) (t' : ℝ) (ht' : t' ∈ blockTime T (j i)) :
      |(b l' 1 + t' * b l' 4) - c i 2 - t' * c i 3 - c i 4 * (b l' 0 + t' * b l' 3)| ≤
        K₃ * q ^ 2 := by
    have h := (H.box i l' hl' t' ht').2
    have h2 : K * q * g ≤ K₃ * q ^ 2 :=
      calc K * q * g ≤ K * q * (K * q) := mul_le_mul_of_nonneg_left hgq (mul_nonneg hK₀ hq.le)
        _ = K ^ 2 * q ^ 2 := by ring
        _ ≤ K₃ * q ^ 2 := mul_le_mul_of_nonneg_right hK₃K2 (sq_nonneg q)
    exact h.trans h2
  have hboxZ (l' : α) (hl' : l' ∈ A i) (t' : ℝ) (ht' : t' ∈ blockTime T (j i)) :
      |(b l' 0 + t' * b l' 3) - c i 0 - t' * c i 1| ≤ K₃ * q :=
    (H.box i l' hl' t' ht').1.trans hKq
  have hl₀A : l₀ ∈ A i := (H.meas i).2.2 hl₀
  have hqK₃ : q ≤ K₃ * q := le_mul_of_one_le_left hq.le (by linarith)
  have hq2K₃ : q ^ 2 ≤ K₃ * q ^ 2 := le_mul_of_one_le_left (sq_nonneg q) (by linarith)
  have hcontactZ : |(b l₀ 0 + t₀ * b l₀ 3) - (pc + t₀ * v)| ≤ K₃ * q := by
    linarith
  have hcontactY : |(b l₀ 1 + t₀ * b l₀ 4) - (r - t₀ * pc) -
      τb * ((b l₀ 0 + t₀ * b l₀ 3) - (pc + t₀ * v))| ≤ K₃ * q ^ 2 := by
    obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = (b l₀ 1 + t₀ * b l₀ 4) - (r - t₀ * pc) -
        τ * ((b l₀ 0 + t₀ * b l₀ 3) - (pc + t₀ * v)) := ⟨_, rfl⟩
    obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : ℝ, Z₀ = (b l₀ 0 + t₀ * b l₀ 3) - (pc + t₀ * v) := ⟨_, rfl⟩
    have heq : (b l₀ 1 + t₀ * b l₀ 4) - (r - t₀ * pc) -
        τb * ((b l₀ 0 + t₀ * b l₀ 3) - (pc + t₀ * v)) = E₀ - (τb - τ) * Z₀ := by
      rw [hE₀, hZ₀]; ring
    rw [heq]
    rw [← hE₀] at hcY
    rw [← hZ₀] at hcZ
    have h1 := abs_sub E₀ ((τb - τ) * Z₀)
    have h2 : |(τb - τ) * Z₀| ≤ q * (D + χ) := by
      rw [abs_mul]; exact mul_le_mul hτbτ hcZ (abs_nonneg _) hq.le
    have h3 : q * (D + χ) ≤ q ^ 2 / 4 := by
      have : D + χ ≤ q / 4 := by linarith
      calc q * (D + χ) ≤ q * (q / 4) := mul_le_mul_of_nonneg_left this hq.le
        _ = q ^ 2 / 4 := by ring
    have h4 : D * σ + σ * D = 2 * D * σ := by ring
    have h5 := sq_nonneg q
    linarith
  have hq1 : q ≤ 1 := by
    rw [H.q_eq]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
  have hKv : K + χ ≤ K₃ := by
    have : K + 1 ≤ K₃ := by rw [hK₃def]; nlinarith
    linarith
  obtain ⟨hZout, hYout⟩ := horizontal_box_from_contact (c i) pc r v τb t t₀
    (b l 0 + t * b l 3) (b l 1 + t * b l 4) (b l₀ 0 + t₀ * b l₀ 3) (b l₀ 1 + t₀ * b l₀ 4)
    K₃ q (by linarith) hq.le ((H.coeff i 1).trans hK₃K) (hv'.trans hKv)
    halign htilt hclose (by linarith [hmid'])
    (hboxZ l hl t ht) (hboxY l hl t ht) (hboxZ l₀ hl₀A t₀ ht₀) (hboxY l₀ hl₀A t₀ ht₀)
    hcontactZ hcontactY
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = (b l 0 + t * b l 3) - (pc + t * v) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (b l 1 + t * b l 4) - (r - t * pc) - τb * Z := ⟨_, rfl⟩
  rw [← hZ] at hZout ⊢
  rw [← hZ, ← hE] at hYout
  refine ⟨?_, ?_, ?_⟩
  · have := abs_sub_le t t₀ τ
    linarith
  · have h1 : 5 * K₃ * q ≤ 5 * K₃ ^ 2 * (2 * q) := by
      have h5 : 5 * K₃ * q ≤ 5 * K₃ ^ 2 * q :=
        mul_le_mul_of_nonneg_right (by linarith) hq.le
      have h6 : 5 * K₃ ^ 2 * q ≤ 5 * K₃ ^ 2 * (2 * q) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      exact h5.trans h6
    linarith
  · have heq : (b l 1 + t * b l 4) - (r - t * pc) - τ * Z = E + (τb - τ) * Z := by
      rw [hE]; ring
    rw [heq]
    have h1 := abs_add_le E ((τb - τ) * Z)
    have h2 : |(τb - τ) * Z| ≤ q * (5 * K₃ * q) := by
      rw [abs_mul]; exact mul_le_mul hτbτ hZout (abs_nonneg _) hq.le
    have h3 : q * (5 * K₃ * q) ≤ 5 * K₃ ^ 2 * q ^ 2 := by
      have hq2 := sq_nonneg q
      calc q * (5 * K₃ * q) = 5 * K₃ * q ^ 2 := by ring
        _ ≤ 5 * K₃ ^ 2 * q ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hq2
    have h4 : 12 * K₃ ^ 2 * q ^ 2 + 5 * K₃ ^ 2 * q ^ 2 ≤ 5 * K₃ ^ 2 * (2 * q) ^ 2 := by
      have h7 := mul_nonneg (sq_nonneg K₃) (sq_nonneg q)
      have h8 : 5 * K₃ ^ 2 * (2 * q) ^ 2 = 20 * (K₃ ^ 2 * q ^ 2) := by ring
      have h9 : 12 * K₃ ^ 2 * q ^ 2 + 5 * K₃ ^ 2 * q ^ 2 = 17 * (K₃ ^ 2 * q ^ 2) := by ring
      rw [h8, h9]
      linarith
    linarith

/-- The true labels meeting the scalar cell `z` of the chart `(P, Q, β)`. -/
def cellLabels (b : α → Fin 6 → ℝ) (K ζ D χ σ : ℝ) (P Q β : ℤ) {T n : ℕ}
    (j : Fin n → Fin (2 ^ T)) (B : Fin n → Set α) (z : Fin 2 → ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ p : α × ℝ, p.1 ∈ B i ∧
    p.1 ∈ chartSet b K ζ D χ P Q β ∧ p.2 ∈ blockTime T (j i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
    chartCell D σ P Q (b p.1) p.2 = z)

theorem mem_cellLabels {b : α → Fin 6 → ℝ} {K ζ D χ σ : ℝ} {P Q β : ℤ} {T n : ℕ}
    {j : Fin n → Fin (2 ^ T)} {B : Fin n → Set α} {z : Fin 2 → ℤ} {i : Fin n} :
    i ∈ cellLabels b K ζ D χ σ P Q β j B z ↔ ∃ p : α × ℝ, p.1 ∈ B i ∧
      p.1 ∈ chartSet b K ζ D χ P Q β ∧ p.2 ∈ blockTime T (j i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
      chartCell D σ P Q (b p.1) p.2 = z := by
  classical
  simp [cellLabels]

/-- The labels meeting one cell use at most three time blocks. -/
theorem card_image_cellLabels_le {b : α → Fin 6 → ℝ} {K ζ D χ σ q : ℝ} {P Q β : ℤ} {T n : ℕ}
    {j : Fin n → Fin (2 ^ T)} {B : Fin n → Set α} {z : Fin 2 → ℤ}
    (hq : q = (2 : ℝ) ^ (-(T : ℤ))) (hσ : 0 < σ) (hσq : σ ≤ q / 2) :
    ((cellLabels b K ζ D χ σ P Q β j B z).image j).card ≤ 3 := by
  classical
  have hq0 : 0 < q := by rw [hq]; positivity
  set m₀ : ℤ := ⌊((z 0 : ℝ) * σ) / q⌋
  have hmaps : Set.MapsTo (fun x : Fin (2 ^ T) => ((x : ℕ) : ℤ))
      ((cellLabels b K ζ D χ σ P Q β j B z).image j : Set (Fin (2 ^ T)))
      (Finset.Icc (m₀ - 1) (m₀ + 1) : Set ℤ) := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨p, -, -, hpI, -, hz⟩ := mem_cellLabels.mp hi
    obtain ⟨hτ₀, hτ₁, -, -⟩ := chartCell_corner hσ hz
    obtain ⟨hI₀, hI₁⟩ := blockTime_bounds hq hpI
    have hm₀ := floor_cell_mem (x := (z 0 : ℝ) * σ) hq0
    have hlow : ((j i : ℕ) : ℝ) + 1 > ((m₀ : ℤ) : ℝ) - 1 := by
      have : ((z 0 : ℝ) * σ) / q * q = (z 0 : ℝ) * σ := by field_simp
      nlinarith
    have hhigh : ((j i : ℕ) : ℝ) < ((m₀ : ℤ) : ℝ) + 2 := by
      nlinarith
    simp only [Finset.coe_Icc, Set.mem_Icc]
    constructor
    · have : ((m₀ : ℤ) : ℝ) - 1 < ((j i : ℕ) : ℝ) + 1 := hlow
      have h' : m₀ - 1 < ((j i : ℕ) : ℤ) + 1 := by exact_mod_cast this
      omega
    · have h' : ((j i : ℕ) : ℤ) < m₀ + 2 := by exact_mod_cast hhigh
      omega
  have hinj : Set.InjOn (fun x : Fin (2 ^ T) => ((x : ℕ) : ℤ))
      ((cellLabels b K ζ D χ σ P Q β j B z).image j : Set (Fin (2 ^ T))) := by
    intro x _ y _ hxy
    simp only [Nat.cast_inj] at hxy
    exact Fin.ext hxy
  have h := Finset.card_le_card_of_injOn _ hmaps hinj
  have hc : (Finset.Icc (m₀ - 1) (m₀ + 1)).card = 3 := by
    rw [Int.card_Icc]; omega
  omega

/-- At most `3·10⁹ K¹⁷ a^(-d)` true labels meet one scalar cell of a chart.
Their whole domains lie in one common box, whose mass the fine original cube
caps bound by `K q⁴`, while each whole assignment has mass `≥ a^d q³ g / K²`. -/
theorem card_cellLabels_le {ν : Measure α} {μ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {K a q g d D χ ζ σ δc : ℝ} {T n : ℕ} {j : Fin n → Fin (2 ^ T)}
    {A B : Fin n → Set α} {c : Fin n → Fin 5 → ℝ} {L : Fin n → Fin 4 → ℝ}
    (H : BlockHyp ν μ b K a q g d T n j A B c L)
    (hK : 1 ≤ K) (ha : 0 < a) (hq : 0 < q) (hg : 0 < g) (hD : 0 < D) (hχ : 0 < χ)
    (hσ : 0 < σ) (hδc : 0 < δc)
    (hgq : g ≤ K * q) (hqg : q ≤ K * g) (hq1 : q ≤ 1 / 2) (hδcq : δc ≤ q ^ 2)
    (hσq : σ ≤ q / 2) (hDq : D ≤ q / 8) (hχD : χ ≤ D)
    (hsmall : 2 * D * σ + ζ + χ ≤ q ^ 2 / 2)
    (hx3 : ∀ᵐ p ∂μ, |b p.1 2 + p.2 * b p.1 5| ≤ K)
    (hcap : ∀ (w : Fin 3 → ℤ) (j' : ℤ), μ {p | (fun e => ⌊(![p.2, b p.1 0 + p.2 * b p.1 3,
        b p.1 1 + p.2 * b p.1 4] : Fin 3 → ℝ) e / δc⌋) = w ∧
        ⌊b p.1 2 + p.2 * b p.1 5⌋ = j'} ≤ ENNReal.ofReal (K * δc ^ 3))
    (P Q β : ℤ) (z : Fin 2 → ℤ) :
    ((cellLabels b K ζ D χ σ P Q β j B z).card : ℝ) ≤ 3 * 10 ^ 9 * K ^ 17 * a ^ (-d) := by
  classical
  set S := cellLabels b K ζ D χ σ P Q β j B z with hSdef
  rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
  · rw [hS, Finset.card_empty, Nat.cast_zero]; positivity
  -- bounds on the reference motion, from one witness
  obtain ⟨p₀, -, hc₀, -, ht₀', hz₀⟩ := mem_cellLabels.mp hi₀
  obtain ⟨-, -, -, -, -, -, hP, hβ, -, -, -⟩ := chartSet_bounds hD hχ hc₀
  obtain ⟨hτ₀, hτ₁, -, -⟩ := chartCell_corner hσ hz₀
  have hK₀ : 0 ≤ K := by linarith
  obtain ⟨Hb, hHb⟩ : ∃ Hb : ℝ, Hb = 5 * (2 * K ^ 2) ^ 2 := ⟨_, rfl⟩
  have hHbK : Hb = 20 * K ^ 4 := by rw [hHb]; ring
  have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hKK4 : K ≤ K ^ 4 := by
    calc K = K * 1 := by ring
      _ ≤ K * K ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hK) hK₀
      _ = K ^ 4 := by ring
  have hHb1 : 1 ≤ Hb := by rw [hHbK]; linarith
  have hq1' : q ≤ 1 := by linarith
  have hD1 : D ≤ 1 := by linarith
  have hχ1 : χ ≤ 1 := by linarith
  have hpcH : |(P : ℝ) * D| ≤ Hb := by rw [hHbK]; linarith
  have hvH : |(β : ℝ) * χ| ≤ Hb := by rw [hHbK]; linarith
  have hτH : |(z 0 : ℝ) * σ| ≤ Hb := by
    have hz0 : (0 : ℤ) ≤ z 0 := by
      have h0 : ⌊p₀.2 / σ⌋ = z 0 := by rw [← hz₀]; rfl
      rw [← h0]
      exact Int.floor_nonneg.mpr (div_nonneg ht₀'.1 hσ.le)
    have : (0 : ℝ) ≤ (z 0 : ℝ) := by exact_mod_cast hz0
    rw [abs_of_nonneg (mul_nonneg this hσ.le)]
    linarith [ht₀'.2]
  -- the common box
  set τ := (z 0 : ℝ) * σ with hτ
  set r := (Q : ℝ) * D + D * ((z 1 : ℝ) * σ) with hr
  set pc := (P : ℝ) * D with hpc
  set v := (β : ℝ) * χ with hv
  set E : Set (α × ℝ) := {p | |p.2 - τ| ≤ 2 * q ∧
    |(b p.1 0 + p.2 * b p.1 3) - (pc + p.2 * v)| ≤ Hb * (2 * q) ∧
    |(b p.1 1 + p.2 * b p.1 4) - (r - p.2 * pc) - τ * ((b p.1 0 + p.2 * b p.1 3) -
      (pc + p.2 * v))| ≤ Hb * (2 * q) ^ 2 ∧ |b p.1 2 + p.2 * b p.1 5| ≤ K} with hE
  set W : Fin n → Set (α × ℝ) := fun i =>
    (B i ×ˢ blockTime T (j i)) ∩ {p | |b p.1 2 + p.2 * b p.1 5| ≤ K} with hW
  have hmeasX : MeasurableSet {p : α × ℝ | |b p.1 2 + p.2 * b p.1 5| ≤ K} := by
    apply measurableSet_le _ measurable_const
    have h2 : Measurable fun p : α × ℝ => b p.1 2 :=
      (measurable_pi_apply 2).comp (hb.comp measurable_fst)
    have h5 : Measurable fun p : α × ℝ => b p.1 5 :=
      (measurable_pi_apply 5).comp (hb.comp measurable_fst)
    exact (h2.add (measurable_snd.mul h5)).abs
  have hWmeas : ∀ i ∈ S, MeasurableSet (W i) := by
    intro i _
    exact ((H.meas i).2.1.prod measurableSet_Icc).inter hmeasX
  have hWdisj : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → j i = j i' → Disjoint (W i) (W i') := by
    intro i _ i' _ hii' hjj
    have hA := H.disj i i' hii' hjj
    refine Set.disjoint_left.mpr ?_
    intro p hp hp'
    exact Set.disjoint_left.mp hA ((H.meas i).2.2 hp.1.1) ((H.meas i').2.2 hp'.1.1)
  have hWsub : ∀ i ∈ S, W i ⊆ E := by
    intro i hi p hp
    obtain ⟨⟨hpB, hpI⟩, hpX⟩ := hp
    obtain ⟨w, hwB, hwc, hwI, hw01, hwz⟩ := mem_cellLabels.mp hi
    obtain ⟨h1, h2, h3⟩ := block_in_common_box H hK hq hD hχ hσ hgq hσq hDq hχD hsmall
      hτ hr hpc hv i hwB hwc hwI hw01 hwz ((H.meas i).2.2 hpB) hpI
    exact ⟨h1, by rw [hHb]; exact h2, by rw [hHb]; exact h3, hpX⟩
  have hfloor : ∀ i ∈ S, ENNReal.ofReal (a ^ d * q ^ 3 * g / K ^ 2) ≤ μ (W i) := by
    intro i _
    have hnull : μ {p : α × ℝ | |b p.1 2 + p.2 * b p.1 5| ≤ K}ᶜ = 0 := by
      rw [ae_iff] at hx3
      simpa [Set.compl_ofPred] using hx3
    rw [hW, measure_inter_conull hnull]
    refine le_trans ?_ (H.floor_μ i)
    calc ENNReal.ofReal (a ^ d * q ^ 3 * g / K ^ 2)
        = ENNReal.ofReal (q / K) * ENNReal.ofReal (a ^ d * q ^ 2 * g / K) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
      _ ≤ ENNReal.ofReal (q / K) * ν (A i) := mul_le_mul' le_rfl (H.floor_ν i)
  have hcapE : μ E ≤ ENNReal.ofReal (819 * Hb ^ 3 * (2 * q) ^ 4 * (2 * K + 5) * K) := by
    have h := horizontal_box_joint_bound μ
      (fun p : α × ℝ => ![p.2, b p.1 0 + p.2 * b p.1 3, b p.1 1 + p.2 * b p.1 4])
      (fun p : α × ℝ => b p.1 2 + p.2 * b p.1 5) E (δ := δc) (q := 2 * q) (H := Hb) (X := K)
      (C := K) hδc (by linarith) (by linarith) (by nlinarith) hHb1 hK₀ hK₀ τ pc r v τ
      hpcH hvH hτH ?_ 1 ?_
    · simpa using h
    · intro p hp
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      exact hp
    · intro w j'
      simpa using hcap w j'
  have hcount := whole_witness_count μ S j W E (m := a ^ d * q ^ 3 * g / K ^ 2)
    (V := 819 * Hb ^ 3 * (2 * q) ^ 4 * (2 * K + 5) * K) (by positivity) (by positivity)
    hWmeas hWdisj hWsub hfloor hcapE
  have himage : (((S.image j).card : ℕ) : ℝ) ≤ 3 := by
    exact_mod_cast card_image_cellLabels_le H.q_eq hσ hσq
  -- arithmetic
  have hA : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have hm : 0 < a ^ d * q ^ 3 * g / K ^ 2 := by positivity
  have hV : 0 ≤ 819 * Hb ^ 3 * (2 * q) ^ 4 * (2 * K + 5) * K := by positivity
  have h3V : (S.card : ℝ) * (a ^ d * q ^ 3 * g / K ^ 2) ≤
      3 * (819 * Hb ^ 3 * (2 * q) ^ 4 * (2 * K + 5) * K) :=
    hcount.trans (mul_le_mul_of_nonneg_right himage hV)
  have hcard : (S.card : ℝ) ≤ 3 * (819 * Hb ^ 3 * (2 * q) ^ 4 * (2 * K + 5) * K) /
      (a ^ d * q ^ 3 * g / K ^ 2) := (le_div_iff₀ hm).mpr h3V
  have hneg : a ^ (-d) = (a ^ d)⁻¹ := Real.rpow_neg ha.le d
  rw [hneg]
  refine hcard.trans ?_
  rw [div_le_iff₀ hm, hHbK]
  have hK5 : 2 * K + 5 ≤ 7 * K := by linarith
  have hqg' : q * (a ^ d)⁻¹ * (a ^ d) = q := by field_simp
  have key : 3 * (819 * (20 * K ^ 4) ^ 3 * (2 * q) ^ 4 * (2 * K + 5) * K) ≤
      3 * 10 ^ 9 * K ^ 17 * (a ^ d)⁻¹ * (a ^ d * q ^ 3 * g / K ^ 2) := by
    have e1 : 3 * 10 ^ 9 * K ^ 17 * (a ^ d)⁻¹ * (a ^ d * q ^ 3 * g / K ^ 2) =
        3 * 10 ^ 9 * K ^ 15 * q ^ 3 * g := by
      field_simp
    rw [e1]
    have e2 : 3 * (819 * (20 * K ^ 4) ^ 3 * (2 * q) ^ 4 * (2 * K + 5) * K) =
        (3 * 819 * 8000 * 16) * K ^ 13 * q ^ 3 * (2 * K + 5) * q := by ring
    rw [e2]
    have hq3 : 0 ≤ q ^ 3 := by positivity
    have hK13 : 0 ≤ K ^ 13 := by positivity
    calc (3 * 819 * 8000 * 16 : ℝ) * K ^ 13 * q ^ 3 * (2 * K + 5) * q
        ≤ (3 * 819 * 8000 * 16 : ℝ) * K ^ 13 * q ^ 3 * (7 * K) * (K * g) := by
          gcongr
      _ = (3 * 819 * 8000 * 16 * 7 : ℝ) * (K ^ 15 * q ^ 3 * g) := by ring
      _ ≤ (3 * 10 ^ 9) * (K ^ 15 * q ^ 3 * g) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 3 * 10 ^ 9 * K ^ 15 * q ^ 3 * g := by ring
  linarith

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
