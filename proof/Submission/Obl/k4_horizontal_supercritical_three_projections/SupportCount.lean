import Submission.Obl.k4_horizontal_supercritical_three_projections.BlockCount

/-!
# The terminal support count of a chart (one index `k`)

Inside a chart, a.e. incidence lies in a true block; on its scalar cell the
block's affine predictor, collapsed along the discarded parameter direction,
fixes the hidden coordinate to `5K'a`. Hence each cell carries at most
`3·10⁹K¹⁷a^(-d)` labels times `15K²` hidden bins, and the support of
`(cell, ⌊x/a⌋)` has at most `10¹² K²⁰ σ⁻² a^(-d)` elements: this is the
finite-support hypothesis of the scalar mesh projection
(paper, Proposition 9.7, "Each of at most `Kσ_R^{-2}` cells has at most
`Kw_i^{-d}` terminal scalar bins").
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Parent
open scoped ENNReal

noncomputable section

/-- The scalar cells met by chart incidences at times in `[0,1]`. -/
def chartCells (σ : ℝ) : Finset (Fin 2 → ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊1 / σ⌋) ×ˢ (Finset.Icc ⌊-2 / σ⌋ ⌊1 / σ⌋)).image
    (fun w => ![w.1, w.2])

theorem chartCell_mem_chartCells {α : Type*} {b : α → Fin 6 → ℝ} {K ζ D χ σ : ℝ}
    {P Q β : ℤ} (hD : 0 < D) (hχ : 0 < χ) (hσ : 0 < σ) {l : α}
    (hl : l ∈ chartSet b K ζ D χ P Q β) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    chartCell D σ P Q (b l) t ∈ chartCells σ := by
  obtain ⟨hR₀, hR₁⟩ := chart_scalarParameter_mem hD hχ hl ht
  refine Finset.mem_image.mpr ⟨(⌊t / σ⌋, ⌊scalarParameter t ((b l 0 - P * D) / D)
    ((b l 1 - Q * D) / D) / σ⌋), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨Int.floor_nonneg.mpr (div_nonneg ht.1 hσ.le), ?_⟩, ?_, ?_⟩
    · exact Int.floor_mono (div_le_div_of_nonneg_right ht.2 hσ.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right hR₀ hσ.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right hR₁ hσ.le)
  · ext e; fin_cases e <;> rfl

theorem card_chartCells_mul_sq {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2) :
    ((chartCells σ).card : ℝ) * σ ^ 2 ≤ 6 := by
  have hcard : (chartCells σ).card ≤
      (Finset.Icc (0 : ℤ) ⌊1 / σ⌋).card * (Finset.Icc ⌊-2 / σ⌋ ⌊1 / σ⌋).card := by
    unfold chartCells
    exact Finset.card_image_le.trans (Finset.card_product _ _).le
  have h1 : ((Finset.Icc (0 : ℤ) ⌊1 / σ⌋).card : ℝ) ≤ 1 / σ + 1 := by
    rw [Int.card_Icc]
    have hf : (0 : ℤ) ≤ ⌊1 / σ⌋ := Int.floor_nonneg.mpr (by positivity)
    have : ((⌊1 / σ⌋ + 1 - 0).toNat : ℝ) = ((⌊1 / σ⌋ : ℤ) : ℝ) + 1 := by
      rw [sub_zero]
      have h' : (0 : ℤ) ≤ ⌊1 / σ⌋ + 1 := by omega
      rw [show ((⌊1 / σ⌋ + 1).toNat : ℝ) = (((⌊1 / σ⌋ + 1).toNat : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg h']
      push_cast; ring
    rw [this]
    linarith [Int.floor_le (1 / σ)]
  have h2 : ((Finset.Icc ⌊-2 / σ⌋ ⌊1 / σ⌋).card : ℝ) ≤ 3 / σ + 2 := by
    rw [Int.card_Icc]
    have hlo := Int.lt_floor_add_one (-2 / σ)
    have hhi := Int.floor_le (1 / σ)
    by_cases h : (0 : ℤ) ≤ ⌊1 / σ⌋ + 1 - ⌊-2 / σ⌋
    · rw [show ((⌊1 / σ⌋ + 1 - ⌊-2 / σ⌋).toNat : ℝ) =
          (((⌊1 / σ⌋ + 1 - ⌊-2 / σ⌋).toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg h]
      push_cast
      have : -2 / σ = -(2 / σ) := by ring
      have h3 : 3 / σ = 1 / σ + 2 / σ := by ring
      linarith
    · push Not at h
      rw [Int.toNat_of_nonpos h.le]
      simp only [Nat.cast_zero]
      positivity
  have h1' : (0 : ℝ) ≤ 1 / σ + 1 := by positivity
  calc ((chartCells σ).card : ℝ) * σ ^ 2
      ≤ ((Finset.Icc (0 : ℤ) ⌊1 / σ⌋).card * (Finset.Icc ⌊-2 / σ⌋ ⌊1 / σ⌋).card : ℕ) * σ ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg σ)
    _ ≤ (1 / σ + 1) * (3 / σ + 2) * σ ^ 2 := by
        push_cast
        gcongr
    _ = 3 + 5 * σ + 2 * σ ^ 2 := by field_simp; ring
    _ ≤ 6 := by nlinarith

/-- The hidden bins predicted by one true label on one scalar cell. -/
def labelBins (L : Fin 4 → ℝ) (D σ a K' : ℝ) (P Q β : ℤ) (χ : ℝ) (z : Fin 2 → ℤ) :
    Finset ℤ :=
  intervalBins a (parameterValue L ((P : ℝ) * D) ((Q : ℝ) * D) ((β : ℝ) * χ) D
    ((z 0 : ℝ) * σ) 0 ((z 1 : ℝ) * σ)) (5 * K' * a)

variable {α : Type*} [MeasurableSpace α]

/-- The support of the scalar cell and terminal hidden bin of a chart. -/
def chartSupport (b : α → Fin 6 → ℝ) (K ζ D χ σ a : ℝ) (P Q β : ℤ) {T n : ℕ}
    (j : Fin n → Fin (2 ^ T)) (B : Fin n → Set α) (L : Fin n → Fin 4 → ℝ) :
    Finset ((Fin 2 → ℤ) × ℤ) :=
  (chartCells σ).biUnion fun z =>
    ((cellLabels b K ζ D χ σ P Q β j B z).biUnion fun i =>
      labelBins (L i) D σ a (K * (1 + K) / 2) P Q β χ z).image fun x => (z, x)

/-- **The terminal support count** at one index: the scalar cells and hidden
bins of a.e. chart incidence lie in a set of at most `10¹²K²⁰σ⁻²a^(-d)` pairs. -/
theorem support_count_finite {ν : Measure α} {μ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {K a q g d D χ ζ σ δc : ℝ} {T n : ℕ} {j : Fin n → Fin (2 ^ T)}
    {A B : Fin n → Set α} {c : Fin n → Fin 5 → ℝ} {L : Fin n → Fin 4 → ℝ}
    (H : BlockHyp ν μ b K a q g d T n j A B c L)
    (hK : 1 ≤ K) (ha : 0 < a) (hq : 0 < q) (hg : 0 < g) (hD : 0 < D) (hχ : 0 < χ)
    (hσ : 0 < σ) (hδc : 0 < δc)
    (hgq : g ≤ K * q) (hqg : q ≤ K * g) (haq : a ≤ K * q) (hDa : D ≤ a)
    (hq1 : q ≤ 1 / 2) (hδcq : δc ≤ q ^ 2) (hσq : σ ≤ q / 2) (hσ1 : σ ≤ 1 / 2)
    (hDq : D ≤ q / 8) (hχD : χ ≤ D)
    (hsmall : 2 * D * σ + ζ + χ ≤ q ^ 2 / 2)
    (hcontact : 8 * K ^ 2 * (1 + a / q ^ 2) * (χ + ζ) ≤ K * a)
    (hcellosc : 8 * K ^ 2 * (1 + a / q ^ 2) * σ * (4 + 2 * K) ≤ K * a)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ blockTime T (j i))
    (hx3 : ∀ᵐ p ∂μ, |b p.1 2 + p.2 * b p.1 5| ≤ K)
    (hcap : ∀ (w : Fin 3 → ℤ) (j' : ℤ), μ {p | (fun e => ⌊(![p.2, b p.1 0 + p.2 * b p.1 3,
        b p.1 1 + p.2 * b p.1 4] : Fin 3 → ℝ) e / δc⌋) = w ∧
        ⌊b p.1 2 + p.2 * b p.1 5⌋ = j'} ≤ ENNReal.ofReal (K * δc ^ 3))
    (P Q β : ℤ) :
    ((chartSupport b K ζ D χ σ a P Q β j B L).card : ℝ) * σ ^ 2 ≤
        10 ^ 12 * K ^ 20 * a ^ (-d) ∧
      ∀ᵐ p ∂μ, p.1 ∈ chartSet b K ζ D χ P Q β → p.2 ∈ Icc (0 : ℝ) 1 →
        (chartCell D σ P Q (b p.1) p.2, ⌊(b p.1 2 + p.2 * b p.1 5) / a⌋) ∈
          chartSupport b K ζ D χ σ a P Q β j B L := by
  classical
  have hK₀ : 0 ≤ K := by linarith
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = K * (1 + K) / 2 := ⟨_, rfl⟩
  have hKK' : K ≤ K' := by rw [hK']; nlinarith
  have hK'K2 : K' ≤ K ^ 2 := by rw [hK']; nlinarith
  have hK'0 : 0 ≤ K' := by linarith
  have hsupp : chartSupport b K ζ D χ σ a P Q β j B L =
      (chartCells σ).biUnion fun z =>
        ((cellLabels b K ζ D χ σ P Q β j B z).biUnion fun i =>
          labelBins (L i) D σ a K' P Q β χ z).image fun x => (z, x) := by
    rw [hK']; rfl
  rw [hsupp]
  constructor
  · -- the count
    have hbins : ∀ (z : Fin 2 → ℤ) (i : Fin n),
        ((labelBins (L i) D σ a K' P Q β χ z).card : ℝ) ≤ 15 * K ^ 2 := by
      intro z i
      have h := card_intervalBins ha (mul_nonneg (mul_nonneg (by norm_num) hK'0) ha.le : (0 : ℝ) ≤ 5 * K' * a)
        (parameterValue (L i) ((P : ℝ) * D) ((Q : ℝ) * D) ((β : ℝ) * χ) D
          ((z 0 : ℝ) * σ) 0 ((z 1 : ℝ) * σ))
      have e : 2 * (5 * K' * a) / a + 5 = 10 * K' + 5 := by field_simp; ring
      rw [e] at h
      unfold labelBins
      have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
      linarith
    have hlab : ∀ z : Fin 2 → ℤ,
        ((cellLabels b K ζ D χ σ P Q β j B z).card : ℝ) ≤ 3 * 10 ^ 9 * K ^ 17 * a ^ (-d) :=
      fun z => card_cellLabels_le hb H hK ha hq hg hD hχ hσ hδc hgq hqg hq1 hδcq hσq
        hDq hχD hsmall hx3 hcap P Q β z
    have hper : ∀ z : Fin 2 → ℤ,
        ((((cellLabels b K ζ D χ σ P Q β j B z).biUnion fun i =>
          labelBins (L i) D σ a K' P Q β χ z).image fun x => (z, x)).card : ℝ) ≤
          3 * 10 ^ 9 * K ^ 17 * a ^ (-d) * (15 * K ^ 2) := by
      intro z
      calc _ ≤ (((cellLabels b K ζ D χ σ P Q β j B z).biUnion fun i =>
            labelBins (L i) D σ a K' P Q β χ z).card : ℝ) := by
            exact_mod_cast Finset.card_image_le
        _ ≤ ∑ i ∈ cellLabels b K ζ D χ σ P Q β j B z,
            ((labelBins (L i) D σ a K' P Q β χ z).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ cellLabels b K ζ D χ σ P Q β j B z, (15 * K ^ 2) :=
            Finset.sum_le_sum fun i _ => hbins z i
        _ = ((cellLabels b K ζ D χ σ P Q β j B z).card : ℝ) * (15 * K ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * 10 ^ 9 * K ^ 17 * a ^ (-d) * (15 * K ^ 2) :=
            mul_le_mul_of_nonneg_right (hlab z) (by positivity)
    have htot : ((((chartCells σ).biUnion fun z =>
        ((cellLabels b K ζ D χ σ P Q β j B z).biUnion fun i =>
          labelBins (L i) D σ a K' P Q β χ z).image fun x => (z, x))).card : ℝ) ≤
        ((chartCells σ).card : ℝ) * (3 * 10 ^ 9 * K ^ 17 * a ^ (-d) * (15 * K ^ 2)) := by
      calc _ ≤ ∑ z ∈ chartCells σ, ((((cellLabels b K ζ D χ σ P Q β j B z).biUnion fun i =>
            labelBins (L i) D σ a K' P Q β χ z).image fun x => (z, x)).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _z ∈ chartCells σ, (3 * 10 ^ 9 * K ^ 17 * a ^ (-d) * (15 * K ^ 2)) :=
            Finset.sum_le_sum fun z _ => hper z
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcells := card_chartCells_mul_sq hσ hσ1
    have hA : 0 ≤ a ^ (-d) := Real.rpow_nonneg ha.le _
    have hK19 : K ^ 19 ≤ K ^ 20 := pow_le_pow_right₀ hK (by norm_num)
    calc _ ≤ ((chartCells σ).card : ℝ) * (3 * 10 ^ 9 * K ^ 17 * a ^ (-d) * (15 * K ^ 2)) *
            σ ^ 2 := mul_le_mul_of_nonneg_right htot (sq_nonneg σ)
      _ = ((chartCells σ).card : ℝ) * σ ^ 2 * (45 * 10 ^ 9 * K ^ 19 * a ^ (-d)) := by ring
      _ ≤ 6 * (45 * 10 ^ 9 * K ^ 19 * a ^ (-d)) :=
          mul_le_mul_of_nonneg_right hcells (by positivity)
      _ ≤ 10 ^ 12 * K ^ 20 * a ^ (-d) := by
          have : (6 * (45 * 10 ^ 9) : ℝ) ≤ 10 ^ 12 := by norm_num
          calc 6 * (45 * 10 ^ 9 * K ^ 19 * a ^ (-d))
              = (6 * (45 * 10 ^ 9)) * (K ^ 19 * a ^ (-d)) := by ring
            _ ≤ 10 ^ 12 * (K ^ 20 * a ^ (-d)) :=
                mul_le_mul this (mul_le_mul_of_nonneg_right hK19 hA) (by positivity)
                  (by norm_num)
            _ = 10 ^ 12 * K ^ 20 * a ^ (-d) := by ring
  · -- membership
    filter_upwards [hcover] with p hp hpc hpt
    obtain ⟨i, hpB, hpI⟩ := hp
    set z := chartCell D σ P Q (b p.1) p.2 with hz
    have hzmem : z ∈ chartCells σ := chartCell_mem_chartCells hD hχ hσ hpc hpt
    have himem : i ∈ cellLabels b K ζ D χ σ P Q β j B z :=
      mem_cellLabels.mpr ⟨p, hpB, hpc, hpI, hpt, rfl⟩
    obtain ⟨hp₀, hp₁, -, -, -, hv, hPD, hβχ, hb0, hb3, he⟩ := chartSet_bounds hD hχ hpc
    obtain ⟨hτ₀, hτ₁, hR₀, hR₁⟩ := chartCell_corner hσ hz.symm
    have hx1 : |b p.1 0 + p.2 * b p.1 3| ≤ 2 * K := by
      have ht1 : |p.2| ≤ 1 := by rw [abs_of_nonneg hpt.1]; exact hpt.2
      calc |b p.1 0 + p.2 * b p.1 3| ≤ |b p.1 0| + |p.2| * |b p.1 3| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ K + 1 * K := by gcongr
        _ = 2 * K := by ring
    have hq1' : q ≤ 1 := by linarith
    have hslope := H.slope i p.1 hpB p.2 hpI
    obtain ⟨h₁, h₂, h₃⟩ := horizontal_affine_coeff_bounds (L i) (K := 2 * K) (a := a) (q := q)
      (Z := b p.1 0 + p.2 * b p.1 3) (t := p.2) (by linarith) ha.le hq hq1' hx1 hpt
      ((H.slope₃ i).trans (by nlinarith [div_nonneg ha.le (sq_nonneg q)]))
      (hslope.trans (by nlinarith [div_nonneg ha.le hq.le]))
    have hHeq : 2 * (2 * K) ^ 2 * (1 + a / q ^ 2) = 8 * K ^ 2 * (1 + a / q ^ 2) := by ring
    rw [hHeq] at h₁ h₂ h₃
    have haq' : a / q ≤ K := by rw [div_le_iff₀ hq]; linarith
    have hslope' : |L i 2 + p.2 * L i 3| ≤ K' * (1 + a / a) := by
      have h := (le_add_of_nonneg_left (abs_nonneg _)).trans hslope
      have h' : K * (1 + a / q) ≤ K * (1 + K) :=
        mul_le_mul_of_nonneg_left (by linarith) hK₀
      have e : K' * (1 + a / a) = K * (1 + K) := by
        rw [div_self ha.ne', hK']; ring
      rw [e]
      exact h.trans h'
    have hfit : |b p.1 2 + p.2 * b p.1 5 - affineValue (L i) p.2 (b p.1 0 + p.2 * b p.1 3)
        (b p.1 1 + p.2 * b p.1 4)| ≤ K' * a :=
      (H.fit i p.1 hpB p.2 hpI).trans (mul_le_mul_of_nonneg_right hKK' ha.le)
    have hp' : |(b p.1 0 - (P : ℝ) * D) / D| ≤ 1 := by
      rw [abs_of_nonneg hp₀]; exact hp₁.le
    have htτ : |p.2 - (z 0 : ℝ) * σ| ≤ σ := by rw [abs_le]; constructor <;> linarith
    have hR : |scalarParameter p.2 ((b p.1 0 - P * D) / D) ((b p.1 1 - Q * D) / D) -
        (z 1 : ℝ) * σ| ≤ σ := by rw [abs_le]; constructor <;> linarith
    have hcontact' : 8 * K ^ 2 * (1 + a / q ^ 2) * (χ + ζ) ≤ K' * a :=
      hcontact.trans (mul_le_mul_of_nonneg_right hKK' ha.le)
    have hD1 : D ≤ 1 := by linarith
    have hχ1 : χ ≤ 1 := by linarith
    have hcell' : 8 * K ^ 2 * (1 + a / q ^ 2) * σ *
        (1 + |(β : ℝ) * χ| + |(P : ℝ) * D| + D) ≤ K' * a := by
      have h4 : 1 + |(β : ℝ) * χ| + |(P : ℝ) * D| + D ≤ 4 + 2 * K := by linarith
      have hH0 : 0 ≤ 8 * K ^ 2 * (1 + a / q ^ 2) * σ := by positivity
      calc _ ≤ 8 * K ^ 2 * (1 + a / q ^ 2) * σ * (4 + 2 * K) :=
            mul_le_mul_of_nonneg_left h4 hH0
        _ ≤ K * a := hcellosc
        _ ≤ K' * a := mul_le_mul_of_nonneg_right hKK' ha.le
    have hfit5 := scalar_cell_fit_bound (L i) (b p.1) (pc := (P : ℝ) * D) (qc := (Q : ℝ) * D)
      (v := (β : ℝ) * χ) (τ := (z 0 : ℝ) * σ) (R₀ := (z 1 : ℝ) * σ) (q := a)
      hD hK'0 hDa ha le_rfl hpt hp' hv he h₁ h₂ h₃ hslope' htτ hR hcontact'
      hcell' hfit
    have hbin : ⌊(b p.1 2 + p.2 * b p.1 5) / a⌋ ∈ labelBins (L i) D σ a K' P Q β χ z :=
      mem_intervalBins ha (by simpa [mul_assoc] using hfit5)
    refine Finset.mem_biUnion.mpr ⟨z, hzmem, Finset.mem_image.mpr ⟨_, ?_, rfl⟩⟩
    exact Finset.mem_biUnion.mpr ⟨i, himem, hbin⟩

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
