import Submission.Obl.k4_horizontal_strict_parameter_step.ChartCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.ChartDuration
import Submission.Obl.k4_horizontal_strict_parameter_step.MixedDuration

/-!
# One old chart after density and duration preparation

Under the fixed conditional prior `C.prior ν` of an old full-time label, the current law of the
chart is cut at half its density (x0852's `prepare_chart_duration`), short line/time-bin pieces
are deleted, and the integrated mixed caps of `ChartCaps.lean` become instantaneous mixed caps
(x0852's `affine_mixed_cap_from_duration`). The time bins are `Mb` closed bins of length
`1/Mb`, fine enough that the normalized scalar moves by at most `ζ` in one bin.
-/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4Homogenization

noncomputable section

/-- `Mb` closed bins of length `1/Mb` cover the unit time interval. -/
theorem unit_bins_cover {Mb : ℕ} (hMb : 0 < Mb) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ j : Fin Mb, t ∈ Icc (((j : ℕ) : ℝ) / Mb) (((j : ℕ) : ℝ) / Mb + 1 / Mb) := by
  have hMbR : (0 : ℝ) < Mb := by exact_mod_cast hMb
  have ht0 : 0 ≤ t * Mb := mul_nonneg ht.1 hMbR.le
  by_cases hlt : ⌊t * Mb⌋₊ < Mb
  · refine ⟨⟨⌊t * Mb⌋₊, hlt⟩, ?_, ?_⟩
    · rw [div_le_iff₀ hMbR]
      exact Nat.floor_le ht0
    · rw [← add_div, le_div_iff₀ hMbR]
      exact (Nat.lt_floor_add_one _).le
  · push Not at hlt
    have hge : (Mb : ℝ) ≤ t * Mb := by
      have h1 : ((⌊t * Mb⌋₊ : ℕ) : ℝ) ≤ t * Mb := Nat.floor_le ht0
      have h2 : (Mb : ℝ) ≤ ((⌊t * Mb⌋₊ : ℕ) : ℝ) := by exact_mod_cast hlt
      linarith
    have ht1 : t = 1 := by
      have : 1 ≤ t := by
        by_contra hcon
        push Not at hcon
        nlinarith
      linarith [ht.2]
    refine ⟨⟨Mb - 1, by omega⟩, ?_, ?_⟩
    · rw [ht1, div_le_one hMbR]
      have : ((Mb - 1 : ℕ) : ℝ) ≤ Mb := by exact_mod_cast Nat.sub_le Mb 1
      exact this
    · rw [ht1, ← add_div, le_div_iff₀ hMbR, one_mul]
      have : ((Mb - 1 : ℕ) : ℝ) = (Mb : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ Mb)]
        simp
      rw [this]
      linarith

/-- The unit bins have total length one. -/
theorem unit_bins_volume {Mb : ℕ} (hMb : 0 < Mb) :
    ∑ j : Fin Mb, volume (Icc (((j : ℕ) : ℝ) / Mb) (((j : ℕ) : ℝ) / Mb + 1 / Mb)) ≤ 1 := by
  have hMbR : (0 : ℝ) < Mb := by exact_mod_cast hMb
  have hvol : ∀ j : Fin Mb,
      volume (Icc (((j : ℕ) : ℝ) / Mb) (((j : ℕ) : ℝ) / Mb + 1 / Mb)) =
        ENNReal.ofReal (1 / Mb) := by
    intro j
    rw [Real.volume_Icc]
    congr 1
    ring
  simp only [hvol, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_le_one]
  rw [mul_one_div, div_self hMbR.ne']

/-- The normalized chart coordinates are measurable. -/
theorem RawChart.measurable_coords {α : Type} [MeasurableSpace α] (C : RawChart α)
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (hA : MeasurableSet C.A) (a D : ℝ) :
    Measurable (C.y b a D) ∧ Measurable (C.β b a D) ∧ Measurable (C.γ b a D) := by
  have hc := measurable_chartCoordinates hA hb C.h a D ((C.q 1 : ℝ) * D) ((C.q 2 : ℝ) * D)
  have h0 : Measurable fun l => chartCoordinates C.A b C.h a D ((C.q 1 : ℝ) * D)
      ((C.q 2 : ℝ) * D) l 0 := (measurable_pi_apply 0).comp hc
  have h1 : Measurable fun l => chartCoordinates C.A b C.h a D ((C.q 1 : ℝ) * D)
      ((C.q 2 : ℝ) * D) l 1 := (measurable_pi_apply 1).comp hc
  have h2 : Measurable fun l => chartCoordinates C.A b C.h a D ((C.q 1 : ℝ) * D)
      ((C.q 2 : ℝ) * D) l 2 := (measurable_pi_apply 2).comp hc
  have h3 : Measurable fun l => chartCoordinates C.A b C.h a D ((C.q 1 : ℝ) * D)
      ((C.q 2 : ℝ) * D) l 3 := (measurable_pi_apply 3).comp hc
  refine ⟨?_, h2, h3⟩
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-- The old full-time fit and the old static square bound the normalized coordinates. -/
theorem RawChart.coords_bounds {α : Type} (C : RawChart α) {b : α → Fin 6 → ℝ}
    {a D M : ℝ} (ha : 0 < a) (hD : 0 < D) (hM : 0 ≤ M)
    (hgrid : ∀ l ∈ C.A, ⌊b l 0 / D⌋ = C.q 1 ∧ ⌊b l 1 / D⌋ = C.q 2)
    (hfit : ∀ l ∈ C.A, ∀ t ∈ Icc (0 : ℝ) 1,
      |b l 2 + t * b l 5 - predictor C.h t (b l 0) (b l 1)| ≤ M * a) :
    ∀ l, (∀ i, |C.y b a D l i| ≤ 1) ∧ |C.β b a D l| ≤ M ∧ |C.γ b a D l| ≤ 2 * M := by
  have hbox : ∀ l ∈ C.A, b l 0 ∈ Icc ((C.q 1 : ℝ) * D) ((C.q 1 : ℝ) * D + D) ∧
      b l 1 ∈ Icc ((C.q 2 : ℝ) * D) ((C.q 2 : ℝ) * D + D) := by
    intro l hl
    obtain ⟨h0, h1⟩ := hgrid l hl
    have m0 := mem_Icc_of_floor_eq hD h0
    have m1 := mem_Icc_of_floor_eq hD h1
    exact ⟨⟨m0.1, by linarith [m0.2]⟩, ⟨m1.1, by linarith [m1.2]⟩⟩
  intro l
  obtain ⟨b0, b1, b2, b3⟩ := chartCoordinates_bounds ha hD hM hbox hfit l
  refine ⟨?_, b2, b3⟩
  intro i
  fin_cases i
  · exact b0
  · exact b1

/-- One old chart after density cutoff and duration preparation, with its instantaneous mixed
caps under the fixed conditional prior and the lower density in the original current law. -/
theorem chart_prepared {α : Type} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {μ σ : Measure (α × ℝ)} {π : Measure ℝ} [IsFiniteMeasure π] {b : α → Fin 6 → ℝ}
    (C : RawChart α) {d K M χ D a ζ m δ' : ℝ}
    (hb : Measurable b)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hK : 1 ≤ K) (hM : 1 ≤ M) (hD : 0 < D) (hD1 : D ≤ 1)
    (ha : 0 < a) (hm : 0 < m) (hχ : 0 < χ) (hζ1 : ζ ≤ 1) (hδ' : 0 < δ')
    (hm8 : 8 * M * m ≤ ζ) (hmD : (K + 2) * m ≤ D * ζ) (hχD : χ ≤ D * ζ)
    (hma : m ≤ 2 * a * ζ) (ha1 : 2 * a ≤ 1)
    (hround : 2 * M * m + (6 * M / D) * (χ + (K + 2) * m) ≤ 2 * a * ζ)
    (hσμ : σ ≤ μ) (hμ : μ ≤ ENNReal.ofReal K • ν.prod volume)
    (hA : MeasurableSet C.A) (hA0 : ν C.A ≠ 0)
    (hgood : ∀ᵐ p ∂μ, |b p.1 4 + b p.1 0| ≤ χ ∧ |b p.1 0| ≤ K ∧ |b p.1 3| ≤ K)
    (hgrid : ∀ l ∈ C.A, ⌊b l 3 / χ⌋ = C.q 0 ∧ ⌊b l 0 / D⌋ = C.q 1 ∧ ⌊b l 1 / D⌋ = C.q 2)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc ((C.q 1 : ℝ) * D) (((C.q 1 : ℝ) + 1) * D),
      ∀ q ∈ Icc ((C.q 2 : ℝ) * D) (((C.q 2 : ℝ) + 1) * D), |predictor C.h t p q| ≤ M)
    (hfit : ∀ l ∈ C.A, ∀ t ∈ Icc (0 : ℝ) 1,
      |b l 2 + t * b l 5 - predictor C.h t (b l 0) (b l 1)| ≤ M * a)
    (hcap : MeshCapAt μ π b d K χ m)
    (hfloor : ENNReal.ofReal (D ^ 2 * a ^ d / M) *
      π (Ico ((C.q 0 : ℝ) * χ) (((C.q 0 : ℝ) + 1) * χ)) ≤ ENNReal.ofReal K * ν C.A)
    (hE : MeasurableSet C.E) (hEsub : C.E ⊆ C.A ×ˢ Icc (0 : ℝ) 1)
    (hconull : σ ((C.A ×ˢ Icc (0 : ℝ) 1) \ C.E) = 0)
    (hheavy : ENNReal.ofReal δ' * ν C.A ≤ σ (C.A ×ˢ Icc (0 : ℝ) 1)) :
    ∃ E' : Set (α × ℝ), MeasurableSet E' ∧ E' ⊆ C.E ∧
      ENNReal.ofReal (δ' / (4 * K)) ≤ ((C.prior ν).prod volume) E' ∧
      (ENNReal.ofReal (δ' / 2) * ν C.A) • ((C.prior ν).prod volume).restrict E' ≤
        σ.restrict (C.A ×ˢ Icc (0 : ℝ) 1) ∧
      ∀ t r w : ℝ, ζ ≤ r → r ≤ 1 → ζ ≤ w → w ≤ 1 → ∀ (z : Fin 2 → ℤ) (j : ℤ),
        (C.prior ν) {l | (l, t) ∈ E' ∧ ⌊FirstJet.xbar (C.β b a D) (C.γ b a D) l t / w⌋ = j ∧
          ⌊C.y b a D l 0 / r⌋ = z 0 ∧ ⌊C.y b a D l 1 / r⌋ = z 1} ≤
          ENNReal.ofReal ((201600 * K ^ 3 * M / δ' ^ 2) * r ^ 2 * w ^ d) := by
  classical
  have hζ : 0 < ζ := by
    by_contra hcon
    push Not at hcon
    have : D * ζ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD.le hcon
    linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  -- the time bins
  set Mb : ℕ := ⌈2 * M / ζ⌉₊ with hMb
  have h2Mζ : 1 ≤ 2 * M / ζ := by
    rw [le_div_iff₀ hζ]
    linarith
  have hMbpos : 0 < Mb := Nat.ceil_pos.mpr (by positivity)
  have hMbR : (0 : ℝ) < Mb := by exact_mod_cast hMbpos
  have hMbge : 2 * M / ζ ≤ Mb := Nat.le_ceil _
  have hMble : (Mb : ℝ) ≤ 4 * M / ζ := by
    have hlt : (Mb : ℝ) < 2 * M / ζ + 1 := Nat.ceil_lt_add_one (by positivity)
    have : 2 * M / ζ + 1 ≤ 4 * M / ζ := by
      have : 4 * M / ζ = 2 * M / ζ + 2 * M / ζ := by ring
      linarith
    linarith
  set τ : ℝ := 1 / Mb with hτdef
  have hτ : 0 < τ := by positivity
  have hsmall : 2 * M * τ ≤ ζ := by
    rw [hτdef, mul_one_div, div_le_iff₀ hMbR]
    rw [div_le_iff₀ hζ] at hMbge
    linarith
  have hmτ : m ≤ τ / 2 := by
    rw [hτdef]
    have hMb4 : (Mb : ℝ) * ζ ≤ 4 * M := by
      rw [le_div_iff₀ hζ] at hMble
      linarith
    rw [div_div, le_div_iff₀ (by positivity)]
    nlinarith
  set left : Fin Mb → ℝ := fun j => ((j : ℕ) : ℝ) / Mb with hleft
  set I : Fin Mb → Set ℝ := fun j => Icc (left j) (left j + τ) with hIdef
  have hI : ∀ j, MeasurableSet (I j) := fun j => measurableSet_Icc
  have hsum : ∑ j, volume (I j) ≤ 1 := unit_bins_volume hMbpos
  have hcover : ∀ t ∈ Icc (0 : ℝ) 1, ∃ j, t ∈ Icc (left j) (left j + τ) :=
    fun t ht => unit_bins_cover hMbpos t ht
  -- the conditional prior and the chart law
  have hσK : σ ≤ ENNReal.ofReal K • ν.prod volume := hσμ.trans hμ
  obtain ⟨hprob, hdom, hlamuniv⟩ := normalize_chart_prior ν σ hσK C.A hA hA0
  set lam : Measure (α × ℝ) := (ν C.A)⁻¹ • σ.restrict (C.A ×ˢ Icc (0 : ℝ) 1) with hlam
  haveI : IsProbabilityMeasure (C.prior ν) := hprob
  have hAI : MeasurableSet (C.A ×ˢ Icc (0 : ℝ) 1) := hA.prod measurableSet_Icc
  have hAtop : ν C.A ≠ ⊤ := measure_ne_top ν C.A
  have hsupp : ∀ᵐ p ∂lam, p ∈ C.E := by
    rw [ae_iff, hlam, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply' hAI]
    have : {a : α × ℝ | a ∉ C.E} ∩ (C.A ×ˢ Icc (0 : ℝ) 1) =
        (C.A ×ˢ Icc (0 : ℝ) 1) \ C.E := by
      ext p
      simp [and_comm]
    rw [this, hconull, mul_zero]
  have hmass : ENNReal.ofReal δ' ≤ lam univ := by
    rw [hlamuniv]
    calc ENNReal.ofReal δ' = (ν C.A)⁻¹ * (ENNReal.ofReal δ' * ν C.A) := by
          rw [mul_comm (ENNReal.ofReal δ'), ← mul_assoc, ENNReal.inv_mul_cancel hA0 hAtop,
            one_mul]
      _ ≤ (ν C.A)⁻¹ * σ (C.A ×ˢ Icc (0 : ℝ) 1) := by gcongr
  have hEunit : C.E ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun p hp => ⟨trivial, (hEsub hp).2⟩
  obtain ⟨E₀, E', hE₀, hE', hE'E₀, hE₀S, -, hmassE', hweighted, hdur⟩ :=
    prepare_chart_duration (C.prior ν) lam C.E hE hEunit hsupp hδ' hK0
      (η := δ' / (4 * K)) (by positivity) (by rw [mul_div_assoc']; field_simp; rfl) hdom hmass
      I hI hsum
  refine ⟨E', hE', hE'E₀.trans hE₀S, hmassE', ?_, ?_⟩
  · -- the lower density in the original current law
    have hrestr : ((C.prior ν).prod volume).restrict E' ≤ ((C.prior ν).prod volume).restrict E₀ :=
      Measure.restrict_mono hE'E₀ le_rfl
    calc (ENNReal.ofReal (δ' / 2) * ν C.A) • ((C.prior ν).prod volume).restrict E'
        = ν C.A • (ENNReal.ofReal (δ' / 2) • ((C.prior ν).prod volume).restrict E') := by
          rw [smul_smul, mul_comm]
      _ ≤ ν C.A • (ENNReal.ofReal (δ' / 2) • ((C.prior ν).prod volume).restrict E₀) := by
          gcongr
      _ ≤ ν C.A • lam := by gcongr
      _ = σ.restrict (C.A ×ˢ Icc (0 : ℝ) 1) := by
          rw [hlam, smul_smul, ENNReal.mul_inv_cancel hA0 hAtop, one_smul]
  · -- the instantaneous mixed caps
    obtain ⟨hy, hβ, hγ⟩ := RawChart.measurable_coords C hb hA a D
    have hbounds := RawChart.coords_bounds C (b := b) ha hD hM0.le
      (fun l hl => ⟨(hgrid l hl).2.1, (hgrid l hl).2.2⟩) hfit
    have hγV : ∀ l, |C.γ b a D l| ≤ 2 * M := fun l => (hbounds l).2.2
    have hE'unit : E' ⊆ univ ×ˢ Icc (0 : ℝ) 1 := (hE'E₀.trans hE₀S).trans hEunit
    have hduration : ∀ p ∈ E', ∀ i, p.2 ∈ Icc (left i) (left i + τ) →
        ENNReal.ofReal (τ / (4 * K / δ')) ≤
          incidenceDuration volume (E₀.indicator 1) (Icc (left i) (left i + τ)) p.1 := by
      intro p hp i hpi
      have := hdur p hp i hpi
      refine le_trans (le_of_eq ?_) this
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    have hcapbin : ∀ (i : Fin Mb) (r w : ℝ), ζ ≤ r → r ≤ 1 → ζ ≤ w → w ≤ 1 →
        ∀ (x₀ : ℝ) (y₀ : Fin 2 → ℝ),
        lam {p | p.2 ∈ Icc (left i) (left i + τ) ∧
          |FirstJet.xbar (C.β b a D) (C.γ b a D) p.1 p.2 - x₀| ≤ 2 * w ∧
          |C.y b a D p.1 0 - y₀ 0| ≤ r ∧ |C.y b a D p.1 1 - y₀ 1| ≤ r} ≤
          ENNReal.ofReal ((25200 * K ^ 2 * M * r ^ 2 * w ^ d) * τ) := by
      intro i r w hr hr1 hw hw1 x₀ y₀
      exact chart_bin_cap C hd hd1 hK0.le hM0 hD hD1 ha hm hτ hχ hr hr1 hw hw1 hmτ hmD hχD
        hma ha1 hround hσμ hA hA0 hgood hgrid hnorm hcap hfloor
    have hmix := affine_mixed_cap_from_duration (C.prior ν) lam (C.y b a D) (C.β b a D)
      (C.γ b a D) hy hβ hγ hE' hE₀ hE'unit left (τ := τ) (V := 2 * M) (ζ := ζ)
      (δ := δ' / 2) (K := 4 * K / δ') (B := 25200 * K ^ 2 * M) (d := d) hτ hζ
      (by positivity) (by positivity) (by positivity) hγV hsmall hcover hweighted hduration
      hcapbin
    intro t r w hr hr1 hw hw1 z j
    refine (hmix t r w hr hr1 hw hw1 z j).trans (le_of_eq ?_)
    congr 1
    field_simp
    ring

end

end Submission.Obl.k4_horizontal_strict_parameter_step
