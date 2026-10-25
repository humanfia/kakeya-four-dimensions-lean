import Submission.Obl.k4_horizontal_supercritical_three_projections.RawMargins

/-!
# The raw chart estimates (child A)

`HorizontalModel.raw_preparation`: for the prepared supercritical model and fixed
depths `s₀ < depth < min(3s₀/2, 2κs₀, U)` with `100 s₀ < min(U, e₀)`, the original law
is carried by good lines, and eventually every parameter chart has the total cap,
the pure and angular scalar cell caps and the terminal support count of
`RawChartData`, with any fixed loss `N^ξ` (paper, Proposition 9.7, "The scalar
projection: measure ceilings and support").
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Filter Parent
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped ENNReal

noncomputable section

namespace HorizontalModel

variable {α : Type} [MeasurableSpace α] {m : HorizontalModel α}

/-- The palette weight of a direction bin, as a real factor. -/
theorem palette_ofReal {π : Measure ℝ} [IsFiniteMeasure π] {χ : ℝ} (hχ : 0 < χ) (β : ℤ) :
    π {x : ℝ | ⌊x / χ⌋ = β} =
      ENNReal.ofReal (π (Ico ((β : ℝ) * χ) (((β : ℝ) + 1) * χ))).toReal := by
  rw [floor_div_eq_iff_mem_Ico hχ, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem cap_to_raw {π : Measure ℝ} [IsFiniteMeasure π] {χ C X Y D : ℝ} (hχ : 0 < χ)
    (hC : 0 ≤ C) (hX : 0 ≤ X) (hCX : C ≤ Y) (β : ℤ) :
    ENNReal.ofReal (C * X * D ^ 2) * π {x : ℝ | ⌊x / χ⌋ = β} ≤
      ENNReal.ofReal (Y * X * ((π (Ico ((β : ℝ) * χ) (((β : ℝ) + 1) * χ))).toReal * D ^ 2)) := by
  rw [palette_ofReal hχ, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hπ : 0 ≤ (π (Ico ((β : ℝ) * χ) (((β : ℝ) + 1) * χ))).toReal := ENNReal.toReal_nonneg
  calc C * X * D ^ 2 * (π (Ico ((β : ℝ) * χ) (((β : ℝ) + 1) * χ))).toReal
      = C * (X * ((π (Ico ((β : ℝ) * χ) (((β : ℝ) + 1) * χ))).toReal * D ^ 2)) := by ring
    _ ≤ Y * (X * ((π (Ico ((β : ℝ) * χ) (((β : ℝ) + 1) * χ))).toReal * D ^ 2)) :=
        mul_le_mul_of_nonneg_right hCX (by positivity)
    _ = Y * X * ((π (Ico ((β : ℝ) * χ) (((β : ℝ) + 1) * χ))).toReal * D ^ 2) := by ring

/-- **Raw chart data at one index**, from the true blocks of the depth, the
original caps, and explicit fixed-power margins. -/
theorem rawChartData_at (h : m.Valid) {k : ℕ} {s₀ δ M ξ R : ℝ}
    (hs₀ : 0 < s₀) (hlow : s₀ < δ) (hnear : δ < 3 * s₀ / 2) (hsuper : δ < 2 * m.κ * s₀)
    (hM : 100 * s₀ < M) (he : 100 * s₀ < m.e₀)
    (hR1 : 1 < R) (hRs : R⁻¹ ≤ s₀) (hRbig : M + 50 * s₀ ≤ R)
    (hA : m.AtDepth k δ R) (hc : m.CapsAt R k)
    (n1 : 2 * m.K k ≤ m.N k ^ (m.κ * δ))
    (n2 : m.K k ^ 2 ≤ m.N k ^ s₀)
    (n3 : 2 * m.K k ≤ m.N k ^ (20 * s₀ - m.κ * δ))
    (n4 : 2 ≤ m.N k ^ (20 * s₀))
    (n5 : 8 * m.K k ≤ m.N k ^ (2 * m.κ * s₀ - m.κ * δ))
    (n6 : 12 * m.K k ^ 2 ≤ m.N k ^ (2 * m.κ * s₀ + 20 * s₀ - 2 * m.κ * δ))
    (n7 : 32 * m.K k ^ 3 ≤ m.N k ^ (m.e₀ - 2 * m.κ * δ))
    (n8 : 32 * m.K k ^ 3 ≤ m.N k ^ (M - 2 * m.κ * δ))
    (n9 : 96 * m.K k ^ 4 ≤ m.N k ^ (20 * s₀ - 2 * m.κ * δ))
    (n10 : 4 ≤ m.N k ^ (2 * m.κ * s₀))
    (n11 : 4 ≤ m.N k ^ (19 * s₀))
    (n12 : 10 ^ 12 * m.K k ^ 20 ≤ m.N k ^ ξ) :
    RawChartData (m.N k) (m.K k) m.d s₀ (2 * m.κ * s₀) δ m.e₀ M ξ (m.b k) (m.μ k) (m.π k) := by
  have hN := h.N_pos k
  have hN1 := h.N_one_le k
  have hK := h.K_ge k
  have hK0 : 0 < m.K k := by linarith
  have hκ := h.κ_pos
  have hκ1 := h.κ_le
  have hsc := h.supercritical
  have hb := (h.basic k).1
  have hπ : IsProbabilityMeasure (m.π k) := (h.basic k).2.2.1
  have hsupp := (h.basic k).2.2.2.2.2.1
  have hδ : 0 < δ := by linarith
  have hκs₀ : m.κ * s₀ ≤ 1 * s₀ := mul_le_mul_of_nonneg_right hκ1 hs₀.le
  have hκs₀' : 0 ≤ m.κ * s₀ := mul_nonneg hκ.le hs₀.le
  have hκδ : m.κ * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hκ1 hδ.le
  have hκδ' : 0 ≤ m.κ * δ := mul_nonneg hκ.le hδ.le
  have e2s : 2 * m.κ * s₀ = 2 * (m.κ * s₀) := by ring
  have e2d : 2 * m.κ * δ = 2 * (m.κ * δ) := by ring
  have h2κδ : δ ≤ 2 * (m.κ * δ) := by
    have : 1 * δ ≤ 2 * m.κ * δ := mul_le_mul_of_nonneg_right hsc.le hδ.le
    linarith
  -- true blocks of the depth
  have hT1 : m.N k ^ (m.κ * δ) / m.K k ≤ (2 : ℝ) ^ m.T k δ := hA.1
  have hT2 : (2 : ℝ) ^ m.T k δ ≤ m.K k * m.N k ^ (m.κ * δ) := hA.2.1
  obtain ⟨hql, hqh⟩ := block_length_bounds hN hK hT1 hT2
  have hcover : ∀ᵐ p ∂m.μ k, ∃ i, p.1 ∈ m.B k δ i ∧
      p.2 ∈ blockTime (m.T k δ) (m.j k δ i) := hA.2.2.2.2.2.1
  obtain ⟨L, H⟩ := hA.blockHyp
  have hx3 : ∀ᵐ p ∂m.μ k, |m.b k p.1 2 + p.2 * m.b k p.1 5| ≤ m.K k := by
    filter_upwards [hA.ae_hidden_contact h, h.ae_time k] with p hp ht
    exact hp.1 p.2 ht
  -- scales
  have hgeq : m.N k ^ (-m.κ * δ) = m.N k ^ (-(m.κ * δ)) := by rw [neg_mul]
  have hq0 : 0 < (2 : ℝ) ^ (-(m.T k δ : ℤ)) := by positivity
  have hgpos : 0 < m.N k ^ (-m.κ * δ) := Real.rpow_pos_of_pos hN _
  have hgq : m.N k ^ (-m.κ * δ) ≤ m.K k * (2 : ℝ) ^ (-(m.T k δ : ℤ)) := by
    rw [hgeq]; rw [div_le_iff₀ hK0] at hql; linarith
  have hqg : (2 : ℝ) ^ (-(m.T k δ : ℤ)) ≤ m.K k * m.N k ^ (-m.κ * δ) := by
    rw [hgeq]; exact hqh
  have hag : m.N k ^ (-δ) ≤ m.N k ^ (-(m.κ * δ)) :=
    rpow_neg_le_rpow_neg hN1 (by linarith)
  have haq : m.N k ^ (-δ) ≤ m.K k * (2 : ℝ) ^ (-(m.T k δ : ℤ)) := by
    rw [← hgeq] at hag; linarith
  have hDa : m.N k ^ (-(2 * m.κ * s₀)) ≤ m.N k ^ (-δ) := rpow_neg_le_rpow_neg hN1 hsuper.le
  have hχD : m.N k ^ (-M) ≤ m.N k ^ (-(2 * m.κ * s₀)) :=
    rpow_neg_le_rpow_neg hN1 (by linarith)
  -- support count
  have hsupport := scalar_support_count (ν := m.ν k) hb H hK (Real.rpow_pos_of_pos hN _) hq0
    hgpos (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN (-M))
    (Real.rpow_pos_of_pos hN (-(20 * s₀))) (Real.rpow_pos_of_pos hN (-(2 * (m.κ * δ) + s₀)))
    hgq hqg haq hDa (margin_q_half hN hK hqh n1) (margin_δc hN hK hql n2)
    (margin_σq hN hK hql n3) (margin_σ_half hN n4) (margin_Dq hN hK hql n5) hχD
    (margin_small hN hK hql n6 n7 n8) (margin_contact hN1 hK hsc hδ hql n7 n8)
    (margin_cell hN1 hK hsc hδ hql n9) hsupp hcover hx3
    (hc.pure_cube hR1 (by linarith) (by linarith) hN)
  -- cell cap scales
  have hDpos : 0 < m.N k ^ (-(2 * m.κ * s₀)) := Real.rpow_pos_of_pos hN _
  have hσpos : 0 < m.N k ^ (-(20 * s₀)) := Real.rpow_pos_of_pos hN _
  have hD4 : m.N k ^ (-(2 * m.κ * s₀)) ≤ 1 / 4 := by
    have h' := const_mul_rpow_neg_le hN (x := 2 * m.κ * s₀) (y := 0) (C := 4) (by simpa using n10)
    simp only [neg_zero, Real.rpow_zero] at h'
    linarith
  have hσ2 := margin_σ_half hN n4
  have hδcσ : m.N k ^ (-(2 * m.κ * s₀ + 40 * s₀)) ≤
      m.N k ^ (-(2 * m.κ * s₀)) * (m.N k ^ (-(20 * s₀))) ^ 2 := by
    rw [rpow_neg_sq hN, rpow_neg_mul_rpow_neg hN]; ring_nf; exact le_rfl
  have hχσ : m.N k ^ (-M) ≤ m.N k ^ (-(2 * m.κ * s₀)) * m.N k ^ (-(20 * s₀)) := by
    rw [rpow_neg_mul_rpow_neg hN]; exact rpow_neg_le_rpow_neg hN1 (by linarith)
  have hζσ : m.N k ^ (-m.e₀) ≤ m.N k ^ (-(2 * m.κ * s₀)) * m.N k ^ (-(20 * s₀)) := by
    rw [rpow_neg_mul_rpow_neg hN]; exact rpow_neg_le_rpow_neg hN1 (by linarith)
  have hr8₀ : R⁻¹ ≤ 2 * m.κ * s₀ + 40 * s₀ := by linarith
  have hr8₁ : 2 * m.κ * s₀ + 40 * s₀ ≤ R := by linarith
  have hM₀ : R⁻¹ ≤ M := by linarith
  have hM₁ : M ≤ R := by linarith
  have hξK : 2 * 10 ^ 8 * m.K k ^ 5 ≤ m.N k ^ ξ := by
    have : 2 * 10 ^ 8 * m.K k ^ 5 ≤ 10 ^ 12 * m.K k ^ 20 := by
      have h5 : m.K k ^ 5 ≤ m.K k ^ 20 := pow_le_pow_right₀ hK (by norm_num)
      have h5' : 0 ≤ m.K k ^ 5 := by positivity
      linarith
    linarith
  have hξK4 : 3 * 10 ^ 6 * m.K k ^ 4 ≤ m.N k ^ ξ := by
    have : 3 * 10 ^ 6 * m.K k ^ 4 ≤ 10 ^ 12 * m.K k ^ 20 := by
      have h4 : m.K k ^ 4 ≤ m.K k ^ 20 := pow_le_pow_right₀ hK (by norm_num)
      have h4' : 0 ≤ m.K k ^ 4 := by positivity
      linarith
    linarith
  -- assemble
  simp only [RawChartData]
  intro P Q β
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- total chart cap
    have hcap1 := hc.directionCap (r := 2 * m.κ * s₀ + 40 * s₀) (s := 0) (M := M) hr8₀ hr8₁
      le_rfl (by linarith) hM₀ hM₁ hN β
    rw [neg_zero, Real.rpow_zero] at hcap1
    have htot := total_chart_cap hb (P := P) (Q := Q) hK hDpos (by linarith)
      (Real.rpow_pos_of_pos hN (-M)) hσpos hσ2 (Real.rpow_pos_of_pos hN _) hδcσ hχσ hζσ
      (Real.rpow_nonneg hN.le _) hsupp hx3 hcap1
    refine htot.trans ?_
    have := cap_to_raw (π := m.π k) (Real.rpow_pos_of_pos hN (-M)) (by positivity)
      zero_le_one hξK (D := m.N k ^ (-(2 * m.κ * s₀))) β
    simpa only [mul_one] using this
  · -- pure cell caps
    intro r q j hr₀ hr₁
    have hcapr := hc.directionCap (r := 2 * m.κ * s₀ + 40 * s₀) (s := r) (M := M) hr8₀ hr8₁
      hr₀ (by linarith) hM₀ hM₁ hN β
    have hpure := pure_cell_cap hb (P := P) (Q := Q) hK hDpos (by linarith)
      (Real.rpow_pos_of_pos hN (-M)) hσpos (by linarith) (Real.rpow_pos_of_pos hN (-r))
      (Real.rpow_pos_of_pos hN _) hδcσ hχσ hζσ (Real.rpow_nonneg hN.le _) hsupp hcapr q j
    have hset : {p : α × ℝ | p.1 ∈ chartSet (m.b k) (m.K k) (m.N k ^ (-m.e₀))
        (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-M)) P Q β ∧
        scalarCell (chartParams (m.N k ^ (-(2 * m.κ * s₀))) P Q (m.b k p.1)) p.2
          (m.N k ^ (-(20 * s₀))) = q ∧
        ⌊scalarX (chartParams (m.N k ^ (-(2 * m.κ * s₀))) P Q (m.b k p.1)) p.2 /
          m.N k ^ (-r)⌋ = j} =
        {p : α × ℝ | p.1 ∈ chartSet (m.b k) (m.K k) (m.N k ^ (-m.e₀))
        (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-M)) P Q β ∧
        chartCell (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-(20 * s₀))) P Q (m.b k p.1) p.2 = q ∧
        ⌊(m.b k p.1 2 + p.2 * m.b k p.1 5) / m.N k ^ (-r)⌋ = j} := by
      ext p
      simp only [Set.mem_ofPred_eq, scalarCell_chartParams, scalarX_chartParams]
    rw [hset] at hpure
    refine hpure.trans ?_
    have := cap_to_raw (π := m.π k) (Real.rpow_pos_of_pos hN (-M)) (by positivity)
      (by positivity : (0 : ℝ) ≤ (m.N k ^ (-(20 * s₀))) ^ 2 * (m.N k ^ (-r)) ^ m.d) hξK4
      (D := m.N k ^ (-(2 * m.κ * s₀))) β
    have e1 : 3 * 10 ^ 6 * m.K k ^ 4 * (m.N k ^ (-(20 * s₀))) ^ 2 *
        (m.N k ^ (-(2 * m.κ * s₀))) ^ 2 * (m.N k ^ (-r)) ^ m.d =
        3 * 10 ^ 6 * m.K k ^ 4 * ((m.N k ^ (-(20 * s₀))) ^ 2 * (m.N k ^ (-r)) ^ m.d) *
        (m.N k ^ (-(2 * m.κ * s₀))) ^ 2 := by ring
    rw [e1]
    refine this.trans (le_of_eq ?_)
    congr 1; ring
  · -- angular cell caps
    intro r q j v hr₀ hr₁
    have hcapa := hc.directionCap (r := 2 * m.κ * s₀ + 40 * s₀) (s := δ) (M := M) hr8₀ hr8₁
      hδ.le (by linarith) hM₀ hM₁ hN β
    have hh4 : 4 * m.N k ^ (-(20 * s₀)) ≤ m.N k ^ (-r) := by
      have h' := const_mul_rpow_neg_le hN (x := 20 * s₀) (y := s₀) (C := 4)
        (by ring_nf; ring_nf at n11; exact n11)
      exact h'.trans (rpow_neg_le_rpow_neg hN1 hr₁)
    have hh1 : m.N k ^ (-r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have hang := angular_cell_cap hb (P := P) (Q := Q) hK hDpos hD4 (Real.rpow_pos_of_pos hN (-M))
      hσpos (Real.rpow_pos_of_pos hN (-δ)) (Real.rpow_pos_of_pos hN _) hδcσ hh4 hh1 hχσ hζσ
      (Real.rpow_nonneg hN.le _) hsupp hcapa q j v
    have hset : {p : α × ℝ | p.1 ∈ chartSet (m.b k) (m.K k) (m.N k ^ (-m.e₀))
        (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-M)) P Q β ∧
        scalarCell (chartParams (m.N k ^ (-(2 * m.κ * s₀))) P Q (m.b k p.1)) p.2
          (m.N k ^ (-(20 * s₀))) = q ∧
        ⌊scalarX (chartParams (m.N k ^ (-(2 * m.κ * s₀))) P Q (m.b k p.1)) p.2 /
          m.N k ^ (-δ)⌋ = j ∧
        ⌊chartParams (m.N k ^ (-(2 * m.κ * s₀))) P Q (m.b k p.1) 1 / m.N k ^ (-r)⌋ = v} =
        {p : α × ℝ | p.1 ∈ chartSet (m.b k) (m.K k) (m.N k ^ (-m.e₀))
        (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-M)) P Q β ∧
        chartCell (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-(20 * s₀))) P Q (m.b k p.1) p.2 = q ∧
        ⌊(m.b k p.1 2 + p.2 * m.b k p.1 5) / m.N k ^ (-δ)⌋ = j ∧
        ⌊(-2 * ((m.b k p.1 0 - (P : ℝ) * m.N k ^ (-(2 * m.κ * s₀))) /
          m.N k ^ (-(2 * m.κ * s₀)))) / m.N k ^ (-r)⌋ = v} := by
      ext p
      simp only [Set.mem_ofPred_eq, scalarCell_chartParams, scalarX_chartParams,
        chartParams_one]
    rw [hset] at hang
    refine hang.trans ?_
    have hK4 : 0 ≤ m.K k ^ 4 := by positivity
    have := cap_to_raw (π := m.π k) (Real.rpow_pos_of_pos hN (-M)) (by positivity)
      (by positivity : (0 : ℝ) ≤ (m.N k ^ (-(20 * s₀))) ^ 2 * (m.N k ^ (-δ)) ^ m.d *
        m.N k ^ (-r)) (by linarith : 3 * 10 ^ 6 * m.K k ^ 4 / 4 ≤ m.N k ^ ξ)
      (D := m.N k ^ (-(2 * m.κ * s₀))) β
    have e1 : 3 * 10 ^ 6 * m.K k ^ 4 * (m.N k ^ (-(20 * s₀))) ^ 2 * (m.N k ^ (-r) / 4) *
        (m.N k ^ (-(2 * m.κ * s₀))) ^ 2 * (m.N k ^ (-δ)) ^ m.d =
        3 * 10 ^ 6 * m.K k ^ 4 / 4 * ((m.N k ^ (-(20 * s₀))) ^ 2 * (m.N k ^ (-δ)) ^ m.d *
        m.N k ^ (-r)) * (m.N k ^ (-(2 * m.κ * s₀))) ^ 2 := by ring
    rw [e1]
    refine this.trans (le_of_eq ?_)
    congr 1; ring
  · -- terminal support count
    obtain ⟨F, hFcard, hF⟩ := hsupport P Q β
    refine ⟨F, hFcard.trans ?_, ?_⟩
    · have : 10 ^ 12 * m.K k ^ 20 * (m.N k ^ (-δ)) ^ (-m.d) ≤
          m.N k ^ ξ * (m.N k ^ (-δ)) ^ (-m.d) :=
        mul_le_mul_of_nonneg_right n12 (Real.rpow_nonneg (Real.rpow_nonneg hN.le _) _)
      exact this
    · filter_upwards [hF] with p hp hpA
      have := hp hpA
      rw [scalarCell_chartParams, scalarX_chartParams] at this
      exact this

/-- **Child A: the raw chart estimates.** For the prepared supercritical model and
fixed depths `s₀ < depth < min(3s₀/2, 2κs₀, U)` with `100 s₀ < min(U, e₀)`, the
original law is carried by good lines, and for every fine direction mesh
`M > 100 s₀` and every loss `ξ > 0`, eventually every parameter chart has the
total cap, the pure and angular scalar cell caps and the terminal support count. -/
theorem raw_preparation (h : m.Valid) {s₀ depth : ℝ} (hs₀ : 0 < s₀)
    (h100U : 100 * s₀ < m.U) (h100e : 100 * s₀ < m.e₀) (hlow : s₀ < depth)
    (hUdepth : depth < m.U) (hnear : depth < 3 * s₀ / 2) (hsuper : depth < 2 * m.κ * s₀) :
    RawPreparation m.N m.K m.d s₀ (2 * m.κ * s₀) depth m.e₀ m.b m.μ m.π := by
  refine ⟨h.originalGood hs₀ (by linarith), ?_⟩
  intro M hM ξ hξ
  have hκ := h.κ_pos
  have hκ1 := h.κ_le
  have hδ : 0 < depth := by linarith
  have hκδ : m.κ * depth ≤ 1 * depth := mul_le_mul_of_nonneg_right hκ1 hδ.le
  have hκδ' : 0 < m.κ * depth := mul_pos hκ hδ
  have hκs : 0 < m.κ * s₀ := mul_pos hκ hs₀
  have e2s : 2 * m.κ * s₀ = 2 * (m.κ * s₀) := by ring
  have e2d : 2 * m.κ * depth = 2 * (m.κ * depth) := by ring
  have hκgap : m.κ * depth < m.κ * (2 * s₀) := mul_lt_mul_of_pos_left (by linarith) hκ
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = M + 50 * s₀ + 1 / s₀ + 1 := ⟨_, rfl⟩
  have hinv : 0 < 1 / s₀ := by positivity
  have hR1 : 1 < R := by rw [hR]; linarith
  have hRs : R⁻¹ ≤ s₀ := by
    rw [inv_le_comm₀ (by linarith) hs₀]
    rw [hR, one_div] at *
    linarith
  have hRbig : M + 50 * s₀ ≤ R := by rw [hR]; linarith
  have hRdepth : R⁻¹ ≤ depth := by linarith
  have ev (x C : ℝ) (p : ℕ) (hx : 0 < x) := h.eventually_const_mul_K_pow_le hx C p
  filter_upwards [h.capsAt hR1, h.prepared R hR1,
    ev (m.κ * depth) 2 1 hκδ',
    ev s₀ 1 2 hs₀,
    ev (20 * s₀ - m.κ * depth) 2 1 (by linarith),
    ev (20 * s₀) 2 0 (by linarith),
    ev (2 * m.κ * s₀ - m.κ * depth) 8 1 (by linarith),
    ev (2 * m.κ * s₀ + 20 * s₀ - 2 * m.κ * depth) 12 2 (by linarith),
    ev (m.e₀ - 2 * m.κ * depth) 32 3 (by linarith),
    ev (M - 2 * m.κ * depth) 32 3 (by linarith),
    ev (20 * s₀ - 2 * m.κ * depth) 96 4 (by linarith),
    ev (2 * m.κ * s₀) 4 0 (by linarith),
    ev (19 * s₀) 4 0 (by linarith),
    ev ξ (10 ^ 12) 20 hξ] with k hc hprep n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12
  simp only [pow_one, pow_zero, mul_one, one_mul] at n1 n2 n3 n4 n5 n10 n11
  exact rawChartData_at h hs₀ hlow hnear hsuper hM h100e hR1 hRs hRbig
    (hprep depth hRdepth hUdepth.le) hc n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12

end HorizontalModel

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
