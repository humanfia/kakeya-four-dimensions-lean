import Submission.Obl.k4_subcritical_chart_projection.ChartScalar
import Submission.Obl.k4_subcritical_chart_projection.OriginalCaps

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_horizontal_supercritical_three_projections
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- Factor the physical hidden scale and the unchanged velocity palette
back into the original reference numerator. -/
theorem chart_cap_reference_form (π : Measure ℝ) [IsFiniteMeasure π]
    {A σ β χ D a w d : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hχ : 0 < χ) (ha : 0 < a) (hw : 0 < w) (q : Fin 3 → ℤ) :
    ENNReal.ofReal (A * σ ^ 2 * β * D ^ 2 * (a * w) ^ d) *
      π {x | ⌊x / χ⌋ = q 0} =
    ENNReal.ofReal (A * σ ^ 2 * β * w ^ d * chartReference π χ D a d q) := by
  rw [Submission.Obl.k4_critical_conditional_row_preparation.floor_bin_eq_Ico χ (q 0) hχ]
  have hnn : 0 ≤ A * σ ^ 2 * β * D ^ 2 * (a * w) ^ d := by positivity
  rw [← ENNReal.ofReal_toReal (measure_ne_top π
    (Ico ((q 0 : ℝ) * χ) (((q 0 : ℝ) + 1) * χ))), ← ENNReal.ofReal_mul hnn]
  congr 1
  unfold chartReference
  rw [Real.mul_rpow ha.le hw.le]
  ring

/-- A terminal table and the original physical joint caps give exactly the
conditioned Scalar input, with the original prior as its denominator. -/
theorem corrected_scalar_admissible {α : Type} [MeasurableSpace α]
    {N K d κ s₀ M ξ η Bmax : ℝ} (hN : 1 ≤ N) (hs₀ : 0 < s₀) (hκ : 0 < κ)
    (hξ : 0 < ξ) (hK : 0 ≤ K)
    (depth : Fin 3 → ℝ) (h : Fin 3) (hdepth : s₀ < depth h) (hmax : depth h ≤ Bmax)
    (ν : Measure α) [IsProbabilityMeasure ν] (μ ρ ζ : Measure (α × ℝ))
    (π : Measure ℝ) [IsFiniteMeasure π] (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (C : Charts b ρ π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀))
      (N ^ (-(20 * s₀))) d (N ^ ξ) (N ^ (-ξ))
      (fun h => N ^ (-(depth h - s₀))))
    (hζ : ζ ≤ C.law) (hζμ : ζ ≤ μ)
    (hdom : ζ ≤ ENNReal.ofReal (N ^ η) • (ν.prod volume))
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hnative : OriginalJointCaps N K d M Bmax μ π b)
    (hχσ : N ^ (-M) ≤ N ^ (-(2 * κ * s₀)) * N ^ (-(20 * s₀)))
    (hχσ₂ : N ^ (-M) ≤ N ^ (-(2 * κ * s₀)) * (N ^ (-(20 * s₀))) ^ 2)
    (hsmall : 24 * (N ^ ξ) ^ 2 * N ^ (-M) / N ^ (-(2 * κ * s₀)) ≤ N ^ (-depth h))
    (hcapFactor : 8 * 10 ^ 6 * (N ^ ξ) ^ 3 * K ≤ N ^ η)
    (hcoeff : 2 * N ^ ξ ≤ N ^ η)
    (c : Fin C.n) (hG₀ : ν (C.G c) ≠ 0)
    (hc₁ : N ^ (-(1 : ℝ)) ≤
      chartReference π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀)) d (C.q c) /
        (ν (C.G c)).toReal)
    (hc₂ : chartReference π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀)) d (C.q c) /
        (ν (C.G c)).toReal ≤ N ^ (1 : ℝ))
    (hsupport : N ^ ξ ≤ N ^ η *
      (chartReference π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀)) d (C.q c) /
        (ν (C.G c)).toReal)⁻¹) :
    ScalarAdmissible N η d (depth h - s₀) (20 * s₀) 1 1 s₀
      (chartReference π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀)) d (C.q c) /
        (ν (C.G c)).toReal)
      (ProbabilityTheory.cond ν (C.G c))
      (padCoefficients (C.G c) (fun l => scalarCoefficients (N ^ (-(2 * κ * s₀)))
        (N ^ (-s₀)) (C.q c 1) (C.q c 2) (C.g c) (b l)))
      (chartLaw ν ζ (C.G c)) := by
  let D := N ^ (-(2 * κ * s₀))
  let χ := N ^ (-M)
  let σ := N ^ (-(20 * s₀))
  let a := N ^ (-s₀)
  let H := N ^ ξ
  let W := chartReference π χ D a d (C.q c)
  let bs := fun l => scalarCoefficients D a (C.q c 1) (C.q c 2) (C.g c) (b l)
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hD : 0 < D := Real.rpow_pos_of_pos hN₀ _
  have hD₁ : D ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN₀ _
  have hσ : 0 < σ := Real.rpow_pos_of_pos hN₀ _
  have hσ₁ : σ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have ha : 0 < a := Real.rpow_pos_of_pos hN₀ _
  have hH : 1 ≤ H := Real.one_le_rpow hN hξ.le
  have hsub : C.G c ⊆ chartSet b H χ D χ (C.q c 1) (C.q c 2) (C.q c 0) := by
    intro l hl
    obtain ⟨hv, hp, hq, he, hhor⟩ := C.bins c l hl
    exact ⟨he 0, he 3, hhor, hp, hq, hv⟩
  have hbG : ∀ l ∈ C.G c, ∀ e, |b l e| ≤ H := fun l hl => (C.bins c l hl).2.2.2.1
  have hsuppζ : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((hζμ _).trans_eq hsupp) bot_le
  have hW : 0 ≤ W := chartReference_nonneg π ha.le _
  have hactual (r : ℝ) : a * N ^ (-r) = N ^ (-(s₀ + r)) := by
    dsimp [a]
    rw [← Real.rpow_add hN₀]
    congr 1
    ring
  have hsmallr (r : ℝ) (hr : r ≤ depth h - s₀) :
      24 * H ^ 2 * χ / D ≤ a * N ^ (-r) := by
    apply hsmall.trans
    rw [hactual]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  apply normalized_scalar_admissible hN₀ ν ζ ζ (C.G c) (C.measurable c) hG₀ le_rfl
    bs (measurable_scalarCoefficients D a (C.q c 1) (C.q c 2) (C.g c) b hb)
    hdom hsuppζ (fun l hl e => (scalarCoefficients_bound hD hH (C.bins c l hl).2.1
      (C.bins c l hl).2.2.1 (C.signal c l hl) e).trans hcoeff) hc₁ hc₂
  · intro r z j hr hrs
    have hw : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN₀ _
    have hnat : DirectionCap μ b π K χ χ (a * N ^ (-r)) d (C.q c 0) := by
      rw [hactual]
      exact hnative (s₀ + r) (by linarith) (by linarith) _
    have hc := corrected_pure_cap μ b π (C.g c) hχ hD hD₁ hσ hσ₁ ha hw hH hK
      hχσ hχσ₂ (hsmallr r hrs) (C.norm c) hnat hsupp (C.G c) hsub hbG z j
    have heq := chart_cap_reference_form π (σ := σ) (D := D) (d := d)
      (show 0 ≤ 8 * 10 ^ 6 * H ^ 3 * K by positivity)
      (show (0 : ℝ) ≤ 1 by norm_num) hχ ha hw (C.q c)
    simp only [mul_one] at heq
    apply (hζμ _).trans (hc.trans ?_)
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (by
      change (8 * 10 ^ 6 * H ^ 3 * K) * σ ^ 2 * (N ^ (-r)) ^ d * W ≤ _
      gcongr)
  · obtain ⟨F, hcard, hF⟩ := C.support c h
    refine ⟨F, hcard.trans (mul_le_mul_of_nonneg_right hsupport (by positivity)), ?_⟩
    filter_upwards [ae_mono hζ hF] with p hp hpG
    simpa only [bs, scalarCoefficients_cell, scalarCoefficients_x] using hp hpG
  · intro r z j i hr hrs
    have hβ : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN₀ _
    have hσβ : σ ≤ N ^ (-r) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    have hβ₁ : N ^ (-r) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
    have hw : 0 < N ^ (-(depth h - s₀)) := Real.rpow_pos_of_pos hN₀ _
    have hnat : DirectionCap μ b π K χ χ (a * N ^ (-(depth h - s₀))) d (C.q c 0) := by
      rw [hactual, show s₀ + (depth h - s₀) = depth h by ring]
      exact hnative (depth h) (by linarith) hmax _
    have hc := corrected_angular_cap μ b π (C.g c) hχ hD hD₁ hσ ha hw hH hK
      hχσ hχσ₂ hσβ hβ₁ (hsmallr _ le_rfl) (C.norm c) hnat hsupp (C.G c) hsub hbG z j i
    have heq := chart_cap_reference_form π (σ := σ) (D := D) (d := d)
      (show 0 ≤ 8 * 10 ^ 6 * H ^ 3 * K by positivity) hβ.le hχ ha hw (C.q c)
    apply (hζμ _).trans (hc.trans ?_)
    rw [heq]
    simp only [neg_one_mul]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = (8 * 10 ^ 6 * H ^ 3 * K) * σ ^ 2 * (N ^ (-(depth h - s₀))) ^ d * N ^ (-r) * W := by ring
      _ ≤ _ := by gcongr


/-- The whole-chart ceiling used to select typical unchanged prior
denominators. The original chart floors pay for their sum separately. -/
theorem corrected_chart_upper_cap {α : Type} [MeasurableSpace α]
    {N K d κ s₀ M ξ Bmax : ℝ} (hN : 1 ≤ N) (hs₀ : 0 < s₀) (hκ : 0 < κ)
    (hK : 0 ≤ K) (hd : d ≤ 1) (hξ : 0 < ξ) (hlarge : 2 ≤ N ^ ξ) (hξhalf : 2 * ξ ≤ s₀)
    (depth : Fin 3 → ℝ) (h : Fin 3) (hdepth : s₀ < depth h) (hmax : depth h ≤ Bmax)
    (μ ρ : Measure (α × ℝ)) (π : Measure ℝ) [IsFiniteMeasure π]
    (b : α → Fin 6 → ℝ)
    (C : Charts b ρ π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀))
      (N ^ (-(20 * s₀))) d (N ^ ξ) (N ^ (-ξ))
      (fun h => N ^ (-(depth h - s₀))))
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hnative : OriginalJointCaps N K d M Bmax μ π b)
    (hχσ : N ^ (-M) ≤ N ^ (-(2 * κ * s₀)) * N ^ (-(20 * s₀)))
    (hsmall : 24 * (N ^ ξ) ^ 2 * N ^ (-M) / N ^ (-(2 * κ * s₀)) ≤ N ^ (-depth h))
    (hwhole : 2 * 10 ^ 6 * (N ^ ξ) ^ 5 * K ≤ N ^ (10 * ξ)) :
    ∀ c, μ (C.G c ×ˢ univ) ≤
      ENNReal.ofReal (N ^ (10 * ξ) *
        chartReference π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀)) d (C.q c)) := by
  intro c
  let χ := N ^ (-M)
  let D := N ^ (-(2 * κ * s₀))
  let a := N ^ (-s₀)
  let H := N ^ ξ
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN₀ _
  have hD : 0 < D := Real.rpow_pos_of_pos hN₀ _
  have hD₁ : D ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
  have ha : 0 < a := Real.rpow_pos_of_pos hN₀ _
  have hχD : χ ≤ D := by
    apply hχσ.trans
    have hh : N ^ (-(20 * s₀)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hD.le
  have hsub : C.G c ⊆ chartSet b H χ D χ (C.q c 1) (C.q c 2) (C.q c 0) := by
    intro l hl
    obtain ⟨hv, hp, hq, he, hhor⟩ := C.bins c l hl
    exact ⟨he 0, he 3, hhor, hp, hq, hv⟩
  have hactual : a * H ^ 2 = N ^ (-(s₀ - 2 * ξ)) := by
    dsimp [a, H]
    rw [← Real.rpow_mul_natCast hN₀.le, ← Real.rpow_add hN₀]
    congr 1
    norm_num
    ring
  have hnat : DirectionCap μ b π K χ χ (a * H ^ 2) d (C.q c 0) := by
    rw [hactual]
    exact hnative (s₀ - 2 * ξ) (by linarith) (by linarith) _
  have hsmall' : 24 * H ^ 2 * χ / D ≤ a :=
    hsmall.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  let E := (C.G c ×ˢ (univ : Set ℝ)) ∩ {p : α × ℝ | p.2 ∈ Icc (0 : ℝ) 1}
  have hm := corrected_whole_chart_cap μ b π (C.g c) hχ hD hD₁ ha
    hlarge hK hχD hd hsmall' (C.norm c) hnat E (by
      rintro p ⟨⟨hp, -⟩, ht⟩
      exact ⟨hsub hp, ht, C.signal c p.1 hp p.2 ht, (C.bins c p.1 hp).2.2.2.1⟩)
  have heq := chart_cap_reference_form π (σ := 1) (β := 1) (D := D) (w := 1) (d := d)
    (show 0 ≤ 2 * 10 ^ 6 * H ^ 5 * K by positivity) (by norm_num) hχ ha (by norm_num) (C.q c)
  simp only [one_pow, mul_one, Real.one_rpow] at heq
  apply (measure_le_of_time_support hsupp (C.G c ×ˢ univ)).trans (hm.trans ?_)
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hwhole (chartReference_nonneg π ha.le _))

end Submission.Obl.k4_subcritical_chart_projection
