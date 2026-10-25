/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/CorrectedScalarSupport.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeCellSupport
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ScalarOscillationAsymptotic
import Submission.Obl.k4_subcritical_corrected_scalar_charts.TerminalErrors
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeDirectionalAsymptotic
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeScalarFit

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Original named ancestry and the common time correction give the exact
finite scalar support required by the chart interface, at any loss. -/
theorem Prepared.eventually_corrected_scalar_support (h : cfg.Prepared)
    {s₀ s M η ξ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hnear : s - s₀ ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16)
    (hM : 100 * s₀ < M) (hη : 0 < η)
    (hηsmall : η ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16) (hξ : 0 < ξ) :
    ∀ᶠ k in atTop, ∀ (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
      (P Q V : ℤ) (H : Fin 6 → ℝ) (β : Fin 3 → ℝ)
      (choice : Fin (2 ^ cfg.T k s₀) → Option (Fin (cfg.n k s₀)))
      (E : Set (α × ℝ)),
      |(P : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀))| ≤ 3 * cfg.K k →
      |(V : ℝ) * cfg.N k ^ (-M)| ≤ 3 * cfg.K k →
      |β 2| ≤ cfg.N k ^ η →
      (∀ t ∈ Icc (0 : ℝ) 1,
        ∀ p ∈ Icc ((P : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀)))
          (((P : ℝ) + 1) * cfg.N k ^ (-(2 * cfg.κ * s₀))),
        ∀ q ∈ Icc ((Q : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀)))
          (((Q : ℝ) + 1) * cfg.N k ^ (-(2 * cfg.κ * s₀))),
          |parameterPredictor H t p q| ≤ cfg.N k ^ η) →
      (∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1 ∧
        ⌊cfg.b k p.1 0 / cfg.N k ^ (-(2 * cfg.κ * s₀))⌋ = P ∧
        ⌊cfg.b k p.1 1 / cfg.N k ^ (-(2 * cfg.κ * s₀))⌋ = Q ∧
        ⌊cfg.b k p.1 3 / cfg.N k ^ (-M)⌋ = V ∧
        |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-M)) →
      (∀ p ∈ E, ∃ z, cfg.namedNativeIncidence k s₀ s choice p z) →
      (∀ p ∈ E, ∀ ip : Fin (cfg.n k s₀),
        choice (cfg.j k s₀ ip) = some ip →
        p.2 ∈ I (cfg.T k s₀) (cfg.j k s₀ ip) →
        |nativeFiberSignal H (parent.L ip) (cfg.N k ^ (-(2 * cfg.κ * s₀)))
          (cfg.N k ^ (-s₀)) p.2 - (β 0 + β 1 * p.2 + β 2 * p.2 ^ 2)| ≤
            cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4))) →
      ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
        (F.card : ℝ) * (cfg.N k ^ (-(20 * s₀))) ^ 2 ≤
          cfg.N k ^ ξ * (cfg.N k ^ (-(s - s₀))) ^ (-cfg.d) ∧
        ∀ p ∈ E,
          (chartCell (cfg.N k ^ (-(2 * cfg.κ * s₀))) (cfg.N k ^ (-(20 * s₀)))
            P Q (cfg.b k p.1) p.2,
            ⌊chartSignal (cfg.N k ^ (-s₀))
              (correctedBaseline H β (cfg.N k ^ (-s₀)) (cfg.N k ^ (-(2 * cfg.κ * s₀)))
                ((P : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀)))
                ((Q : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀)))) (cfg.b k p.1) p.2 /
                  cfg.N k ^ (-(s - s₀))⌋) ∈ F := by
  have hm1 : min cfg.κ (1 - 2 * cfg.κ) ≤ 1 :=
    (min_le_left _ _).trans h.rate_le_one
  have hη₄ : η ≤ s₀ / 4 := by
    have hh := mul_le_mul_of_nonneg_left hm1 hs₀.le
    linarith
  have hgap : s - s₀ < 18 * s₀ := by
    have hh := mul_le_mul_of_nonneg_left hm1 hs₀.le
    linarith
  have hpow := eventually_const_mul_rpow_lt h.scale_limit
    (show ξ / 4 < ξ by linarith) 59049
  filter_upwards [h.eventually_native_cell_list_count hs₀ hs hnear hM (show 0 < ξ / 8 by positivity),
    h.eventually_native_scalar_oscillation hs₀ hη₄ hgap,
    h.eventually_child_parent_direction hs₀ hs hη,
    h.eventually_corrected_scalar_error_bound hs₀ hs hnear hM hηsmall
      (show 0 < ξ / 8 by positivity), hpow] with k hcount hvar hdir herr hpow
  intro parent child P Q V H β choice E hpc hv hβ hH hE hwitness hsignal
  let D := cfg.N k ^ (-(2 * cfg.κ * s₀))
  let A := cfg.N k ^ (-s₀)
  let σ := cfg.N k ^ (-(20 * s₀))
  let w := cfg.N k ^ (-(s - s₀))
  let δ := cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4))
  let B := cfg.N k ^ (ξ / 8)
  let C := 81 * B * (A / cfg.N k ^ (-s)) ^ cfg.d
  let value := fun p : α × ℝ => chartSignal A
    (correctedBaseline H β A D ((P : ℝ) * D) ((Q : ℝ) * D)) (cfg.b k p.1) p.2
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hD : 0 < D := Real.rpow_pos_of_pos hN _
  have hA : 0 < A := Real.rpow_pos_of_pos hN _
  have hσ : 0 < σ := Real.rpow_pos_of_pos hN _
  have hw : 0 < w := Real.rpow_pos_of_pos hN _
  have hB : 1 ≤ B := Real.one_le_rpow hN1 (by positivity)
  have hσ1 : σ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hC : 0 ≤ C := by dsimp [C, B, A]; positivity
  have hcard := hcount parent child P Q V choice E hpc hv
    (fun p hp => ⟨(hE p hp).2.1, (hE p hp).2.2.2.1, (hE p hp).2.2.2.2⟩)
  have hH' : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ p ∈ Icc ((P : ℝ) * D) ((P : ℝ) * D + D),
      ∀ q ∈ Icc ((Q : ℝ) * D) ((Q : ℝ) * D + D),
        |parameterPredictor H t p q| ≤ cfg.N k ^ η := by
    simpa only [add_mul, one_mul] using hH
  have hfit : ∀ p ∈ E, ∀ z, cfg.namedNativeIncidence k s₀ s choice p z →
      |value p - nativeScalarEntry H β (child.L z.2) D A ((P : ℝ) * D) ((Q : ℝ) * D)
        ((V : ℝ) * cfg.N k ^ (-M)) p.2 (chartR D P Q (cfg.b k p.1) p.2)| ≤ B * w := by
    intro p hp z hz
    obtain ⟨ip, hchoice, hjp, hp₀, ht₀, hpc', htc, hAc, hIc⟩ := hz
    have hsignal' := hsignal p hp ip (by simpa only [hjp] using hchoice) ht₀
    have hdiff := hdir parent child ip z.2 hAc hIc p.2 htc
    have hcollapse : |nativeFiberSignal H (child.L z.2) D A p.2 -
        (β 0 + β 1 * p.2 + β 2 * p.2 ^ 2)| ≤
          cfg.N k ^ η * D / cfg.timeLength k s + δ := by
      have hh := corrected_directional_comparison (H0 := H) (v := (V : ℝ) * cfg.N k ^ (-M))
        (show 0 ≤ D / A by positivity) hdiff hsignal'
      have heq : D / A * (cfg.N k ^ η * A / cfg.timeLength k s) =
          cfg.N k ^ η * D / cfg.timeLength k s := by field_simp
      rw [show cfg.N k ^ (-s₀) = A from rfl, heq] at hh
      simpa only [nativeFiberSignal, horizontalLift_fiberDerivative] using hh
    have hvel := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error
      (Real.rpow_pos_of_pos hN (-M)) (cfg.b k p.1 3)
    rw [(hE p hp).2.2.2.1] at hvel
    have hh := child.corrected_scalar_fit h z.2 H β
      (p₀ := (P : ℝ) * D) (q₀ := (Q : ℝ) * D) hD hA hpc' (hE p hp).1 htc
      (by simpa only [mul_comm] using hvel) (hE p hp).2.2.2.2 hcollapse
    have hpn := normalized_parameter_mem_unit hD (hE p hp).2.1
    have hpabs : |(cfg.b k p.1 0 - (P : ℝ) * D) / D| ≤ 1 := by
      rw [abs_of_nonneg hpn.1]
      exact hpn.2
    have herror := herr child.assignments
    have hcol₀ : 0 ≤ cfg.N k ^ η * D / cfg.timeLength k s + δ :=
      (abs_nonneg _).trans hcollapse
    have hprod : |(cfg.b k p.1 0 - (P : ℝ) * D) / D| *
        (cfg.N k ^ η * D / cfg.timeLength k s + δ) ≤
          cfg.N k ^ η * D / cfg.timeLength k s + δ :=
      mul_le_of_le_one_left hcol₀ hpabs
    have hsmall :
        (cfg.K k * cfg.N k ^ (-s) + 72 * cfg.K k ^ 4 * cfg.N k ^ (-M)) / A +
          |(cfg.b k p.1 0 - (P : ℝ) * D) / D| *
            (cfg.N k ^ η * D / cfg.timeLength k s + δ) ≤ B * w := by
      calc
        _ ≤ (cfg.K k * cfg.N k ^ (-s) + 72 * cfg.K k ^ 4 * cfg.N k ^ (-M)) / A +
            (cfg.N k ^ η * D / cfg.timeLength k s + δ) := add_le_add le_rfl hprod
        _ ≤ _ := herror
    have hout := hh.trans hsmall
    dsimp only [value]
    rw [correctedBaseline_signal hA.ne']
    simpa only [chartSignal, chartR, chartP, chartQ] using hout
  obtain ⟨F, hF, hFcover⟩ := child.exists_scalar_cell_support (A := A) (L := B) (C := C)
    H β P Q ((V : ℝ) * cfg.N k ^ (-M))
    choice E value hD hσ hσ1 hw (show 0 ≤ B by positivity) hC
    (fun p hp => ⟨(hE p hp).1, (hE p hp).2.1, (hE p hp).2.2.1⟩)
    hwitness hcard hfit
    (fun i => hvar child i H β _ _ _ hpc hv hβ hH')
  · refine ⟨F, hF.trans ?_, hFcover⟩
    have hexp : (A / cfg.N k ^ (-s)) ^ cfg.d = w ^ (-cfg.d) := by
      dsimp [A, w]
      rw [← Real.rpow_sub hN, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le]
      congr 1
      ring
    have hBB : B * B = cfg.N k ^ (ξ / 4) := by
      dsimp [B]
      rw [← Real.rpow_add hN]
      congr 1
      ring
    calc
      81 * C * (2 * B + 7) = 6561 * B * (w ^ (-cfg.d)) * (2 * B + 7) := by
        dsimp [C]
        rw [hexp]
        ring
      _ ≤ 6561 * B * (w ^ (-cfg.d)) * (9 * B) := by gcongr; linarith
      _ = 59049 * cfg.N k ^ (ξ / 4) * (w ^ (-cfg.d)) := by rw [← hBB]; ring
      _ ≤ cfg.N k ^ ξ * (w ^ (-cfg.d)) :=
        mul_le_mul_of_nonneg_right hpow.le (Real.rpow_nonneg hw.le _)

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
