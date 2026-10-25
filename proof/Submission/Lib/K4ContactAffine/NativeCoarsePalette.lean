/- Adapted from: here:o223
   (x0927; countable-cell threshold extends x0775). -/
import Submission.Lib.K4ContactAffine.CellAffinePalette
import Submission.Lib.K4ContactAffine.InteriorCaps
import Submission.Lib.K4QuadraticSheetCore.SheetBridge

/-!
# A coarse affine palette in the original native coordinates

This finite-sample theorem combines the original pure/joint base caps, the
interior contact chart, and the quadratic sheet core. It produces three affine
predictors in the original coordinates for every good source line. No true
labels, affine coefficient bounds, or normalized incidence law are introduced.
-/

namespace Submission.Lib.K4ContactAffine

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4QuadraticSheetCore
open Submission.Lib.K4AffineMeshCaps
open Adapter

theorem native_coarse_palette_of_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (b : Ω → Fin 6 → ℝ) (time : Ω → ℝ)
    (π : Measure ℝ) [IsFiniteMeasure π]
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (Cs K R Λ E δ η m C pmax : ℝ)
    (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs) (hK : 1 ≤ K) (hR : 32 * K ≤ R)
    (hΛ : 1 ≤ Λ) (hΛK : 432 * K ≤ Λ) (hC : 0 < C) (hm : 0 < m)
    (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4) (hη : 0 < η)
    (hgap : Λ⁻¹ ≤ 3 * η / R)
    (hdensity : Λ⁻¹ ≤ m / (2 * (243 * C * R ^ 2)))
    (hE : 0 ≤ E) (hE1 : E / R ≤ 1)
    (hs1 : 4 * Cs * remezC 4 Λ * (3 * δ) ≤ 1)
    (hs2 : 8 * discBudget Cs Λ * (3 * δ) * Λ ^ 2 ≤ 1)
    (hs3 : 192 * Cs * sffKappa Cs Λ * (E / R + 3 * δ) * Λ ^ 2 ≤ 1)
    (G : Set Ω) (hG : ∀ᵐ p ∂μ, p ∈ G)
    (hgood : ∀ p ∈ G, time p ∈ Icc (0 : ℝ) 1 ∧
      |b p 0| + |b p 1| + |b p 3| + |b p 4| ≤ K ∧
      (∀ t ∈ Icc (0 : ℝ) 1, |eval (point (b p) t) P| ≤ K ∧
        |eval (point (b p) t) (pderiv 3 P)| ≤ K ∧
        |eval (point (b p) t) (pderiv 3 (pderiv 3 P))| ≤ K) ∧
      K⁻¹ ≤ |eval (point (b p) (time p)) (pderiv 3 P)| ∧ |b p 4 + b p 0| ≤ E)
    (hmass : ENNReal.ofReal m ≤ μ univ)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh δ (lineP (b p) (time p)) = q} ≤ ENNReal.ofReal (C * δ ^ 3))
    (hbin : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh δ (lineP (b p) (time p)) = q ∧ ⌊b p 3 / η⌋ = j} ≤
        ENNReal.ofReal (C * δ ^ 3) * π {w | ⌊w / η⌋ = j})
    (hπ : ∀ j : ℤ, π {w | ⌊w / η⌋ = j} ≤ ENNReal.ofReal pmax)
    (hsmall : 6 * ENNReal.ofReal (243 * C * R ^ 2) * ENNReal.ofReal pmax <
      ENNReal.ofReal (m / 2)) :
    ∃ L : Fin 3 → Fin 4 → ℝ, ∀ p ∈ G, ∃ u : Fin 3, ∀ t ∈ Icc (0 : ℝ) 1,
      |point (b p) t 3 - (L u 0 + L u 1 * t + L u 2 * point (b p) t 1 +
        L u 3 * point (b p) t 2)| ≤ cubeErr Cs Λ := by
  classical
  have hK0 : 0 < K := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hKΛ : K ≤ Λ := by linarith
  have hinvK : Λ⁻¹ ≤ K⁻¹ := inv_anti₀ hK0 hKΛ
  let P' := interiorTest R P
  let b' : Ω → Fin 6 → ℝ := fun p => interiorCoeff R (b p)
  let τ : Ω → ℝ := fun p => (time p + 1) / 3
  let B := 243 * C * R ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hP' : P'.totalDegree ≤ 2 := (interiorTest_degree R P).trans hP
  have hobs (p : Ω) (t : ℝ) :
      lineP (b' p) ((t + 1) / 3) = interiorBase R (lineP (b p) t) := by
    exact interiorCoeff_observed_base R (b p) t
  have hfull (p : Ω) (hp : p ∈ G) :=
    interior_full_fit R hR0.ne' P hP (b p) (hgood p hp).2.2.1
  have hGne : G.Nonempty := by
    by_contra hn
    have he : G = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hz : μ univ = 0 := by simpa [he] using ae_iff.mp hG
    have hh := hmass
    rw [hz] at hh
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hm)) hh
  obtain ⟨p₀, hp₀⟩ := hGne
  have hα : |2 * testAlpha P'| ≤ Λ := by
    rw [abs_two_testAlpha P' hP' (point (b' p₀) 0)]
    exact ((hfull p₀ hp₀) 0 ⟨le_rfl, zero_le_one⟩).2.2.trans hΛK
  have hgood' : ∀ p ∈ G, τ p ∈ Icc (0 : ℝ) 1 ∧
      (∀ σ ∈ Icc (0 : ℝ) 1,
        |testVal (testAlpha P') (testBeta P') (testGamma P') (b' p) σ| ≤ Λ ∧
        |testDer (testAlpha P') (testBeta P') (b' p) σ| ≤ Λ) ∧
      (∀ σ ∈ Icc (0 : ℝ) 1, lineP (b' p) σ ∈ Icc (0 : Fin 3 → ℝ) 1) ∧
      |b' p 4 + b' p 0| ≤ E / R ∧ |b' p 3| ≤ Λ ∧
      Λ⁻¹ ≤ |testDer (testAlpha P') (testBeta P') (b' p) (τ p)| := by
    intro p hp
    obtain ⟨ht, hb, hfit, hev, hcon⟩ := hgood p hp
    refine ⟨⟨by dsimp [τ]; linarith [ht.1], by dsimp [τ]; linarith [ht.2]⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro σ hσ
      rw [← eval_point_eq_testVal P' hP', ← eval_point_pderiv_eq_testDer P' hP']
      exact ⟨((hfull p hp) σ hσ).1.trans hΛK, ((hfull p hp) σ hσ).2.1.trans hΛK⟩
    · exact interiorCoeff_line_in_cube (b p) hK0 hR hb
    · rw [interiorCoeff_contact, abs_div, abs_of_pos hR0]
      exact div_le_div_of_nonneg_right hcon hR0.le
    · have hb3 : |b p 3| ≤ K := by
        linarith [abs_nonneg (b p 0), abs_nonneg (b p 1), abs_nonneg (b p 4)]
      change |3 * b p 3 / R| ≤ Λ
      rw [abs_div, abs_mul, abs_of_pos hR0, show |(3 : ℝ)| = 3 by norm_num,
        div_le_iff₀ hR0]
      nlinarith [mul_le_mul_of_nonneg_left hR1 (show 0 ≤ Λ by linarith)]
    · rw [← eval_point_pderiv_eq_testDer P' hP']
      exact hinvK.trans (by simpa only [P', b', τ, interior_observed_derivative R hR0.ne'] using hev)
  let S : Set (Fin 3 → ℝ) := Icc (fun _ => 1 / 4) (fun _ => 3 / 4)
  have hsource : ∀ᵐ p ∂μ, lineP (b' p) (τ p) ∈ S := by
    filter_upwards [hG] with p hp
    rw [show τ p = (time p + 1) / 3 from rfl, hobs]
    have hh := interiorBase_margin (b p) hK0 hR (hgood p hp).2.1 (hgood p hp).1
    exact ⟨fun e => (hh e).1, fun e => (hh e).2⟩
  have hmargin : ∀ x ∈ S, ∀ e, 1 / 4 ≤ x e ∧ x e ≤ 1 - 1 / 4 := by
    intro x hx e
    exact ⟨hx.1 e, by linarith [hx.2 e]⟩
  have hcap' : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh δ (lineP (b' p) (τ p)) = q} ≤ ENNReal.ofReal (B * δ ^ 3) := by
    intro q
    have hh := interior_cap_transfer μ (fun p => lineP (b p) (time p)) (fun _ => True)
      hR1 hδ hC.le (fun q' => by simpa only [and_true] using hcap q') q
    simpa only [← hobs, τ, B, and_true] using hh
  have hbin' : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh δ (lineP (b' p) (τ p)) = q ∧ ⌊b' p 3 / (3 * η / R)⌋ = j} ≤
        ENNReal.ofReal (B * δ ^ 3) * ENNReal.ofReal pmax := by
    intro q j
    have hh := interior_joint_bin_transfer μ (fun p => lineP (b p) (time p)) b π
      hR1 hδ hη.ne' hC.le hbin q j
    have hh' : μ {p | baseMesh δ (lineP (b' p) (τ p)) = q ∧
        ⌊b' p 3 / (3 * η / R)⌋ = j} ≤
        ENNReal.ofReal (B * δ ^ 3) * π {w | ⌊w / η⌋ = j} := by
      simpa only [← hobs, τ, B, b'] using hh
    exact hh'.trans (mul_le_mul' le_rfl (hπ j))
  obtain ⟨c₀, c, hpal⟩ := affine_palette_of_original_cell_caps μ b' τ
    (testAlpha P') (testBeta P') (testGamma P') (testBeta_degree P' hP') (testGamma_degree P' hP')
    Cs Λ (E / R) δ (3 * η / R) (1 / 4) m B (ENNReal.ofReal pmax)
    hCs hCs0 hΛ hm hB hδ (by positivity) hδquarter hgap hdensity hα hE1 hs1 hs2 hs3
    G hG hgood' S hsource hmargin hmass hcap' hbin' hsmall
  refine ⟨fun u => interiorAffineCoeff R (c₀ u) (c u), ?_⟩
  intro p hp
  obtain ⟨u, hu⟩ := hpal p hp
  refine ⟨u, ?_⟩
  intro t ht
  have hσ : (t + 1) / 3 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hh := hu ((t + 1) / 3) hσ
  rw [affineFn, dot3, hobs] at hh
  have hpred : c₀ u +
      (c u 0 * interiorBase R (lineP (b p) t) 0 + c u 1 * interiorBase R (lineP (b p) t) 1 +
        c u 2 * interiorBase R (lineP (b p) t) 2) =
      interiorAffineCoeff R (c₀ u) (c u) 0 + interiorAffineCoeff R (c₀ u) (c u) 1 *
        lineP (b p) t 0 + interiorAffineCoeff R (c₀ u) (c u) 2 * lineP (b p) t 1 +
        interiorAffineCoeff R (c₀ u) (c u) 3 * lineP (b p) t 2 := by
    convert interior_affine_prediction R (c₀ u) (c u) (lineP (b p) t) using 1; ring
  rw [hpred] at hh
  simpa only [lineW, b', interiorCoeff_observed_hidden, point, lineP, Matrix.cons_val] using hh

end Submission.Lib.K4ContactAffine
