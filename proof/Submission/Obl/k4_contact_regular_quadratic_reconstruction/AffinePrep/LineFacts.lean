import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.Source
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.LineBox
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.Cells

/-!
# Normalized witness lines

For an incidence of the quarter-band source, its normalized line satisfies all line hypotheses of
the affine-sheet core: full-time test bounds, the unit cube, bounded velocity, small contact error,
and an event at the normalized observed time, whose base point is inside the trimmed cube.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open MeasureTheory Set MvPolynomial Filter
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4QuadraticSheetCore
open Submission.Obl.k4_critical_switching_state_preparation.Data

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem shiftedVec_eq (D : ChartData) (b : Fin 6 → ℝ) (t : ℝ) :
    D.shiftedVec b t = shiftedPt D.L b t := rfl

theorem point_eq_x (cfg : Model α) (k : ℕ) (l : α) (t : ℝ) :
    point (cfg.b k l) t = cfg.x k l t := rfl

theorem x_castSucc (cfg : Model α) (k : ℕ) (l : α) (t : ℝ) :
    cfg.x k l t ∘ Fin.castSucc = basePt (cfg.b k l) t := by
  funext m
  fin_cases m <;> rfl

/-- The data of one normalized line. -/
structure LineFacts (D : ChartData) (G : MvPolynomial (Fin 4) ℝ) (H Kv εc hm : ℝ)
    (b : Fin 6 → ℝ) (σo : ℝ) : Prop where
  fit : ∀ σ ∈ Icc (0 : ℝ) 1,
    |testVal (testAlpha (D.hatTest G)) (testBeta (D.hatTest G)) (testGamma (D.hatTest G))
      (D.normLine b) σ| ≤ H ∧
    |testDer (testAlpha (D.hatTest G)) (testBeta (D.hatTest G)) (D.normLine b) σ| ≤ H
  cube : ∀ σ ∈ Icc (0 : ℝ) 1, lineP (D.normLine b) σ ∈ Icc (0 : Fin 3 → ℝ) 1
  obs : σo ∈ Icc (0 : ℝ) 1
  event : H⁻¹ ≤ |testDer (testAlpha (D.hatTest G)) (testBeta (D.hatTest G)) (D.normLine b) σo|
  vel : |D.normLine b 3| ≤ Kv
  con : |D.normLine b 4 + D.normLine b 0| ≤ εc
  inner : ∀ m, hm ≤ lineP (D.normLine b) σo m ∧ lineP (D.normLine b) σo m ≤ 1 - hm
  alpha : |2 * testAlpha (D.hatTest G)| ≤ H

theorem lineFacts_of_witness {cfg : Model α} {k : ℕ} {s v η : ℝ} {i : Fin (cfg.n k s)}
    {L : Fin 4 → ℝ} {G : MvPolynomial (Fin 4) ℝ} (hG : G.totalDegree ≤ 2)
    {J hm γ : ℝ} (hJ : 0 ≤ J) (hhm : 0 < hm) (hhm8 : hm ≤ 1 / 8)
    (hgq : cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹)
    (hrows : ∀ l ∈ cfg.A k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤
          cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ ∧
        |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤
          cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.N k ^ (-cfg.ℓ * s) ∧
        |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤
          cfg.K k * cfg.N k ^ (-cfg.ℓ * s))
    (hBA : cfg.B k s i ⊆ cfg.A k s i) (hK : 1 ≤ cfg.K k)
    (D : ChartData)
    (hDt : D.t₀ = ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s)
    (hDq : D.q = ((2 : ℝ) ^ cfg.T k s)⁻¹)
    (hDZ : D.Z₀ = cfg.c k s i 0 + D.t₀ * cfg.c k s i 1)
    (hDY : D.Y₀ = cfg.c k s i 2 + D.t₀ * cfg.c k s i 3 + cfg.c k s i 4 * D.Z₀)
    (hDB : D.B = 2 * cfg.K k + 2 * cfg.K k ^ 2 + 2 * J * cfg.K k + J)
    (hDc : D.c = cfg.N k ^ (-s - v)) (hDL : D.L = L) (hDγ : D.γ = γ)
    (hcenter : |cfg.c k s i 3 + D.Z₀| ≤ J * D.q) (hpivot : |cfg.c k s i 4 - D.t₀| ≤ J * D.q)
    (p : α × ℝ) (hpW : p ∈ shiftedWitness cfg k s v η i L G) (hpg : p ∈ goodSet cfg k)
    (hpt : p ∈ trimSet D.t₀ D.q hm) (hpband : |cfg.shiftedPoint k L p.1 p.2 3 - γ| ≤ 1 / 8)
    (hN : 0 < cfg.N k) :
    LineFacts D G (cfg.N k ^ η) (cfg.K k / (8 * D.B))
      (cfg.N k ^ (-cfg.e₀) / D.q / (8 * D.B)) hm (cfg.b k p.1) ((p.2 - D.t₀) / D.q) := by
  set b := cfg.b k p.1 with hbdef
  have hq : 0 < D.q := by rw [hDq]; positivity
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hB0 : 0 < D.B := by rw [hDB]; positivity
  have hc : 0 < D.c := by rw [hDc]; positivity
  have hHpos : 0 < cfg.N k ^ η := by positivity
  have hIeq : I (cfg.T k s) (cfg.j k s i) = Icc D.t₀ (D.t₀ + D.q) := by
    rw [I_eq_Icc, ← hDt, ← hDq]
  have hpA : p.1 ∈ cfg.A k s i := hBA hpW.1
  have hfull := hpW.2.2.1
  have hσt : ∀ σ ∈ Icc (0 : ℝ) 1, D.t₀ + D.q * σ ∈ I (cfg.T k s) (cfg.j k s i) := by
    intro σ hσ
    rw [hIeq]
    constructor <;> nlinarith [hσ.1, hσ.2]
  have hvecσ : ∀ σ, D.shiftedVec b (D.t₀ + D.q * σ) = cfg.shiftedPoint k L p.1 (D.t₀ + D.q * σ) := by
    intro σ
    rw [shiftedVec_eq, shiftedPoint_eq, hDL]
  have hhatdeg : (D.hatTest G).totalDegree ≤ 2 := (D.hatTest_degree G).trans hG
  -- the observed normalized time
  set σo := (p.2 - D.t₀) / D.q with hσodef
  have hσo : D.t₀ + D.q * σo = p.2 := by rw [hσodef]; field_simp; ring
  have hpI : p.2 ∈ Icc D.t₀ (D.t₀ + D.q) := by rw [← hIeq]; exact hpW.2.1
  have hσo01 : σo ∈ Icc (0 : ℝ) 1 := by
    rw [hσodef]
    constructor
    · exact div_nonneg (by linarith [hpI.1]) hq.le
    · rw [div_le_one hq]; linarith [hpI.2]
  -- the good-set bounds
  obtain ⟨hgb, hgc⟩ := hpg
  have hb3 : |b 3| ≤ cfg.K k := by
    have := abs_nonneg (b 0); have := abs_nonneg (b 1); have := abs_nonneg (b 4)
    linarith
  -- rows at the block start
  have ht₀I : D.t₀ ∈ I (cfg.T k s) (cfg.j k s i) := by
    rw [hIeq]; constructor <;> linarith
  obtain ⟨hr1, hr2, hr3⟩ := hrows p.1 hpA D.t₀ ht₀I
  have hrow1 : |b 0 + D.t₀ * b 3 - D.Z₀| ≤ cfg.K k * D.q := by
    have e : b 0 + D.t₀ * b 3 - D.Z₀ = (cfg.x k p.1 D.t₀) 1 - cfg.c k s i 0 - D.t₀ * cfg.c k s i 1 := by
      rw [hDZ]; simp [x, hbdef]; ring
    rw [e, hDq]; exact hr1
  have hrow2 : |(b 1 + D.t₀ * b 4) - cfg.c k s i 2 - D.t₀ * cfg.c k s i 3 -
      cfg.c k s i 4 * (b 0 + D.t₀ * b 3)| ≤ cfg.K k * D.q * cfg.N k ^ (-cfg.ℓ * s) := by
    have e : (b 1 + D.t₀ * b 4) - cfg.c k s i 2 - D.t₀ * cfg.c k s i 3 -
        cfg.c k s i 4 * (b 0 + D.t₀ * b 3) = (cfg.x k p.1 D.t₀) 2 - cfg.c k s i 2 -
          D.t₀ * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k p.1 D.t₀) 1 := by
      simp [x, hbdef]
    rw [e, hDq]; exact hr2
  have hcube := fun σ hσ => D.normLine_mem_cube hK hq (by rw [hDq]; exact hgq) hJ rfl hDB
    (cfg.c k s i) hDY hcenter hpivot b hb3 hrow1 hrow2 hr3 σ hσ
  refine ⟨?_, fun σ hσ => (hcube σ hσ).1, hσo01, ?_, ?_, ?_, ?_, ?_⟩
  · -- full-time test bounds
    intro σ hσ
    obtain ⟨_, hval, hder, _⟩ := hfull _ (hσt σ hσ)
    constructor
    · rw [← eval_point_eq_testVal _ hhatdeg, D.eval_hatTest_normLine hq.ne' hB0.ne' hc.ne',
        hvecσ, abs_mul, abs_inv, abs_of_pos hc]
      rw [hDc] at hc ⊢
      calc (cfg.N k ^ (-s - v))⁻¹ * |eval (cfg.shiftedPoint k L p.1 (D.t₀ + D.q * σ)) G| ≤
          (cfg.N k ^ (-s - v))⁻¹ * (cfg.N k ^ η * cfg.N k ^ (-s - v)) :=
            mul_le_mul_of_nonneg_left hval (by positivity)
        _ = cfg.N k ^ η := by field_simp
    · rw [← eval_point_pderiv_eq_testDer _ hhatdeg, D.eval_pderiv_hatTest_normLine hq.ne' hB0.ne'
        hc.ne', hvecσ]
      exact hder
  · -- the event
    have hfl := hpW.2.2.2
    rw [← eval_point_pderiv_eq_testDer _ hhatdeg, D.eval_pderiv_hatTest_normLine hq.ne' hB0.ne'
      hc.ne', hvecσ, hσo, ← Real.rpow_neg hN.le]
    exact hfl
  · -- velocity
    rw [D.normLine_velocity, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * D.B)]
    exact div_le_div_of_nonneg_right hb3 (by positivity)
  · -- contact
    rw [D.normLine_contact, abs_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * D.B),
      abs_of_pos hq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right hgc hq.le
  · -- the observed base point is inside the trimmed cube
    intro m
    have hc' := hcube σo hσo01
    obtain ⟨hT1, hT2⟩ := hpt
    have hσlo : hm ≤ σo := by
      rw [hσodef, le_div_iff₀ hq]; linarith
    have hσhi : σo ≤ 1 - hm := by
      rw [hσodef, div_le_iff₀ hq]; linarith
    have h0 : lineP (D.normLine b) σo 0 = σo := by
      rw [D.normLine_lineP hq.ne' hB0.ne']
      simp [ChartData.normBase, Transfer.unitContactBase, Transfer.contactBaseFrame, basePt]
      field_simp
    fin_cases m
    · simp only [Fin.zero_eta, Fin.isValue]; rw [h0]; exact ⟨hσlo, hσhi⟩
    · simp only [Fin.mk_one, Fin.isValue]
      constructor <;> linarith [hc'.2.1, hc'.2.2.1]
    · simp only [Fin.reduceFinMk, Fin.isValue]
      constructor <;> linarith [hc'.2.2.2.1, hc'.2.2.2.2]
  · -- curvature
    obtain ⟨_, _, _, hdd⟩ := hfull _ (hσt σo hσo01)
    rw [abs_two_testAlpha _ hhatdeg (point (D.normLine b) σo),
      D.eval_pderiv_pderiv_hatTest_normLine hq.ne' hB0.ne' hc.ne', hvecσ, abs_mul,
      abs_of_pos hc]
    rw [hDc] at hc ⊢
    calc cfg.N k ^ (-s - v) * |eval (cfg.shiftedPoint k L p.1 (D.t₀ + D.q * σo))
          (pderiv 3 (pderiv 3 G))| ≤ cfg.N k ^ (-s - v) * (cfg.N k ^ η / cfg.N k ^ (-s - v)) :=
          mul_le_mul_of_nonneg_left hdd (by positivity)
      _ = cfg.N k ^ η := by field_simp

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
