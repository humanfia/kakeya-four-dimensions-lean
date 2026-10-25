import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Input
import Submission.Obl.k4_wide_three_layer_scalar_inputs.FiniteLabels

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

/-- The original block and its retained law, before the finite witness partition is
assigned a measurable label function. The mass uses its full original reference. -/
structure BlockPrefix {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (s H : ℝ) where
  i : Fin (cfg.n k s)
  L : Fin 4 → ℝ
  hL : cfg.F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) +
    MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) +
    MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
    MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4))
  L_bd : ∀ e, |L e| ≤ H * cfg.N k ^ (2 * s)
  H_one : 1 ≤ H
  lam : Measure (α × ℝ)
  lam_le : lam ≤ cfg.ρ k
  lam_supp : ∀ᵐ p ∂lam, p.1 ∈ cfg.B k s i ∧
    p.2 ∈ Icc ((cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s)
      ((cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s + ((2 : ℝ) ^ cfg.T k s)⁻¹)
  lam_mass : ENNReal.ofReal H⁻¹ *
    (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i)) ≤ lam univ

namespace BlockPrefix

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s H : ℝ}

def frame (P : BlockPrefix cfg k s H) : Frame := blockFrame cfg k s P.i P.L

/-- Convert a finite disjoint measurable witness partition into `ComparedBlock`.
Every fit and menu is consumed only on its original witness set. -/
theorem of_partition (P : BlockPrefix cfg k s H) (u v χ : ℝ)
    (Γ Λ : Type) [Fintype Γ] [Fintype Λ]
    (E : Λ → Set α) (hE : ∀ x, MeasurableSet (E x))
    (hdisj : ∀ x y, x ≠ y → Disjoint (E x) (E y)) (fallback : Λ)
    (hcover : ∀ᵐ p ∂P.lam, ∃ x, p.1 ∈ E x)
    (crs : Λ → Γ) (chartOf : Γ → ℤ × ℤ)
    (tc : Γ → Fin 4 → ℝ) (pc : Γ → Fin 6 → ℝ) (D1 D2 : Λ → ℝ)
    (htc : ∀ γ e, |tc γ e| ≤ H) (hpc : ∀ γ e, |pc γ e| ≤ H)
    (hchart : ∀ x, ∀ᵐ p ∂P.lam, p.1 ∈ E x →
      (⌊cfg.b k p.1 3 / χ⌋, ⌊cfg.b k p.1 0 / χ⌋) = chartOf (crs x))
    (hfit1 : ∀ x, ∀ᵐ p ∂P.lam, p.1 ∈ E x →
      |P.frame.resid (cfg.b k p.1) p.2 -
        quadZ (pc (crs x)) (P.frame.zt p.2) (P.frame.zZ (cfg.b k p.1) p.2) - D1 x -
        transv (tc (crs x)) (P.frame.zt p.2) (P.frame.zZ (cfg.b k p.1) p.2)
          (P.frame.tr (cfg.b k p.1) p.2)| ≤ H * cfg.N k ^ (-u))
    (hfit2 : ∀ x, ∀ᵐ p ∂P.lam, p.1 ∈ E x →
      |P.frame.resid (cfg.b k p.1) p.2 -
        quadZ (pc (crs x)) (P.frame.zt p.2) (P.frame.zZ (cfg.b k p.1) p.2) - D2 x -
        transv (tc (crs x)) (P.frame.zt p.2) (P.frame.zZ (cfg.b k p.1) p.2)
          (P.frame.tr (cfg.b k p.1) p.2)| ≤ H * cfg.N k ^ (-v))
    (hcoarse : ∀ z3 z0 : ℤ, ∃ G : Finset Γ, (G.card : ℝ) ≤ H ∧
      ∀ x, ∀ᵐ p ∂P.lam, p.1 ∈ E x →
        ⌊cfg.b k p.1 3 / χ⌋ = z3 → ⌊cfg.b k p.1 0 / χ⌋ = z0 → crs x ∈ G)
    (hoffset1 : ∀ (z3 z0 : ℤ) (γ : Γ), ∃ F : Finset ℤ,
      (F.card : ℝ) ≤ H * cfg.N k ^ (cfg.d * u) ∧
      ∀ x, ∀ᵐ p ∂P.lam, p.1 ∈ E x →
        ⌊cfg.b k p.1 3 / χ⌋ = z3 → ⌊cfg.b k p.1 0 / χ⌋ = z0 → crs x = γ →
          ⌊D1 x / cfg.N k ^ (-u)⌋ ∈ F)
    (hoffset2 : ∀ (z3 z0 : ℤ) (γ : Γ), ∃ F : Finset ℤ,
      (F.card : ℝ) ≤ H * cfg.N k ^ (cfg.d * v) ∧
      ∀ x, ∀ᵐ p ∂P.lam, p.1 ∈ E x →
        ⌊cfg.b k p.1 3 / χ⌋ = z3 → ⌊cfg.b k p.1 0 / χ⌋ = z0 → crs x = γ →
          ⌊D2 x / cfg.N k ^ (-v)⌋ ∈ F) :
    Nonempty (ComparedBlock cfg k s u v χ H) := by
  classical
  obtain ⟨lab, hmeas, hlabel, -⟩ :=
    exists_measurable_finite_label E hE hdisj fallback
  have hmem : ∀ᵐ p ∂P.lam, p.1 ∈ E (lab p.1) := by
    filter_upwards [hcover] with p hp
    obtain ⟨x, hx⟩ := hp
    simpa only [hlabel x p.1 hx] using hx
  refine ⟨{
    i := P.i
    L := P.L
    hL := P.hL
    L_bd := P.L_bd
    H_one := P.H_one
    lam := P.lam
    lam_le := P.lam_le
    lam_supp := P.lam_supp
    lam_mass := P.lam_mass
    Γ := Γ
    instΓ := inferInstance
    Λ := Λ
    instΛ := inferInstance
    lab := lab
    lab_meas := hmeas
    crs := crs
    chartOf := chartOf
    chart_ae := ?_
    tc := tc
    pc := pc
    D1 := D1
    D2 := D2
    tc_bd := htc
    pc_bd := hpc
    fit1 := ?_
    fit2 := ?_
    coarse_list := ?_
    offset1_list := ?_
    offset2_list := ?_ }⟩
  · filter_upwards [hmem, ae_all_iff.mpr hchart] with p hp hc
    exact hc (lab p.1) hp
  · filter_upwards [hmem, ae_all_iff.mpr hfit1] with p hp hf
    exact hf (lab p.1) hp
  · filter_upwards [hmem, ae_all_iff.mpr hfit2] with p hp hf
    exact hf (lab p.1) hp
  · intro z3 z0
    obtain ⟨G, hcard, hG⟩ := hcoarse z3 z0
    refine ⟨G, hcard, ?_⟩
    filter_upwards [hmem, ae_all_iff.mpr hG] with p hp hG'
    exact hG' (lab p.1) hp
  · intro z3 z0 γ
    obtain ⟨F, hcard, hF⟩ := hoffset1 z3 z0 γ
    refine ⟨F, hcard, ?_⟩
    filter_upwards [hmem, ae_all_iff.mpr hF] with p hp hF'
    exact hF' (lab p.1) hp
  · intro z3 z0 γ
    obtain ⟨F, hcard, hF⟩ := hoffset2 z3 z0 γ
    refine ⟨F, hcard, ?_⟩
    filter_upwards [hmem, ae_all_iff.mpr hF] with p hp hF'
    exact hF' (lab p.1) hp

end BlockPrefix

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
