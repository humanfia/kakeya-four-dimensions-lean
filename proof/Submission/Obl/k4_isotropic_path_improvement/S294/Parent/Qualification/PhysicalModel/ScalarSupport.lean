-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.ScalarSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/ScalarSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenScalarSupport.lean.
The bounded quadratic physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenScalarSupport.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ScalarLocalCover
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set Metric
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

def zoomScalarSet (p : PhysicalModel) (E : Set Ev) (ρ : ℝ)
    (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (t : ℝ) : Set ℝ :=
  {s | ∃ l : Ln, (l,t) ∈ E ∧
    Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t = s}

/-- Finite tested ORIGINAL strip widths suffice for every resolution
of the exact scalar-normal SS interface, including outer radii R>1.
All finite covers and the bound on the scalar range are constructed. -/
theorem scalar_support_of_original_strip_counts (p : PhysicalModel) (E : Set Ev)
    (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (W : Finset ℝ)
    (ρ b B η ζ Λ A d Krow : ℝ)
    (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hB : 0 ≤ B) (hη : 0 ≤ η) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hΛ : 1 ≤ Λ) (hA : 0 ≤ A) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hKrow : 1 ≤ Krow)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hdiam : ∀ z ∈ E, ∀ i, |p.scalarCoefficients z.1 i - center i| ≤ ρ)
    (hrowB : ∀ C j, |row C j| ≤ B)
    (hF : ∀ z ∈ E, ‖F z.2‖ ≤ Krow)
    (hwidth : ∀ w ∈ W, 0 < w)
    (hsmall : ∀ w ∈ W, 4 * η * ρ + (1 + 3 * B) * b ≤ w / 2)
    (hrow : ∀ w ∈ W, ∀ z ∈ E, ∀ i : Fin 2,
      |row (p.stripLabel b ρ w row z).1 i.succ - F z.2 i| ≤ η)
    (hscales : ∀ r : ℝ, ζ ≤ r → r ≤ 1 →
      ∃ w ∈ W, w ≤ ρ * r ∧ ρ * r ≤ Λ * w)
    (hcount : ∀ w ∈ W, ∀ t ∈ Icc (0 : ℝ) 1, ∀ R a : ℝ,
      w ≤ ρ * R → R ≤ 1 → ∀ C : Fin 4 → ℤ, ∀ N : Finset ℤ,
      (∀ n ∈ N, ∃ l : Ln, (l,t) ∈ E ∧ p.stripLabel b ρ w row (l,t) = (C,n) ∧
        Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t ∈ Icc a (a+R)) →
      (N.card : ℝ) ≤ A * ((ρ * R) / w) ^ d) :
    ∀ t, IntervalAD ζ d
      ((2 * (4 * Krow ^ 2 + 3 * Krow) + 2) * ((27:ℝ)^4 * A * Λ))
      (p.zoomScalarSet E ρ center F t) := by
  intro t
  let S := p.zoomScalarSet E ρ center F t
  let Bscalar := 4 * Krow ^ 2 + 3 * Krow
  let C₀ := (27:ℝ)^4 * A
  let C₁ := C₀ * Λ
  have hBscalar : 0 ≤ Bscalar := by dsimp [Bscalar]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hconstant : 0 ≤ (2 * Bscalar + 2) * C₁ := by positivity
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hbounded : ∀ s ∈ S, |s| ≤ Bscalar := by
      rintro s ⟨l,hl,rfl⟩
      have hc : ∀ i, |Jets2.zoomCoefficients ρ center (p.scalarCoefficients l) i| ≤ Krow := by
        intro i
        exact ((norm_le_pi_norm _ i).trans (Jets2.zoom_coefficients_bound ρ hρ center
          (p.scalarCoefficients l) (hdiam (l,t) hl))).trans hKrow
      exact Jets2.abs_zS_le hc ht (hF (l,t) hl)
    have hlocal : ∀ r R a : ℝ, ζ ≤ r → r ≤ R → R ≤ 1 →
        ∃ (m : ℕ) (c : Fin m → ℝ),
          S ∩ Icc a (a+R) ⊆ ⋃ j, closedBall (c j) r ∧ (m : ℝ) ≤ C₁ * (R/r)^d := by
      intro r R a hζr hrR hR1
      have hr : 0 < r := hζ.trans_le hζr
      have hR : 0 < R := hr.trans_le hrR
      obtain ⟨w,hw,hwr,hround⟩ := hscales r hζr (hrR.trans hR1)
      have hwpos := hwidth w hw
      have hwR : w ≤ ρ * R := hwr.trans (mul_le_mul_of_nonneg_left hrR hρ.le)
      obtain ⟨m,c,hcover,hcard⟩ := p.scalar_local_cover_of_original_strips E center F row
        ρ b B η w r R t a A d hρ hb hbρ hB hη hA hR.le hwpos ht hwr
        (hsmall w hw) (fun l hl => hdiam (l,t) hl) hrowB
        (fun l hl => hrow w hw (l,t) hl) (hcount w hw t ht R a hwR hR1)
      have hratio : (ρ * R) / w ≤ Λ * (R / r) := by
        apply (div_le_iff₀ hwpos).mpr
        calc
          ρ * R = (ρ * r) * (R / r) := by field_simp
          _ ≤ (Λ * w) * (R / r) :=
            mul_le_mul_of_nonneg_right hround (div_nonneg hR.le hr.le)
          _ = Λ * (R / r) * w := by ring
      have hpower : ((ρ * R) / w) ^ d ≤ Λ * (R / r) ^ d := by
        calc
          _ ≤ (Λ * (R / r)) ^ d :=
            Real.rpow_le_rpow (by positivity) hratio hd
          _ = Λ ^ d * (R / r) ^ d := Real.mul_rpow (by linarith) (by positivity)
          _ ≤ Λ ^ (1 : ℝ) * (R / r) ^ d :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hΛ hd1)
              (by positivity)
          _ = _ := by rw [Real.rpow_one]
      refine ⟨m,c,hcover,?_⟩
      calc
        (m : ℝ) ≤ C₀ * ((ρ * R) / w) ^ d := hcard
        _ ≤ C₀ * (Λ * (R / r) ^ d) := mul_le_mul_of_nonneg_left hpower hC₀
        _ = C₁ * (R / r) ^ d := by dsimp [C₁]; ring
    have hAD := intervalAD_of_bounded_local S ζ d C₁ Bscalar hζ hζ1 hd hC₁ hBscalar hbounded hlocal
    intro r R a hζr hrR
    obtain ⟨m,c,hcover,hcard⟩ := hAD r R a hζr hrR
    refine ⟨m,c,hcover,hcard.trans ?_⟩
    have hceil : (((⌈2 * Bscalar⌉₊ + 1 : ℕ) : ℝ)) ≤ 2 * Bscalar + 2 := by
      have hh := Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hBscalar)
      push_cast
      linarith
    have hcoef : (⌈2 * Bscalar⌉₊ + 1 : ℕ) * C₁ ≤ (2 * Bscalar + 2) * C₁ :=
      mul_le_mul_of_nonneg_right hceil hC₁
    exact mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg (div_nonneg ((hζ.trans_le hζr).le.trans hrR)
        (hζ.trans_le hζr).le) d)
  · have hempty : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro s ⟨l,hl,_⟩
      exact ht (htime (l,t) hl)
    change IntervalAD ζ d ((2 * Bscalar + 2) * C₁) S
    rw [hempty]
    intro r R a hζr hrR
    refine ⟨0,Fin.elim0,by simp,?_⟩
    have hr := hζ.trans_le hζr
    simpa only [Nat.cast_zero] using
      mul_nonneg hconstant (Real.rpow_nonneg (div_nonneg (hr.le.trans hrR) hr.le) d)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
