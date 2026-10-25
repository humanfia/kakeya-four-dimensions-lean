-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Observations, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Observations.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Observations.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Observations.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Graph
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Model
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedSupport

set_option autoImplicit false

/-!
# The sliced observation model in version 2 (paper `tex-05`, display `a04:sliced-model`)

The `j = 2` counterpart of `exists_actual_block_observations` of o078 (session x0662, branch
`x0662` at `f2bac599`, `ScalarBlockObservations.lean`).  In one sliced starting group (anchor time
`t₀`, scalar bin `b.1` of width `H`, slice `b.2` of width `p` in `y_{k'}`), the normalized
observations, shifted by the time-only term `φ_{k'}(u) · (p b.2)` of the slice corner, follow the
planar model of x0662's kernel:
`Obs'(u, l) = Z l + u G(v l) + f(u) v l + O(28 K² p)`, with `v = 3K² y_k(t₀)`,
`Z = (S(t₀) - H b.1)/H ∈ [0, 1]`, `f(u) = -φ_k(u)/(3K²)` (`1`-Lipschitz, `f 0 = 0`), and `G` the
`1`-Lipschitz residual graph of `V2Graph`.  The shifted supports are translates of the normalized
supports, hence `IntervalAD` at scale `p`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The normalized row increment `φ(u) = (g(t₀ + H u) - F(t₀))/H`. -/
def normRow (g F : ℝ → Fin 2 → ℝ) (t₀ H u : ℝ) : Fin 2 → ℝ := H⁻¹ • (g (t₀ + H * u) - F t₀)

/-- The time-only shift by the slice corner. -/
def sliceShift (g F : ℝ → Fin 2 → ℝ) (t₀ H p : ℝ) (k : Fin 2) (b : ℤ × ℤ) (u : ℝ) : ℝ :=
  normRow g F t₀ H u (Fin.rev k) * (p * b.2)

/-- The shifted normalized observation. -/
def slicedObs (c : Λ → Fin 7 → ℝ) (g F : ℝ → Fin 2 → ℝ) (t₀ H p : ℝ) (k : Fin 2) (b : ℤ × ℤ)
    (q : ℝ × Λ) : ℝ :=
  (zS F (c q.2) (t₀ + H * q.1) - H * b.1) / H + sliceShift g F t₀ H p k b q.1

/-- The normalized starting scalar. -/
def slicedStart (c : Λ → Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (t₀ H : ℝ) (b : ℤ × ℤ) (l : Λ) : ℝ :=
  (zS F (c l) t₀ - H * b.1) / H

/-- The scaled fitted coordinate. -/
def scaledFitted (c : Λ → Fin 7 → ℝ) (K t₀ : ℝ) (k : Fin 2) (l : Λ) : ℝ :=
  graphScale K * zy (c l) t₀ k

/-- The normalized fitted row component. -/
def fittedRow (g F : ℝ → Fin 2 → ℝ) (t₀ H K : ℝ) (k : Fin 2) (u : ℝ) : ℝ :=
  -normRow g F t₀ H u k / graphScale K

/-- The shifted normalized supports. -/
def slicedSupport (c : Λ → Fin 7 → ℝ) (g F : ℝ → Fin 2 → ℝ) (E : Set (Λ × ℝ)) (t₀ H p : ℝ)
    (k : Fin 2) (b : ℤ × ℤ) (u : ℝ) : Set ℝ :=
  (fun z => H⁻¹ * z + (-(b.1 : ℝ) + sliceShift g F t₀ H p k b u)) ''
    scalarSupport c F E (t₀ + H * u)

theorem slicedSupport_AD {c : Λ → Fin 7 → ℝ} {g F : ℝ → Fin 2 → ℝ} {E : Set (Λ × ℝ)}
    {ζ d C t₀ H p : ℝ} {k : Fin 2} {b : ℤ × ℤ} (hζ : 0 < ζ) (hH : 0 < H) (hfloor : ζ ≤ H * p)
    (hS : ∀ t, IntervalAD ζ d C (scalarSupport c F E t)) (u : ℝ) :
    IntervalAD p d C (slicedSupport c g F E t₀ H p k b u) := by
  have h := intervalAD_affine (a := H⁻¹) (b := -(b.1 : ℝ) + sliceShift g F t₀ H p k b u) hζ
    (inv_pos.mpr hH) (hS (t₀ + H * u))
  have hf : H⁻¹ * ζ ≤ p := by
    have hh : ζ / H ≤ p := (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hfloor)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  intro r R a hpr hrR
  exact h r R a (hf.trans hpr) hrR

theorem slicedObs_mem {c : Λ → Fin 7 → ℝ} {g F : ℝ → Fin 2 → ℝ} {E : Set (Λ × ℝ)}
    {t₀ H p : ℝ} {k : Fin 2} {b : ℤ × ℤ} (hH : 0 < H) (u : ℝ) (l : Λ)
    (hl : (l, t₀ + H * u) ∈ E) :
    slicedObs c g F t₀ H p k b (u, l) ∈ slicedSupport c g F E t₀ H p k b u := by
  refine ⟨zS F (c l) (t₀ + H * u), ⟨l, hl, rfl⟩, ?_⟩
  simp only [slicedObs]
  field_simp
  ring

theorem slicedStart_eq_obs {c : Λ → Fin 7 → ℝ} {g F : ℝ → Fin 2 → ℝ} {t₀ H p : ℝ}
    {k : Fin 2} {b : ℤ × ℤ} (hg : g t₀ = F t₀) (l : Λ) :
    slicedObs c g F t₀ H p k b (0, l) = slicedStart c F t₀ H b l := by
  simp [slicedObs, slicedStart, sliceShift, normRow, hg]

/-- **The sliced observation model.** -/
theorem exists_v2_block_observations {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {K ζ d H p t₀ : ℝ} (h : UpperHyp ν c E F K ζ d) (hK : 1 ≤ K)
    (hH : 0 < H) (hH1 : H ≤ 1) (hζ : 0 ≤ ζ) (hζH : ζ ≤ H ^ 2) (hHp : H ≤ p) (hp1 : p ≤ 1)
    (ht₀ : t₀ ∈ activeTimes E) (k : Fin 2) (b : ℤ × ℤ) :
    ∃ (g : ℝ → Fin 2 → ℝ) (G : ℝ → ℝ), g t₀ = F t₀ ∧
      (∀ t ∈ activeTimes E, ‖g t - F t‖ ≤ 2 * K * ζ) ∧
      (∀ i, Continuous (fun t => g t i)) ∧
      fittedRow g F t₀ H K k 0 = 0 ∧
      (∀ u u', |fittedRow g F t₀ H K k u - fittedRow g F t₀ H K k u'| ≤ |u - u'|) ∧
      (∀ s s', |G s - G s'| ≤ |s - s'|) ∧
      (∀ l ∈ slicedLabels c F E t₀ H p k b,
        |scaledFitted c K t₀ k l| ≤ 6 * K ^ 3 ∧ |G (scaledFitted c K t₀ k l)| ≤ 17 * K ^ 2 ∧
        slicedStart c F t₀ H b l ∈ Icc (0 : ℝ) 1) ∧
      ∀ u l, |u| ≤ 1 → l ∈ slicedLabels c F E t₀ H p k b → (l, t₀ + H * u) ∈ E →
        |slicedObs c g F t₀ H p k b (u, l)| ≤ 48 * K ^ 2 ∧
        |slicedObs c g F t₀ H p k b (u, l) -
          (slicedStart c F t₀ H b l + u * G (scaledFitted c K t₀ k l) +
            fittedRow g F t₀ H K k u * scaledFitted c K t₀ k l)| ≤ 28 * K ^ 2 * p := by
  have hK0 : 0 ≤ K := by linarith
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have hp : 0 < p := hH.trans_le hHp
  have hL : 0 < graphScale K := by unfold graphScale; positivity
  have hKL : K ≤ graphScale K := by unfold graphScale; nlinarith
  have hζH' : ζ ≤ H := hζH.trans (by nlinarith)
  obtain ⟨g, hgc, hgnear, hgLip, hgbound, hgcont⟩ :=
    exists_v2_row_approximant hK0 hH ht₀ h.active_row_comparison
  obtain ⟨G, hG, hGnear, hGbound⟩ := exists_sliced_residual_graph h hK hH hH1 hζH' hp hp1 t₀ k b
  have hφ : ∀ u, ‖normRow g F t₀ H u‖ ≤ K * |u| := hgbound
  have hfzero : fittedRow g F t₀ H K k 0 = 0 := by
    simp [fittedRow, normRow, hgc]
  have hfLip : ∀ u u', |fittedRow g F t₀ H K k u - fittedRow g F t₀ H K k u'| ≤ |u - u'| := by
    intro u u'
    have h1 := hgLip k u u'
    have e : fittedRow g F t₀ H K k u - fittedRow g F t₀ H K k u' =
        -((g (t₀ + H * u) k - F t₀ k) / H - (g (t₀ + H * u') k - F t₀ k) / H) / graphScale K := by
      simp only [fittedRow, normRow, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp; ring
    rw [e, abs_div, abs_neg, abs_of_pos hL, div_le_iff₀ hL]
    nlinarith [abs_nonneg (u - u')]
  have hbds : ∀ l ∈ slicedLabels c F E t₀ H p k b,
      |scaledFitted c K t₀ k l| ≤ 6 * K ^ 3 ∧ |G (scaledFitted c K t₀ k l)| ≤ 17 * K ^ 2 ∧
      slicedStart c F t₀ H b l ∈ Icc (0 : ℝ) 1 := by
    intro l hl
    have hy := (h.active_bounds hl.1).2.1 k
    refine ⟨?_, hGbound l hl, ?_⟩
    · unfold scaledFitted graphScale
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 * K ^ 2)]
      nlinarith
    · have hcode := hl.2
      simp only [slicedCode, Prod.ext_iff] at hcode
      have hz := (mesh_lower_endpoint hH hcode.1).1
      exact ⟨div_nonneg (by linarith [hz.1]) hH.le, (div_le_iff₀ hH).mpr (by linarith [hz.2])⟩
  refine ⟨g, G, hgc, hgnear, hgcont, hfzero, hfLip, hG, hbds, ?_⟩
  intro u l hu hl hcur
  have hcoef := h.coefficients _ hl.1
  have hbd := h.active_bounds hl.1
  have ht₀1 : t₀ ∈ Icc (0 : ℝ) 1 := (h.unit_time hl.1).2
  have hy0 : ‖zy (c l) t₀‖ ≤ 2 * K := norm_zy_le hcoef ht₀1
  have hgcur : ‖g (t₀ + H * u) - F (t₀ + H * u)‖ ≤ 2 * K * ζ := hgnear _ ⟨l, hcur⟩
  have hmodel := v2_quadratic_model_error (c l) (F t₀) (F (t₀ + H * u)) (g (t₀ + H * u))
    (base := H * b.1) hH hK0 hζ hζH hH1 hu (hcoef 2) (norm_zv_le hcoef) hy0
    ((hφ u).trans (by nlinarith [abs_nonneg u])) hgcur
  -- names
  set Obs := slicedObs c g F t₀ H p k b (u, l) with hObs
  set Z := slicedStart c F t₀ H b l
  set R := zR F (c l) t₀
  set φ := normRow g F t₀ H u
  set v := scaledFitted c K t₀ k l
  have hRdef : R = c l 1 + 2 * c l 2 * t₀ - F t₀ ⬝ᵥ zv (c l) := rfl
  have hφy : φ ⬝ᵥ zy (c l) t₀ = φ k * zy (c l) t₀ k + φ (Fin.rev k) * zy (c l) t₀ (Fin.rev k) :=
    dot_split _ _ k
  -- the slice
  have hcode := hl.2
  simp only [slicedCode, Prod.ext_iff] at hcode
  have hw := mesh_lower_endpoint hp hcode.2
  have hwd : |zy (c l) t₀ (Fin.rev k) - p * b.2| ≤ p := hw.2.le
  have hφk' : |φ (Fin.rev k)| ≤ K := by
    have := (abs_le_norm φ (Fin.rev k)).trans (hφ u)
    nlinarith [abs_nonneg u]
  have hslice : |φ (Fin.rev k) * (zy (c l) t₀ (Fin.rev k) - p * b.2)| ≤ K * p := by
    rw [abs_mul]; exact mul_le_mul hφk' hwd (abs_nonneg _) hK0
  have hR := hGnear l hl
  have hdecomp : Obs - (Z + u * G v + fittedRow g F t₀ H K k u * v) =
      ((zS F (c l) (t₀ + H * u) - H * b.1) / H -
        ((zS F (c l) t₀ - H * b.1) / H + u * R - φ ⬝ᵥ zy (c l) t₀)) +
      u * (R - G v) - φ (Fin.rev k) * (zy (c l) t₀ (Fin.rev k) - p * b.2) := by
    simp only [hObs, slicedObs, sliceShift, Z, slicedStart, fittedRow, v, scaledFitted, hφy]
    have hL' : graphScale K ≠ 0 := hL.ne'
    field_simp
    ring
  have hmodel' : |(zS F (c l) (t₀ + H * u) - H * b.1) / H -
      ((zS F (c l) t₀ - H * b.1) / H + u * R - φ ⬝ᵥ zy (c l) t₀)| ≤ H * (K + 14 * K ^ 2) := by
    simpa only [zS, hRdef, φ, normRow] using hmodel
  have huR : |u * (R - G v)| ≤ 6 * K ^ 2 * (p + H) := by
    rw [abs_mul]
    exact (mul_le_mul hu hR (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have herr : |Obs - (Z + u * G v + fittedRow g F t₀ H K k u * v)| ≤ 28 * K ^ 2 * p := by
    rw [hdecomp]
    have h1 := abs_sub ((zS F (c l) (t₀ + H * u) - H * b.1) / H -
        ((zS F (c l) t₀ - H * b.1) / H + u * R - φ ⬝ᵥ zy (c l) t₀) + u * (R - G v))
      (φ (Fin.rev k) * (zy (c l) t₀ (Fin.rev k) - p * b.2))
    have h2 := abs_add_le ((zS F (c l) (t₀ + H * u) - H * b.1) / H -
        ((zS F (c l) t₀ - H * b.1) / H + u * R - φ ⬝ᵥ zy (c l) t₀)) (u * (R - G v))
    have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
    have a1 : H * K ≤ K ^ 2 * p := mul_le_mul hHp hKsq hK0 hp.le |>.trans_eq (mul_comm _ _)
    have a2 : H * K ^ 2 ≤ K ^ 2 * p := (mul_le_mul_of_nonneg_right hHp hK2).trans_eq (mul_comm _ _)
    have hKp : K * p ≤ K ^ 2 * p := mul_le_mul_of_nonneg_right hKsq hp.le
    have hm : H * (K + 14 * K ^ 2) = H * K + 14 * (H * K ^ 2) := by ring
    have hu6 : 6 * K ^ 2 * (p + H) = 6 * (K ^ 2 * p) + 6 * (H * K ^ 2) := by ring
    rw [hm] at hmodel'
    rw [hu6] at huR
    linarith
  refine ⟨?_, herr⟩
  -- the size of the observation
  have hZ1 : |Z| ≤ 1 := by
    have hz := (hbds l hl).2.2
    exact abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  have hGv : |G v| ≤ 17 * K ^ 2 := (hbds l hl).2.1
  have hφk : |φ k| ≤ K := (abs_le_norm φ k).trans ((hφ u).trans (mul_le_of_le_one_right hK0 hu))
  have hv : |fittedRow g F t₀ H K k u * v| ≤ 2 * K ^ 2 := by
    have e : fittedRow g F t₀ H K k u * v = -(φ k * zy (c l) t₀ k) := by
      simp only [fittedRow, v, scaledFitted, φ]
      field_simp
    rw [e, abs_neg, abs_mul]
    calc |φ k| * |zy (c l) t₀ k| ≤ K * (2 * K) := mul_le_mul hφk (hbd.2.1 k) (abs_nonneg _) hK0
      _ = 2 * K ^ 2 := by ring
  have huG : |u * G v| ≤ 17 * K ^ 2 := by
    rw [abs_mul]; exact (mul_le_mul hu hGv (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hmodelK : 28 * K ^ 2 * p ≤ 28 * K ^ 2 := by
    have := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 28 * K ^ 2 by positivity)
    linarith
  have h0 := abs_sub_abs_le_abs_sub Obs (Z + u * G v + fittedRow g F t₀ H K k u * v)
  have h3 := abs_add_le (Z + u * G v) (fittedRow g F t₀ H K k u * v)
  have h4 := abs_add_le Z (u * G v)
  -- `|Obs| ≤ 1 + 17 K² + 2 K² + 28 K² p ≤ 48 K²`
  have h1K : 1 ≤ K ^ 2 := by nlinarith
  linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
