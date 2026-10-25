-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/SevenCells.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/SevenCells.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.GroupWitness
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.GeneralPositionSampling

/-!
# Seven directions and tubes from charged cells

A cell charged by a velocity bin carries a tube of certified group points through the cell
with a velocity in that bin (the producer's realization). For any point `u` of the cell and the
lifted bin centre `p = (1, centre)`, that tube is a `CertifiedTubeWitness` at `(u, p)` with
precision `max(cell diameter, bin width)`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial
open GeneralPositionSampling

lemma norm_lift_sub (v c : EuclideanSpace ℝ (Fin 2)) : ‖lift v - lift c‖ = ‖v - c‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [lift, Fin.sum_univ_three, Fin.sum_univ_two]

lemma norm_sub_le_of_coords {v c : EuclideanSpace ℝ (Fin 2)} {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ i, |v i - c i| ≤ w / 2) : ‖v - c‖ ≤ w := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 := h 0
  have h1 := h 1
  have hsq0 : ‖(v - c) 0‖ ^ 2 ≤ (w / 2) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    simpa using sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
  have hsq1 : ‖(v - c) 1‖ ^ 2 ≤ (w / 2) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    simpa using sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  rw [Real.sqrt_le_left hw]
  nlinarith

lemma norm_lift_le {v : EuclideanSpace ℝ (Fin 2)} {R At : ℝ} (hAt : 0 ≤ At)
    (hv : ∀ i, |v i| ≤ R) (hR : 1 + 2 * R ^ 2 ≤ At ^ 2) : ‖lift v‖ ≤ At := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left hAt]
  simp only [lift, Fin.sum_univ_three, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Real.norm_eq_abs, sq_abs]
  have h0 : (v 0) ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hv 0) 2
  have h1 : (v 1) ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hv 1) 2
  norm_num
  linarith

/-- A tube through a charged cell is a certified tube witness at every point of the cell. -/
theorem certifiedTube_of_cell {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly}
    {εfit A₁ σ Vc At θ h hc w R : ℝ} (hw : 0 < w) (hAt : 0 ≤ At)
    (hR : 1 + 2 * (R + w) ^ 2 ≤ At ^ 2) (hch : hc ≤ h) (hwh : w ≤ h)
    {cellS : Set Base} (hdiam : ∀ u ∈ cellS, ∀ y ∈ cellS, ‖u - y‖ ≤ hc)
    {β : Fin 2 → ℤ} (hcen : ∀ c, |binCenter w β c| ≤ R + w / 2)
    {u : Base} (hu : u ∈ cellS)
    (hreal : ∃ y ∈ cellS, ∃ v ∈ bin w β, ∃ (w₀ w₁ : ℝ) (Et : Set ℝ),
      y ∈ closedBall (0 : Base) 1 ∧ MeasurableSet Et ∧ Et ⊆ Icc (-1) 1 ∧
      ENNReal.ofReal θ ≤ volume Et ∧
      ∀ t ∈ Et, CertifiedGroupPoint S0 P0 Sc εfit A₁ σ Vc
        (y + t • ((8 * At)⁻¹ • lift v)) (w₀ + w₁ * t)) :
    CertifiedTubeWitness S0 P0 Sc εfit A₁ σ Vc At θ h u (lift (binCenter w β)) := by
  obtain ⟨y, hy, v, hv, w₀, w₁, Et, hy1, hEt, hEtsub, hEtvol, hpts⟩ := hreal
  have hcoord : ∀ c, |v c - binCenter w β c| ≤ w / 2 := abs_sub_binCenter_le hw hv
  have hvR : ∀ c, |v c| ≤ R + w := by
    intro c
    have h1 := hcoord c
    have h2 := hcen c
    have := abs_sub_abs_le_abs_sub (v c) (binCenter w β c)
    have : |v c| ≤ |v c - binCenter w β c| + |binCenter w β c| := by
      have := abs_add_le (v c - binCenter w β c) (binCenter w β c)
      simpa using this
    linarith
  refine ⟨y, lift v, w₀, w₁, Et, hy1, norm_lift_le hAt hvR hR, (hdiam u hu y hy).trans hch,
    ?_, hEt, hEtsub, hEtvol, hpts⟩
  rw [norm_sub_rev, norm_lift_sub]
  exact (norm_sub_le_of_coords hw.le hcoord).trans hwh

/-- The lifted bin centres are admissible sampled directions. -/
theorem lift_binCenter_direction {w R At : ℝ} (hAt : 0 ≤ At) (hw : 0 ≤ w)
    (hR : 1 + 2 * (R + w) ^ 2 ≤ At ^ 2) {β : Fin 2 → ℤ}
    (hcen : ∀ c, |binCenter w β c| ≤ R + w / 2) :
    lift (binCenter w β) 0 = 1 ∧ ‖lift (binCenter w β)‖ ≤ At := by
  exact ⟨lift_zero _, norm_lift_le (R := R + w) hAt (fun c => (hcen c).trans (by linarith)) hR⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial
open GeneralPositionSampling
open scoped ENNReal

/-- The seven sampled directions and the common base set of the certified exit, from a cell
decomposition of the zoomed unit ball whose conditional velocity laws are broad and dominated
by one palette, with a base density cap, and whose positive-mass velocity bins are realized by
tubes of certified group points through the cell. -/
theorem seven_directions_of_cells {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly}
    {εfit A₁ σ Vc At A0 θ h hc : ℝ} {ι : Type*} [Fintype ι]
    (cell : ι → Set Base) (hcell : ∀ s, MeasurableSet (cell s))
    (hdisj : Pairwise (Function.onFun Disjoint cell))
    (hcellBall : ∀ s, cell s ⊆ closedBall (0 : Base) 1)
    (hdiam : ∀ s, ∀ u ∈ cell s, ∀ y ∈ cell s, ‖u - y‖ ≤ hc)
    (m : ι → ℝ≥0∞) (βc : ℝ≥0∞) (hcap : ∀ s, m s ≤ βc * volume (cell s))
    (μ : ι → Measure (EuclideanSpace ℝ (Fin 2))) [∀ s, IsProbabilityMeasure (μ s)]
    (π : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure π] (hπ0 : π univ ≠ 0)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hdom : ∀ s, μ s ≤ K • π)
    {δ R w : ℝ} (hδ : 0 < δ) (hw : 0 < w) {κ τ : ℝ≥0∞}
    (hb : ∀ s, StripBreadth (μ s) δ κ) (htail : ∀ s, μ s {v | R < ‖v‖} ≤ τ)
    (hgood : 686 * κ + 7 * τ < 1) (hM0 : ∑ s, m s ≠ 0) (hMtop : ∑ s, m s ≠ ∞)
    (hAt : 0 ≤ At) (hR : 1 + 2 * (R + w) ^ 2 ≤ At ^ 2) (hch : hc ≤ h) (hwh : w ≤ h)
    (hdetA : A0⁻¹ ≤ δ ^ 2 - 4 * w * (2 * R + w / 2))
    (hvolA : 2 * K ^ 7 * (βc * ENNReal.ofReal A0⁻¹) ≤
      (1 - (686 * κ + 7 * τ)) * (∑ s, m s) / π univ ^ 7)
    (hβc0 : βc ≠ 0) (hβctop : βc ≠ ∞) (hK0 : K ≠ 0)
    (hreal : ∀ s (β : Fin 2 → ℤ), (∀ c, |binCenter w β c| ≤ R + w / 2) → μ s (bin w β) ≠ 0 →
      ∃ y ∈ cell s, ∃ v ∈ bin w β, ∃ (w₀ w₁ : ℝ) (Et : Set ℝ),
        y ∈ closedBall (0 : Base) 1 ∧ MeasurableSet Et ∧ Et ⊆ Icc (-1) 1 ∧
        ENNReal.ofReal θ ≤ volume Et ∧
        ∀ t ∈ Et, CertifiedGroupPoint S0 P0 Sc εfit A₁ σ Vc
          (y + t • ((8 * At)⁻¹ • lift v)) (w₀ + w₁ * t)) :
    ∃ (p : Fin 7 → Base) (E : Set Base),
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ At) ∧
      (∀ i k l : Fin 7, i ≠ k → i ≠ l → k ≠ l →
        A0⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p k, p l] r) t)|) ∧
      MeasurableSet E ∧ E ⊆ closedBall (0 : Base) 1 ∧ ENNReal.ofReal A0⁻¹ ≤ volume E ∧
      ∀ u ∈ E, ∀ i, CertifiedTubeWitness S0 P0 Sc εfit A₁ σ Vc At θ h u (p i) := by
  obtain ⟨β, E, hEm, hEsub, hdet, hcen, hvol, hcharge⟩ :=
    exists_seven_bins_cells volume cell hcell hdisj m βc hcap μ π hπ0 hK hdom hδ hw hb htail
      hgood hM0 hMtop
  refine ⟨fun i => lift (binCenter w (β i)), E, fun i => lift_binCenter_direction hAt hw.le hR (hcen i),
    fun i k l hik hil hkl => hdetA.trans (hdet i k l hik hil hkl), hEm, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hEsub hu)
    exact hcellBall s hs
  · -- cancel the positive finite factor `2 K⁷ βc`
    have hfac0 : 2 * K ^ 7 * βc ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hK0)) hβc0
    have hfactop : 2 * K ^ 7 * βc ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hK)) hβctop
    have h1 : 2 * K ^ 7 * βc * ENNReal.ofReal A0⁻¹ ≤ 2 * K ^ 7 * βc * volume E := by
      calc 2 * K ^ 7 * βc * ENNReal.ofReal A0⁻¹ = 2 * K ^ 7 * (βc * ENNReal.ofReal A0⁻¹) := by
            ring
        _ ≤ (1 - (686 * κ + 7 * τ)) * (∑ s, m s) / π univ ^ 7 := hvolA
        _ ≤ 2 * K ^ 7 * (βc * volume E) := hvol
        _ = 2 * K ^ 7 * βc * volume E := by ring
    exact (ENNReal.mul_le_mul_iff_right hfac0 hfactop).mp h1
  · intro u hu i
    obtain ⟨s, hus, hs⟩ := hcharge u hu
    exact certifiedTube_of_cell hw hAt hR hch hwh (hdiam s) (hcen i) hus
      (hreal s (β i) (hcen i) (hs i))

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
