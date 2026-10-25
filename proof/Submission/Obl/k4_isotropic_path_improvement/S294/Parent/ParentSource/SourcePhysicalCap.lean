-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourcePhysicalCap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourcePhysicalCap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourcePhysicalCap.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourcePhysicalCap.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceNativeCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketPhysical
import Submission.Obl.k4_profile_density_bounds.Support
import Submission.Obl.k4_scalar_coefficient_clustering.LiftCells

/-! # Actual physical-cell mass under the original source law -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Scale the accepted scalar floor error to physical cell units. -/
theorem physical_grid_corner_error {mesh value : ℝ} (hmesh : 0 < mesh) {c : ℤ}
    (hcell : ⌊value / mesh⌋ = c) : |value - mesh * (c : ℝ)| ≤ mesh := by
  have hh := k4_scalar_coefficient_clustering.floor_error (value / mesh)
  rw [hcell] at hh
  calc
    _ = |mesh * (c : ℝ) - value| := abs_sub_comm _ _
    _ = |mesh * ((c : ℝ) - value / mesh)| := by congr 1; field_simp
    _ = mesh * |(c : ℝ) - value / mesh| := by rw [abs_mul, abs_of_pos hmesh]
    _ ≤ mesh * 1 := mul_le_mul_of_nonneg_left hh hmesh.le
    _ = _ := mul_one _

/-- A physical cube has an original mass ceiling in the FULL old packet
units. Its hidden-coordinate width is paid by the actual fine original
observation; the spatial volume is the accepted three-dimensional box
volume. No posterior density or counted-set denominator is introduced. -/
theorem source_physical_cell_mass_cap
    {d : Native.ProblemData} (hd : d.Valid) {k : ℕ} {p : Native.PathData (d.W k)}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (a : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev a)))
    {mesh : ℝ} (hmesh : 0 < mesh)
    (hwidth : δ (d.N k) (p.r (p.lev a)) * mesh ≤ δ (d.N k) r')
    (ρ : Measure Event) (hρ : ρ ≤ d.μ k (p.γ a)) (M : ENNReal) (c : Fin 4 → ℤ)
    (hF : ∀ᵐ q ∂ρ, q ∈ p.F a)
    (hcell : ∀ᵐ q ∂ρ, ∀ j, ⌊packetPhysicalPoint (d.N k) p a q j / mesh⌋ = c j)
    (htypical : ∀ᵐ q ∂ρ, d.g k (p.γ a) r'
      (obs (d.B k (p.γ a)) (δ (d.N k) r') q) ≤ M) :
    (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))⁻¹ *
        ρ univ ≤
      ((M * ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
        ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r (p.lev a)))) *
          ENNReal.ofReal ((2 * mesh) ^ 3) := by
  let delta := δ (d.N k) (p.r (p.lev a))
  let center : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 (fun j => mesh * (c j : ℝ))
  let U := k4_profile_density_bounds.baseBox center mesh
  have hdelta : 0 < delta := by dsimp [delta, δ]; positivity
  have hK : 1 ≤ max p.κ (d.K k) := hp.1.trans (le_max_left _ _)
  have ha' : 0 ≤ δ (d.N k) r' := by unfold δ; positivity
  have hband : ∀ᵐ q ∂ρ,
      |MvPolynomial.eval (x q.1 q.2) (p.R a) - delta * mesh * (c 3 : ℝ)| ≤
        max p.κ (d.K k) * δ (d.N k) r' := by
    filter_upwards [hcell] with q hq
    have hs : |packetSignal (d.N k) p a q - mesh * (c 3 : ℝ)| ≤ mesh :=
      physical_grid_corner_error hmesh (hq 3)
    have hid : MvPolynomial.eval (x q.1 q.2) (p.R a) = delta * packetSignal (d.N k) p a q := by
      change MvPolynomial.eval (xp q.1 q.2) (p.R a) =
        delta * (delta⁻¹ * MvPolynomial.eval (xp q.1 q.2) (p.R a))
      rw [← mul_assoc, mul_inv_cancel₀ hdelta.ne', one_mul]
    calc
      _ = delta * |packetSignal (d.N k) p a q - mesh * (c 3 : ℝ)| := by
        rw [hid, mul_assoc delta mesh, ← mul_sub, abs_mul, abs_of_pos hdelta]
      _ ≤ delta * mesh := mul_le_mul_of_nonneg_left hs hdelta.le
      _ ≤ δ (d.N k) r' := hwidth
      _ ≤ _ := le_mul_of_one_le_left ha' hK
  have hbase : ∀ᵐ q ∂ρ, packetBase p a q ∈ U := by
    filter_upwards [hcell] with q hq
    apply (k4_profile_density_bounds.mem_baseBox_iff center mesh (packetBase p a q)).mpr
    intro j
    have hj : packetPhysicalPoint (d.N k) p a q j.castSucc = packetBase p a q j := by
      fin_cases j <;> rfl
    have hh : ⌊packetBase p a q j / mesh⌋ = c j.castSucc := by
      rw [← hj]
      exact hq j.castSucc
    exact physical_grid_corner_error hmesh hh
  have hcap := source_native_signal_cap_in_old_units hd hp a r' hr' hr'L hscale ρ hρ M
    (delta * mesh * (c 3 : ℝ)) hF hband htypical
  change (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))⁻¹ •
      ρ.map (packetBase p a) ≤ _ at hcap
  have hUm : MeasurableSet U := k4_profile_density_bounds.measurableSet_baseBox center mesh
  have hmass : (ρ.map (packetBase p a)) U = ρ univ := by
    rw [Measure.map_apply (measurable_packetBase p a) hUm]
    apply measure_congr
    filter_upwards [hbase] with q hq
    exact propext (iff_true_intro hq)
  have hvol : volume U = ENNReal.ofReal ((2 * mesh) ^ 3) :=
    k4_profile_density_bounds.volume_baseBox center mesh hmesh.le
  simpa only [Measure.smul_apply, smul_eq_mul, hmass, hvol] using hcap U

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
