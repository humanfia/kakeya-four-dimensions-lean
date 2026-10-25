-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalAnisotropicCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalAnisotropicCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalAnisotropicCaps.lean.
All earlier source attributions below are retained. -/
-- Generalizes this obligation's SourcePhysicalCap.lean, whose source is
-- this LOT tree, o204/x0749, commit e4d9e4b8c9b3,
-- Submission/Obl/k4_uniform_sampled_isotropic_branches/SourcePhysicalCap.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourcePhysicalCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PreparedSourceCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalCodePruning

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open scoped ENNReal

noncomputable section

/-- The midpoint of a literal half-open grid interval has half-width error. -/
theorem physical_grid_midpoint_error {mesh value : ℝ} (hmesh : 0 < mesh) {c : ℤ}
    (hcell : ⌊value / mesh⌋ = c) :
    |value - mesh * ((c : ℝ) + 1 / 2)| ≤ mesh / 2 := by
  have hlo := Int.floor_le (value / mesh)
  have hhi := Int.lt_floor_add_one (value / mesh)
  rw [hcell] at hlo hhi
  have hlo' := mul_le_mul_of_nonneg_right hlo hmesh.le
  have hhi' := mul_lt_mul_of_pos_right hhi hmesh
  rw [div_mul_cancel₀ _ hmesh.ne'] at hlo' hhi'
  rw [abs_le]
  constructor <;> nlinarith

/-- Original physical planks may have independent base and hidden widths.
The midpoint of the hidden bin pays only half its width to the original
pure ceiling; all references remain the full old assignment and clock. -/
theorem source_anisotropic_cell_mass_cap
    {d : Native.ProblemData} (hd : d.Valid) {k : ℕ} {p : Native.PathData (d.W k)}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (a : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev a)))
    {baseMesh hidden : ℝ} (hmesh : 0 < baseMesh) (hhidden : 0 < hidden)
    (hwidth : δ (d.N k) (p.r (p.lev a)) * hidden / 2 ≤ δ (d.N k) r')
    (ρ : Measure Event) (hρ : ρ ≤ d.μ k (p.γ a)) (M : ENNReal) (c : Fin 4 → ℤ)
    (hF : ∀ᵐ q ∂ρ, q ∈ p.F a)
    (hcell : ∀ᵐ q ∂ρ, ∀ j, ⌊packetPhysicalPoint (d.N k) p a q j / (if j = 3 then hidden else baseMesh)⌋ = c j)
    (htypical : ∀ᵐ q ∂ρ, d.g k (p.γ a) r'
      (obs (d.B k (p.γ a)) (δ (d.N k) r') q) ≤ M) :
    (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))⁻¹ *
        ρ univ ≤
      ((M * ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
        ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r (p.lev a)))) *
          ENNReal.ofReal ((2 * baseMesh) ^ 3) := by
  let delta := δ (d.N k) (p.r (p.lev a))
  let center : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 (fun j => baseMesh * (c j : ℝ))
  let U := k4_profile_density_bounds.baseBox center baseMesh
  have hdelta : 0 < delta := by dsimp [delta, δ]; positivity
  have hK : 1 ≤ max p.κ (d.K k) := hp.1.trans (le_max_left _ _)
  have ha' : 0 ≤ δ (d.N k) r' := by unfold δ; positivity
  have hband : ∀ᵐ q ∂ρ,
      |MvPolynomial.eval (x q.1 q.2) (p.R a) - delta * (hidden * ((c 3 : ℝ) + 1 / 2))| ≤
        max p.κ (d.K k) * δ (d.N k) r' := by
    filter_upwards [hcell] with q hq
    have hs : |packetSignal (d.N k) p a q - hidden * ((c 3 : ℝ) + 1 / 2)| ≤ hidden / 2 :=
      physical_grid_midpoint_error hhidden (hq 3)
    have hid : MvPolynomial.eval (x q.1 q.2) (p.R a) = delta * packetSignal (d.N k) p a q := by
      change MvPolynomial.eval (xp q.1 q.2) (p.R a) =
        delta * (delta⁻¹ * MvPolynomial.eval (xp q.1 q.2) (p.R a))
      rw [← mul_assoc, mul_inv_cancel₀ hdelta.ne', one_mul]
    calc
      _ = delta * |packetSignal (d.N k) p a q - hidden * ((c 3 : ℝ) + 1 / 2)| := by
        rw [hid, ← mul_sub, abs_mul, abs_of_pos hdelta]
      _ ≤ delta * hidden / 2 := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hs hdelta.le
      _ ≤ δ (d.N k) r' := hwidth
      _ ≤ _ := le_mul_of_one_le_left ha' hK
  have hbase : ∀ᵐ q ∂ρ, packetBase p a q ∈ U := by
    filter_upwards [hcell] with q hq
    apply (k4_profile_density_bounds.mem_baseBox_iff center baseMesh (packetBase p a q)).mpr
    intro j
    have hj : packetPhysicalPoint (d.N k) p a q j.castSucc = packetBase p a q j := by
      fin_cases j <;> rfl
    have hh : ⌊packetBase p a q j / baseMesh⌋ = c j.castSucc := by
      rw [← hj]
      have hj3 : (j.castSucc : Fin 4) ≠ 3 := Fin.castSucc_ne_last j
      simpa only [if_neg hj3] using hq j.castSucc
    exact physical_grid_corner_error hmesh hh
  have hcap := source_native_signal_cap_in_old_units hd hp a r' hr' hr'L hscale ρ hρ M
    (delta * (hidden * ((c 3 : ℝ) + 1 / 2))) hF hband htypical
  change (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))⁻¹ •
      ρ.map (packetBase p a) ≤ _ at hcap
  have hUm : MeasurableSet U := k4_profile_density_bounds.measurableSet_baseBox center baseMesh
  have hmass : (ρ.map (packetBase p a)) U = ρ univ := by
    rw [Measure.map_apply (measurable_packetBase p a) hUm]
    apply measure_congr
    filter_upwards [hbase] with q hq
    exact propext (iff_true_intro hq)
  have hvol : volume U = ENNReal.ofReal ((2 * baseMesh) ^ 3) :=
    k4_profile_density_bounds.volume_baseBox center baseMesh hmesh.le
  simpa only [Measure.smul_apply, smul_eq_mul, hmass, hvol] using hcap U


section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
  (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
    κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- Every literal anisotropic physical fibre inherits the earlier pure
ceiling. Its base-volume factor and hidden depth are independent. -/
theorem Native.PreparedAngularPath.original_anisotropic_grid_cap
    (old : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev old)))
    {baseMesh hidden : ℝ} (hmesh : 0 < baseMesh) (hhidden : 0 < hidden)
    (hwidth : δ (d.N k) (p.r (p.lev old)) * hidden / 2 ≤ δ (d.N k) r')
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old))
    (hbase : ∀ᵐ z ∂μ, z ∈ Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z ∈ p.F old)
    {d₁ f₀ error : ℝ}
    (hprofile : |d.f (p.r (p.lev old)) - f₀ - d₁ * p.r (p.lev old)| ≤ error)
    (hprofile' : |d.f r' - f₀ - d₁ * r'| ≤ error) (c : Fin 4 → ℤ) :
    (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))⁻¹ *
        μ ((p.originalPhysicalCode (d.N k) old baseMesh hidden) ⁻¹' {c}) ≤
      ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2 * p.κ *
        d.N k ^ (-d₁ * (r' - p.r (p.lev old)) + 2 * error + τ + ε)) *
          ENNReal.ofReal ((2 * baseMesh) ^ 3) := by
  let S := (p.originalPhysicalCode (d.N k) old baseMesh hidden) ⁻¹' {c}
  have hS : MeasurableSet S :=
    (p.measurable_originalPhysicalCode (d.N k) old baseMesh hidden) (measurableSet_singleton c)
  have hdom : μ.restrict S ≤ μ := Measure.restrict_le_self
  have hcell : ∀ᵐ z ∂μ.restrict S,
      ∀ j, ⌊packetPhysicalPoint (d.N k) p old z j / (if j = 3 then hidden else baseMesh)⌋ = c j := by
    filter_upwards [ae_restrict_mem hS] with z hz j
    have hh : p.originalPhysicalCode (d.N k) old baseMesh hidden z = c := hz
    rw [p.originalPhysicalCode_coordinates] at hh
    exact congrFun hh j
  have hraw := source_anisotropic_cell_mass_cap hd hp old r' hr' hr'L hscale hmesh hhidden hwidth
      (μ.restrict S) (hdom.trans hμ) _ c ((ae_mono hdom) hF) hcell
      (hpure _ _ (hdom.trans hμ) ((ae_mono hdom) hbase) r' hr' hr'L)

  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hcoeff := pure_cap_coefficient (K := d.K k) (τ := τ) (ε := ε) hN (zero_lt_one.trans_le hp.1).le
    (profile_increment_for_cap hprofile hprofile')
  simpa only [Measure.restrict_apply_univ] using
    hraw.trans (mul_le_mul' hcoeff le_rfl)

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
