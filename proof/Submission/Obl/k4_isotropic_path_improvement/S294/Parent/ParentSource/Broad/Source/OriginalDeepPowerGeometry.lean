-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalDeepPowerGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalDeepPowerGeometry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 40b071c3e1be70138434c7f18ff663f9c27a6dfa,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalDeepPowerGeometry.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentFramePower
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedDeepMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.RenewalCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepPhysicalMenus
import Submission.Obl.k4_clean_cover_graph_atlas.Numerics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native

noncomputable section

/-- The actual two path clock bounds give their relative power directly. -/
theorem Native.PathData.Valid.original_clock_ratio_upper
    {W : ℕ} {p : PathData W} {N L κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 0 < N) (i j : ℕ) (hi : i < m) (hj : j < m) :
    ((2:ℝ)^p.T i/(2:ℝ)^p.T j) ≤ N^((κ₁*(s i-s j)+2*δ₀)*L) := by
  have hupper := (hp.2.2.2.2.1 i hi).2.2.2.1
  have hlower := (hp.2.2.2.2.1 j hj).2.2.1
  calc
    _ ≤ N^((κ₁*s i+δ₀)*L)/N^((κ₁*s j-δ₀)*L) := by gcongr
    _ = _ := by rw [←Real.rpow_sub hN]; congr 1; ring

section Original

variable {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- Native deep radii have a fixed fifth-power frame cost. -/
theorem original_deep_base_radius_le_power {Kgeom : ℝ} (hK : 2304 ≤ Kgeom)
    (hmax : max p.κ (d.K k) ≤ Kgeom) (hgeometry : d.N k^(2*δ₀*d.L) ≤ Kgeom)
    (fine deep : Fin p.C) :
    p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤
      Kgeom^5*((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev deep)) := by
  have hK1 : 1 ≤ Kgeom := by linarith
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hNp : 0 < d.N k := by linarith [hd.1 k]
  have hnonneg : 0 ≤ p.κ^3*d.N k^(2*δ₀*d.L) := by positivity
  have hframe := sharp_frame_coefficient_le_power hK1 hκ ((le_max_left _ _).trans hmax)
    (Real.rpow_nonneg hNp.le _) hgeometry
  have hcoeff : 1+p.κ^3*d.N k^(2*δ₀*d.L)+2*p.κ ≤ Kgeom^5 := by
    apply (show 1+p.κ^3*d.N k^(2*δ₀*d.L)+2*p.κ ≤ 11*Kgeom^4 by linarith).trans
    calc
      _ ≤ Kgeom*Kgeom^4 := by gcongr; linarith
      _ = _ := (pow_succ' Kgeom 4).symm
  exact mul_le_mul_of_nonneg_right hcoeff (by positivity)

/-- The actual center velocity is bounded by an original assigned line,
so unsheared deep radii cost only three geometry powers. -/
theorem original_unsheared_deep_radius_le_power {Kgeom : ℝ} (hK : 2304 ≤ Kgeom)
    (hmax : max p.κ (d.K k) ≤ Kgeom) (old deep : Fin p.C) :
    p.unshearedDeepRadius old deep ≤
      Kgeom^3*((2:ℝ)^p.T (p.lev old)/(2:ℝ)^p.T (p.lev deep)) := by
  have hKp : 0 < Kgeom := by linarith
  have hK1 : 1 ≤ Kgeom := by linarith
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hκK : p.κ ≤ Kgeom := (le_max_left _ _).trans hmax
  have hDK : d.K k ≤ Kgeom := (le_max_right _ _).trans hmax
  have hκ2 := pow_le_pow_left₀ hκ hκK 2
  have hcenter := original_packet_center_velocity hd hp deep
  have hcoeff : 1+p.κ^2+‖p.u deep‖ ≤ Kgeom^3 := by
    have hfirst : 1+p.κ^2+‖p.u deep‖ ≤ 5*Kgeom^2 := by
      nlinarith [one_le_pow₀ hK1 (n := 2),show Kgeom ≤ Kgeom^2 by nlinarith]
    apply hfirst.trans
    calc
      _ ≤ Kgeom*Kgeom^2 := by gcongr; linarith
      _ = _ := (pow_succ' Kgeom 2).symm
  exact mul_le_mul_of_nonneg_right hcoeff (by positivity)

/-- A primitive clock-gap power budget resolves the actual renewal cells. -/
theorem original_capture_resolution_of_clock_budget
    {K Kgeom : ℝ} (hK0 : 0 ≤ K) (hK : 2304 ≤ Kgeom) (hKK : K ≤ Kgeom)
    (hmax : max p.κ (d.K k) ≤ Kgeom) (hgeometry : d.N k^(2*δ₀*d.L) ≤ Kgeom)
    (R J qc : ℕ) (fine deep : Fin p.C)
    (hclock : Kgeom^(R+6+(4*J+qc+14))*
      ((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev deep)) ≤ 1) :
    6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kgeom J qc := by
  have hKp : 0 < Kgeom := by linarith
  have hdeep := original_deep_base_radius_le_power hd hp hK hmax hgeometry fine deep
  have hNp : 0 < d.N k := by linarith [hd.1 k]
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hdeep0 : 0 ≤ p.deepBaseRadius (d.N k) d.L δ₀ fine deep := by
    unfold PathData.deepBaseRadius; positivity
  have hresolved : Kgeom^(R+6)*((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev deep)) ≤
      (Kgeom^(4*J+qc+14))⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (pow_pos hKp _)).mpr
    convert hclock using 1 <;> rw [pow_add] <;> ring
  calc
    _ ≤ 6*Kgeom^R*(Kgeom^5*((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev deep))) := by gcongr
    _ ≤ Kgeom*Kgeom^R*(Kgeom^5*((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev deep))) := by
      gcongr
      linarith
    _ = Kgeom^(R+6)*((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev deep)) := by simp only [pow_add]; ring
    _ ≤ _ := hresolved

/-- A geometry-power envelope and the actual path clock gap discharge
all renewal-resolution inequalities simultaneously. -/
theorem original_clock_gap_power_budget
    {Kgeom cost : ℝ} (hN : 1 ≤ d.N k) (power : ℕ) (fine deep : Fin p.C)
    (hpower : Kgeom^power ≤ d.N k^cost)
    (hgap : cost ≤ (κ₁*(s (p.lev deep)-s (p.lev fine))-2*δ₀)*d.L) :
    Kgeom^power*((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev deep)) ≤ 1 := by
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hclock := hp.original_clock_ratio_upper hNp (p.lev fine) (p.lev deep)
    (hp.2.2.2.2.2.2.2 fine).1 (hp.2.2.2.2.2.2.2 deep).1
  have hclock' : ((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev deep)) ≤ d.N k^(-cost) :=
    hclock.trans (Real.rpow_le_rpow_of_exponent_le hN (by nlinarith))
  calc
    _ ≤ d.N k^cost*d.N k^(-cost) := mul_le_mul hpower hclock' (by positivity) (by positivity)
    _ = 1 := by rw [←Real.rpow_add hNp]; simp

/-- The deep clock divided by an earlier physical width has an explicit
path exponent; the old clock cancels completely. -/
theorem original_deep_clock_div_width_upper
    (hN : 1 ≤ d.N k) (old deep : Fin p.C) :
    (((2:ℝ)^p.T (p.lev deep))⁻¹)/δ (d.N k) (p.r (p.lev old)) ≤
      d.N k^((s (p.lev old)-κ₁*s (p.lev deep)+2*δ₀)*d.L) := by
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hold := hp.2.2.2.2.1 (p.lev old) (hp.2.2.2.2.2.2.2 old).1
  have hdeep := hp.2.2.2.2.1 (p.lev deep) (hp.2.2.2.2.2.2.2 deep).1
  have htime : ((2:ℝ)^p.T (p.lev deep))⁻¹ ≤ d.N k^(-((κ₁*s (p.lev deep)-δ₀)*d.L)) := by
    rw [Real.rpow_neg hNp.le]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hdeep.2.2.1
  have hwidth := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp (p.r (p.lev old))).1
  change d.N k^(-p.r (p.lev old)) ≤ δ (d.N k) (p.r (p.lev old)) at hwidth
  calc
    _ ≤ d.N k^(-((κ₁*s (p.lev deep)-δ₀)*d.L))/d.N k^(-p.r (p.lev old)) := by gcongr
    _ = d.N k^(p.r (p.lev old)-(κ₁*s (p.lev deep)-δ₀)*d.L) := by
      rw [←Real.rpow_sub hNp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith [(abs_le.mp hold.1).2])

/-- The genuine shallow pair oscillation fits one physical height mesh
from just a fine-depth margin and a deep-clock margin. -/
theorem original_shallow_height_resolution
    {K Kgeom G mesh : ℝ} (hK : 0 < K) (hGeom : 2304 ≤ Kgeom) (hKK : K ≤ Kgeom)
    (hmax : max p.κ (d.K k) ≤ Kgeom) (hgeometry : d.N k^(2*δ₀*d.L) ≤ Kgeom)
    (gp : ℕ) (hG : 0 ≤ G) (hGK : G ≤ Kgeom^gp) (old deep : Fin p.C) (mid : ℕ)
    (herror : Kgeom^(gp+10)*(δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev old))) ≤ mesh)
    (hclock : 2*Kgeom^(gp+15)*
      ((((2:ℝ)^p.T (p.lev deep))⁻¹)/δ (d.N k) (p.r (p.lev old))) ≤ mesh) :
    let aOld := δ (d.N k) (p.r (p.lev old))
    let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
    let Lip := (12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison)*
      (((2:ℝ)^p.T (p.lev old))⁻¹)/aOld
    (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/aOld))+
      Lip*(6*p.unshearedDeepRadius old deep) ≤ mesh := by
  intro aOld comparison Lip
  have hGp : 0 < Kgeom := by linarith
  have hNp : 0 < d.N k := by linarith [hd.1 k]
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have ha : 0 < aOld := by dsimp [aOld,δ]; positivity
  have hU : 0 ≤ p.unshearedDeepRadius old deep := by unfold PathData.unshearedDeepRadius; positivity
  have hratio : 0 ≤ δ (d.N k) (p.r mid)/aOld := by unfold δ; positivity
  have hsmall : K^14*(K^6)⁻¹ ≤ Kgeom^14*(Kgeom^6)⁻¹ := by
    have heq (x : ℝ) (hx : x≠0) : x^14*(x^6)⁻¹=x^8 := by
      simpa using (pow_sub₀ x hx (by norm_num : (6:ℕ) ≤ 14)).symm
    rw [heq K hK.ne',heq Kgeom hGp.ne']
    exact pow_le_pow_left₀ hK.le hKK 8
  have hadd : (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/aOld)) ≤ mesh/2 := by
    apply le_trans (b := (2+G/2)*(Kgeom^14*(Kgeom^6)⁻¹*(δ (d.N k) (p.r mid)/aOld)))
    · gcongr
    · exact gradient_error_le_half_power_mesh (by linarith) gp hGK (by dsimp [aOld,δ]; positivity) herror
  have hslopeGeom := original_parent_slope_le_power hd hp hGeom hmax hgeometry gp hG hGK old
  have hslope : 12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison ≤ Kgeom^(gp+11) := by
    apply le_trans (b := 12*Kgeom*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison)
    · dsimp [comparison]; gcongr
    · exact hslopeGeom
  have hdeep := original_unsheared_deep_radius_le_power hd hp hGeom hmax old deep
  have hLip : Lip*(6*p.unshearedDeepRadius old deep) ≤ mesh/2 := by
    calc
      _ ≤ (Kgeom^(gp+11)*(((2:ℝ)^p.T (p.lev old))⁻¹)/aOld)*
          (6*(Kgeom^3*((2:ℝ)^p.T (p.lev old)/(2:ℝ)^p.T (p.lev deep)))) := by
        dsimp [Lip]
        gcongr
      _ = 6*Kgeom^(gp+14)*((((2:ℝ)^p.T (p.lev deep))⁻¹)/aOld) := by
        simp only [pow_add]
        field_simp <;> ring
      _ ≤ Kgeom*Kgeom^(gp+14)*((((2:ℝ)^p.T (p.lev deep))⁻¹)/aOld) := by gcongr; linarith
      _ = Kgeom^(gp+15)*((((2:ℝ)^p.T (p.lev deep))⁻¹)/aOld) := by simp only [pow_add]; ring
      _ ≤ mesh/2 := by linarith
  linarith

end Original

/-- Renewal resolution also resolves the coarser nearby-core menu scale. -/
theorem core_radius_small_of_renewal_resolution {K Kgeom radius : ℝ}
    (hK : 0 < K) (hGeom : 2 ≤ Kgeom) (R J qc : ℕ)
    (hsmall : 6*K^R*radius ≤ renewalCellMesh Kgeom J qc) : radius ≤ (K^R)⁻¹/12 := by
  have hGeom1 : 1 ≤ Kgeom := by linarith
  have hGeomP : 0 < Kgeom := by linarith
  have hpow : 2 ≤ Kgeom^(4*J+qc+14) := hGeom.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hGeom1 (show 1 ≤ 4*J+qc+14 by omega))
  have hmesh : renewalCellMesh Kgeom J qc ≤ 1/2 := by
    unfold renewalCellMesh
    simpa only [one_div] using (inv_le_inv₀ (pow_pos hGeomP _) (by norm_num : (0:ℝ) < 2)).mpr hpow
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 12)).mpr
  rw [←one_div]
  apply (le_div_iff₀ (pow_pos hK R)).mpr
  nlinarith [hsmall.trans hmesh]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
