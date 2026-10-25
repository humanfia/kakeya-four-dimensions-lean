-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleReferenceFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordStateMeshLower
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordReferenceScales
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RelativeOldClock
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RelativeWindowScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

private theorem power_le_half_of_margin {N a b margin : ℝ}
    (hN : 1 ≤ N) (hconstant : 2 ≤ N^margin) (hmargin : a+margin ≤ b) :
    N^(-b) ≤ N^(-a)/2 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ N^(-b)*N^margin :=
      mul_le_mul_of_nonneg_left hconstant (Real.rpow_nonneg hNp.le _)
    _ = N^(margin-b) := by rw [←Real.rpow_add hNp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hmargin])

/-- The actual state mesh and both transport ratios have one common
lower power at the chosen child offset. Its accuracy has no tuning
depth factor; the original path depth/clock bounds suffice. -/
theorem sample_reference_transport_floors
    {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    {precision loss gain : ℝ} {Ep i : ℕ}
    (hN : 1 ≤ d.N k) (hL : 0 < d.L) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1)
    (hprecision : 1 ≤ precision) (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain)
    (_hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain/100) (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ))
    (hs : ∀ j, s j=((j:ℝ)+1)/m)
    (hi : i < m) (hib : i+childOffset κ₁ Ep precision gain m < m)
    (hconstant : 2 ≤ d.N k^(gain*d.L)) :
    let ib := i+childOffset κ₁ Ep precision gain m
    let accuracy := 3*(((Ep:ℝ)+1)*precision+3)*gain*d.L/κ₁
    d.N k^(-accuracy) ≤ epsOf Ep precision loss gain (d.N k) d.L
      (p.r i) (p.r ib) (p.T i) (p.T ib) ∧
    d.N k^(-accuracy) ≤ (2:ℝ)^p.T i/(2:ℝ)^p.T ib ∧
    d.N k^(-accuracy) ≤ δ (d.N k) (p.r ib)/δ (d.N k) (p.r i) := by
  let ib := i+childOffset κ₁ Ep precision gain m
  let X := ((Ep:ℝ)+1)*precision+3
  let u := gain*d.L/κ₁
  let accuracy := 3*X*gain*d.L/κ₁
  let gap := ((childOffset κ₁ Ep precision gain m:ℕ):ℝ)/(m:ℝ)
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hX : 1 ≤ X := by
    have hEp : 0 ≤ (Ep:ℝ) := Nat.cast_nonneg Ep
    dsimp only [X]
    nlinarith only [hEp,hprecision]
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hgL : 0 ≤ gain*d.L := by positivity
  have hGainU : gain*d.L ≤ u := by
    dsimp only [u]
    rw [le_div_iff₀ hκ]
    exact mul_le_of_le_one_right hgL hκ1
  have hGainXU : gain*d.L ≤ X*u := hGainU.trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hX hu)
  have haccuracy : accuracy=3*X*u := by dsimp only [accuracy,u]; ring
  have hgap : s ib-s i=gap := by
    dsimp only [ib,gap]
    rw [hs,hs]
    push_cast
    ring
  have hdepth : (gap+2*δ₀)*d.L ≤ 2*X*u := by
    have hh := childOffset_depth_bound (Ep := Ep) hκ hκ1 hprecision hgain hδ hL.le hm hgm
    simpa only [gap,X,u,div_eq_mul_inv,mul_assoc] using hh
  have hphysical : p.r ib-p.r i ≤ 2*X*u := by
    have h1 := (abs_le.mp (hp.2.2.2.2.1 i hi).1).1
    have h2 := (abs_le.mp (hp.2.2.2.2.1 ib hib).1).2
    have hh : p.r ib-p.r i ≤ (s ib-s i+2*δ₀)*d.L := by nlinarith only [h1,h2]
    rw [hgap] at hh
    exact hh.trans hdepth
  have hclockDepth : (κ₁*(s ib-s i)+2*δ₀)*d.L ≤ 2*X*u := by
    rw [hgap]
    have hgap0 : 0 ≤ gap := by dsimp only [gap]; positivity
    have hh := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hgap0 hκ1) hL.le
    nlinarith only [hh,hdepth]
  have hclock := (hp.relative_old_clock_bounds hNp i ib hi hib).1
  have hclockIdentity : ((2:ℝ)^p.T ib)⁻¹/((2:ℝ)^p.T i)⁻¹=
      (2:ℝ)^p.T i/(2:ℝ)^p.T ib := by field_simp
  rw [hclockIdentity] at hclock
  have hwidth := (hp.relative_parent_width_bounds hN i ib hi hib).1
  rw [hgap] at hwidth
  have hwidthMargin : (gap+2*δ₀)*d.L+gain*d.L ≤ accuracy := by
    rw [haccuracy]
    linarith only [hdepth,hGainXU]
  have hEpsilonFloor := state_mesh_lower_of_depth_bound (L := d.L) (precision := precision)
    (loss := loss) (gain := gain) Ep (p.T i) (p.T ib) hN hphysical hconstant
  have hEpsilonMargin : 2*X*u+((Ep:ℝ)+1)*(precision*gain*d.L)+
      (2*(Ep:ℝ)+2)*(loss*gain*d.L/((Ep:ℝ)+1))+gain*d.L ≤ accuracy := by
    have hE : 0 < (Ep:ℝ)+1 := by positivity
    have hcoeff : (2*(Ep:ℝ)+2)*(loss*gain*d.L/((Ep:ℝ)+1))=2*(loss*gain*d.L) := by field_simp
    have hLoss : loss*gain*d.L ≤ gain*d.L := by
      have hh := mul_le_of_le_one_left hgL hloss1
      nlinarith only [hh]
    have hXgain : ((Ep:ℝ)+1)*(precision*gain*d.L)+3*(gain*d.L)=X*(gain*d.L) := by
      dsimp only [X]
      ring
    have hh := mul_le_mul_of_nonneg_left hGainU hX0
    rw [hcoeff,haccuracy]
    nlinarith only [hLoss,hXgain,hh]
  change d.N k^(-accuracy) ≤ _ ∧ d.N k^(-accuracy) ≤ _ ∧ d.N k^(-accuracy) ≤ _
  refine ⟨?_,?_,?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hEpsilonMargin])).trans hEpsilonFloor
  · apply le_trans _ hclock
    apply Real.rpow_le_rpow_of_exponent_le hN
    rw [haccuracy]
    nlinarith only [hclockDepth,mul_nonneg hX0 hu]
  · exact (power_le_half_of_margin hN hconstant hwidthMargin).trans hwidth

/-- The two literal minimum references have a common lower power.
The only remaining geometric input is the mesh exponent; both actual
path transport factors and the state mesh are supplied internally. -/
theorem sample_record_reference_floors
    {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    {precision loss gain graphMesh graphExponent : ℝ} {Ep i : ℕ}
    (hN : 1 ≤ d.N k) (hL : 0 < d.L) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1)
    (hprecision : 1 ≤ precision) (hloss : 0 < loss) (hloss1 : loss ≤ 1)
    (hgain : 0 < gain) (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain/100)
    (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ)) (hs : ∀ j, s j=((j:ℝ)+1)/m)
    (hi : i < m) (hib : i+childOffset κ₁ Ep precision gain m < m)
    (hconstant : 6 ≤ d.N k^(gain*d.L))
    (hgraph : d.N k^(-graphExponent) ≤ graphMesh) :
    let ib := i+childOffset κ₁ Ep precision gain m
    let epsilon := epsOf Ep precision loss gain (d.N k) d.L
      (p.r i) (p.r ib) (p.T i) (p.T ib)
    let accuracy := 3*(((Ep:ℝ)+1)*precision+3)*gain*d.L/κ₁
    let referenceExponent := max graphExponent (2*accuracy)+gain*d.L
    d.N k^(-referenceExponent) ≤
      recordReference graphMesh epsilon ((2:ℝ)^p.T i/(2:ℝ)^p.T ib) ∧
    d.N k^(-referenceExponent) ≤
      recordReference graphMesh epsilon (δ (d.N k) (p.r ib)/δ (d.N k) (p.r i)) := by
  have hfloors := sample_reference_transport_floors hp hN hL hκ hκ1
    hprecision hloss hloss1 hgain hδ0 hδ hm hgm hs hi hib
    (by linarith only [hconstant])
  dsimp only at hfloors ⊢
  have hmesh := add_le_add_right
    (le_max_left graphExponent (2*(3*(((Ep:ℝ)+1)*precision+3)*gain*d.L/κ₁)))
    (gain*d.L)
  have hphysical := add_le_add_right
    (le_max_right graphExponent (2*(3*(((Ep:ℝ)+1)*precision+3)*gain*d.L/κ₁)))
    (gain*d.L)
  constructor
  · exact record_reference_lower_power hN hgraph hfloors.1 hfloors.2.1 hconstant
      (by linarith only [hmesh]) (by linarith only [hphysical])
  · exact record_reference_lower_power hN hgraph hfloors.1 hfloors.2.2 hconstant
      (by linarith only [hmesh]) (by linarith only [hphysical])

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
