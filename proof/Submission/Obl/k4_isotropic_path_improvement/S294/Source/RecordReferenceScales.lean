-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordReferenceScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordWidth
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open Parent.ParentSource
open Parent.ParentSource.Native (PathData)

noncomputable section

/-- One reference scale fits both the graph mesh and the physical
state mesh transported by its actual clock or thickness ratio. -/
def recordReference (graphMesh epsilon ratio : ℝ) : ℝ := min graphMesh (epsilon*ratio)/6

theorem record_reference_bounds {graphMesh epsilon ratio : ℝ}
    (hgraph : 0 < graphMesh) (hepsilon : 0 < epsilon) (hratio : 0 < ratio) :
    0 < recordReference graphMesh epsilon ratio ∧
      3*recordReference graphMesh epsilon ratio ≤ graphMesh ∧
      3*ratio⁻¹*recordReference graphMesh epsilon ratio ≤ epsilon := by
  have hmin : 0 < min graphMesh (epsilon*ratio) := lt_min hgraph (mul_pos hepsilon hratio)
  have hgraphMin := min_le_left graphMesh (epsilon*ratio)
  have hphysicalMin := min_le_right graphMesh (epsilon*ratio)
  refine ⟨by unfold recordReference; positivity,?_,?_⟩
  · unfold recordReference
    linarith
  · have hh : 3*recordReference graphMesh epsilon ratio ≤ epsilon*ratio := by
      unfold recordReference
      linarith
    calc
      _ = ratio⁻¹*(3*recordReference graphMesh epsilon ratio) := by ring
      _ ≤ ratio⁻¹*(epsilon*ratio) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hratio.le)
      _ = epsilon := by field_simp

/-- The literal graph and physical budgets of every child at a common
level, using the true ancestor clock and thickness. No path format or
absolute depth factor enters these choices. -/
theorem original_record_reference_scales
    {W : ℕ} (p : PathData W) (N : ℝ) (i ib : ℕ)
    {graphMesh epsilon : ℝ} (hgraph : 0 < graphMesh) (hepsilon : 0 < epsilon)
    (hgraph1 : graphMesh ≤ 1) :
    let clockRatio := (2:ℝ)^p.T i/(2:ℝ)^p.T ib
    let thicknessRatio := δ N (p.r ib)/δ N (p.r i)
    let baseRef := recordReference graphMesh epsilon clockRatio
    let hiddenRef := recordReference graphMesh epsilon thicknessRatio
    0 < baseRef ∧ 0 < hiddenRef ∧ hiddenRef ≤ 1 ∧
      3*baseRef ≤ graphMesh ∧ 3*hiddenRef ≤ graphMesh ∧
      3*((2:ℝ)^p.T ib/(2:ℝ)^p.T i)*baseRef ≤ epsilon ∧
      3*(δ N (p.r i)/δ N (p.r ib))*hiddenRef ≤ epsilon := by
  have hclock := record_reference_bounds hgraph hepsilon
    (by positivity : (0:ℝ)<(2:ℝ)^p.T i/(2:ℝ)^p.T ib)
  have hthickness := record_reference_bounds hgraph hepsilon
    (by unfold δ; positivity : (0:ℝ)<δ N (p.r ib)/δ N (p.r i))
  refine ⟨hclock.1,hthickness.1,?_,hclock.2.1,hthickness.2.1,?_,?_⟩
  · linarith only [hthickness.2.1,hgraph1]
  · simpa only [inv_div] using hclock.2.2
  · simpa only [inv_div] using hthickness.2.2

/-- Uniform lower powers of both meshes and the transport ratio pay
the exact minimum reference, including its factor six. -/
theorem record_reference_lower_power
    {N graphMesh epsilon ratio meshExponent epsilonExponent ratioExponent referenceExponent margin : ℝ}
    (hN : 1 ≤ N) (hgraph : N^(-meshExponent) ≤ graphMesh)
    (hepsilon : N^(-epsilonExponent) ≤ epsilon) (hratio : N^(-ratioExponent) ≤ ratio)
    (hconstant : 6 ≤ N^margin)
    (hmeshMargin : meshExponent+margin ≤ referenceExponent)
    (hphysicalMargin : epsilonExponent+ratioExponent+margin ≤ referenceExponent) :
    N^(-referenceExponent) ≤ recordReference graphMesh epsilon ratio := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hepsilon0 : 0 ≤ epsilon := (Real.rpow_nonneg hNp.le _).trans hepsilon
  have hproduct : N^(-(epsilonExponent+ratioExponent)) ≤ epsilon*ratio := by
    calc
      _ = N^(-epsilonExponent)*N^(-ratioExponent) := by
        rw [←Real.rpow_add hNp]
        congr 1
        ring
      _ ≤ _ := mul_le_mul hepsilon hratio (Real.rpow_nonneg hNp.le _) hepsilon0
  have hconstantBudget : N^(-referenceExponent)*6 ≤ N^(margin-referenceExponent) := by
    calc
      _ ≤ N^(-referenceExponent)*N^margin :=
        mul_le_mul_of_nonneg_left hconstant (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [←Real.rpow_add hNp]; congr 1; ring
  unfold recordReference
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<6)]
  exact le_min
    (hconstantBudget.trans ((Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans hgraph))
    (hconstantBudget.trans ((Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans hproduct))

/-- The lower reference powers are uniform in every actual clock,
thickness and graph mesh supplied after the sample. -/
theorem eventually_record_reference_lower_power
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {meshExponent epsilonExponent ratioExponent referenceExponent margin : ℝ}
    (hmargin : 0 < margin) (hmeshMargin : meshExponent+margin ≤ referenceExponent)
    (hphysicalMargin : epsilonExponent+ratioExponent+margin ≤ referenceExponent) :
    ∀ᶠ k in atTop, ∀ graphMesh epsilon ratio : ℝ,
      N k^(-meshExponent) ≤ graphMesh → N k^(-epsilonExponent) ≤ epsilon →
      N k^(-ratioExponent) ≤ ratio →
      N k^(-referenceExponent) ≤ recordReference graphMesh epsilon ratio := by
  have hlarge := ((tendsto_rpow_atTop hmargin).comp hN).eventually (eventually_ge_atTop 6)
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  intro graphMesh epsilon ratio hgraph hepsilon hratio
  exact record_reference_lower_power hk hgraph hepsilon hratio hc hmeshMargin hphysicalMargin

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
