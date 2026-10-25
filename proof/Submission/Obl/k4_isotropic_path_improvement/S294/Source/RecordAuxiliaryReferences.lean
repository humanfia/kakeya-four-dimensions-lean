-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordAuxiliaryReferences, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleReferenceFloors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

/-- The actual auxiliary native resolution and graph mesh have one
common lower power, including their literal minimum. -/
theorem record_auxiliary_mesh_lower_power
    {N graphMesh graphExponent chi finest : ℝ}
    (hN : 1 ≤ N) (hgraph : N^(-graphExponent) ≤ graphMesh) :
    N^(-max graphExponent (chi*finest)) ≤ min graphMesh ((N^chi)^(-finest)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  refine le_min ?_ ?_
  · exact (Real.rpow_le_rpow_of_exponent_le hN
      (neg_le_neg (le_max_left _ _))).trans hgraph
  · rw [←Real.rpow_mul hNp.le]
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hh := le_max_right graphExponent (chi*finest)
    nlinarith only [hh]

/-- The exact references fit both the MK4 graph and every auxiliary
native query, and transport to the physical state mesh by the actual
ancestor clock and thickness ratios. -/
theorem original_auxiliary_record_reference_scales
    {W : ℕ} (p : PathData W) {N : ℝ} (i ib : ℕ)
    {graphMesh epsilon chi finest : ℝ} (hN : 0 < N)
    (hgraph : 0 < graphMesh) (hepsilon : 0 < epsilon) (hgraph1 : graphMesh ≤ 1) :
    let referenceMesh := min graphMesh ((N^chi)^(-finest))
    let baseRef := recordReference referenceMesh epsilon ((2:ℝ)^p.T i/(2:ℝ)^p.T ib)
    let hiddenRef := recordReference referenceMesh epsilon (δ N (p.r ib)/δ N (p.r i))
    0 < baseRef ∧ 0 < hiddenRef ∧ hiddenRef ≤ 1 ∧
      3*baseRef ≤ graphMesh ∧ 3*hiddenRef ≤ graphMesh ∧
      3*baseRef ≤ (N^chi)^(-finest) ∧ 3*hiddenRef ≤ (N^chi)^(-finest) ∧
      3*((2:ℝ)^p.T ib/(2:ℝ)^p.T i)*baseRef ≤ epsilon ∧
      3*(δ N (p.r i)/δ N (p.r ib))*hiddenRef ≤ epsilon := by
  have haux : 0 < (N^chi)^(-finest) := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _
  have hmesh : 0 < min graphMesh ((N^chi)^(-finest)) := lt_min hgraph haux
  have hmesh1 : min graphMesh ((N^chi)^(-finest)) ≤ 1 := (min_le_left _ _).trans hgraph1
  obtain ⟨hb,hh,hh1,hbg,hhg,hbe,hhe⟩ :=
    original_record_reference_scales p N i ib hmesh hepsilon hmesh1
  exact ⟨hb,hh,hh1,hbg.trans (min_le_left _ _),hhg.trans (min_le_left _ _),
    hbg.trans (min_le_right _ _),hhg.trans (min_le_right _ _),hbe,hhe⟩

/-- Both references retain an explicit common lower power after
adding the auxiliary native cutoff. The sample's actual state and
transport floors are proved internally. -/
theorem sample_auxiliary_record_reference_floors
    {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    {precision loss gain graphMesh graphExponent chi finest : ℝ} {Ep i : ℕ}
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
    let referenceExponent := max (max graphExponent (chi*finest)) (2*accuracy)+gain*d.L
    let referenceMesh := min graphMesh (((d.N k)^chi)^(-finest))
    d.N k^(-referenceExponent) ≤
      recordReference referenceMesh epsilon ((2:ℝ)^p.T i/(2:ℝ)^p.T ib) ∧
    d.N k^(-referenceExponent) ≤
      recordReference referenceMesh epsilon (δ (d.N k) (p.r ib)/δ (d.N k) (p.r i)) := by
  exact sample_record_reference_floors hp hN hL hκ hκ1 hprecision hloss hloss1 hgain hδ0 hδ
    hm hgm hs hi hib hconstant (record_auxiliary_mesh_lower_power hN hgraph)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
