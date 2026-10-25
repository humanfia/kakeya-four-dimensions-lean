-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RootSlice, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.AncestorRecordStates

/-!
# The root slice of one active ancestor (session x1082)

`root_slice_full`: the census-cut slice of an active ancestor's record source gets its MK4 rows
(`root_slice_of_census`) with the band cap from the prepared path's pure ceiling
(`Forward/AncestorRowInputs.ancestor_rows_band`) and the breadth renewal from the record source
itself (x1095's `OriginalAncestorRecordSource.graph_breadth_renewal`, renewal cost
`81 β μ(kept) ≤ 81 β ref_a`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily)
open scoped ENNReal

noncomputable section

section Slice

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}

/-- **The root slice of an active ancestor, from its record source and a census cut.** -/
theorem root_slice_full (Q : PreparedAngularPath d k p m H u τ) {ε₀ : ℝ}
    (hpure : Q.uniformPureBounds ε₀) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF}
    (a : Fin p.C) (hactive : F.active a) {Edata : Set Ev}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension'
      Kcap : ℝ}
    (data : OriginalAncestorRecordSource F a Edata Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension' Kcap) (hEdataF : Edata ⊆ p.F a)
    (hR : (p.R a).totalDegree ≤ 2) (hA : d.ν k (p.γ a) (p.A a) ≠ 0)
    (hAmeas : MeasurableSet (p.A a)) {Vmax : ℝ} (hV0 : 0 ≤ Vmax) (level : ℕ)
    (current : Set Ev) (hcurrent : MeasurableSet current) (hcurKept : current ⊆ data.kept)
    {censusRate : ℝ≥0∞}
    (hcensusMass : ((d.ν k (p.γ a)).prod volume) data.kept ≤
      ((d.ν k (p.γ a)).prod volume) current +
        censusRate * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)))
    (hcurF : current ⊆ p.F a) (hcurE : current ⊆ d.E k (p.γ a))
    (hcurBase : current ⊆ Q.base (p.γ a))
    (hcurGood : current ⊆ Prod.fst ⁻¹' Parent.SignalGraph.ancestorGood p a Vmax)
    {fineMesh Kcensus dimension cellRate durationRate coarse radius ratio : ℝ} (steps : ℕ)
    (hFine : 0 < fineMesh) (hFine1 : fineMesh ≤ 1) (hKcensus : 1 ≤ Kcensus)
    (hsteps : Kcensus ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : fineMesh * (2 : ℝ) ^ steps ≤ 1)
    (hcellRate : 0 < cellRate) (hdurationRate : 0 < durationRate) (hratio0 : 0 ≤ ratio)
    (hcensus : ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
      Kcensus ^ (100 : ℕ) * b ≤ 1 * w →
      (Submission.Lib.K4ParentSignalPreparation.Census.occupied current
        (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
      ((Submission.Lib.K4ParentSignalPreparation.Census.occupied current
        (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
        Kcensus / (b ^ 3 * w ^ dimension))
    -- the breadth renewal of the record source
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    (hbaseBudget : 3 * baseRef ≤ fineMesh * (2 : ℝ) ^ steps)
    (hhiddenBudget : 3 * hiddenRef ≤ fineMesh * (2 : ℝ) ^ steps)
    (beta : ENNReal) (hbeta : beta ≠ 0) (hbetaTop : beta ≠ ⊤)
    (hwidth : (6 * p.κ) * radius ≤ frontRadius)
    (hratio : ENNReal.ofReal ((8 * fraction) / cut) / beta ≤ ENNReal.ofReal ratio)
    -- the band cap
    (hr : 0 ≤ p.r (p.lev a)) (hrL : p.r (p.lev a) ≤ d.L)
    {f₀ perror : ℝ} (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀ - dimension * r| ≤ perror)
    (n : ℕ) (hmesh : fineMesh * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse n)
    (hbandResolved : d.N k ^ (-(d.L - p.r (p.lev a))) ≤ 4 * coarse)
    (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    {Kg baseRho w gfraction ε : ℝ}
    (hKgJ : 6 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) ≤ Kg) (hKgRate : durationRate⁻¹ ≤ Kg)
    (hKgCount : 8 * (64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
      d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + ε₀)) / cellRate ≤ Kg)
    (hbaseRho : 0 ≤ baseRho) (hcond : 1 ≤ Kg * baseRho ^ 3) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (Vmax + 1) * baseRho ≤ w)
    (hwRadius : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction) (hgfrac : gfraction < 1 - ratio) (hε : 0 < ε)
    (hsmall : Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) ≤
      min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
        ((gfraction / 4) ^ 4 * ε ^ 4 /
          (256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 * Kg ^ 9 + 1)))) :
    ∃ (G : Set Ev) (row : (Fin 4 → ℤ) → Fin 3 → ℝ),
      MeasurableSet G ∧ G ⊆ current ∧ (∀ c j, |row c j| ≤ 28 * Kg ^ 6) ∧
      (∀ z ∈ G, z ∉ p.oldEndpoints a ∧ z ∉ p.levelEndpoints level) ∧
      ((d.ν k (p.γ a)).prod volume) data.kept ≤
        ENNReal.ofReal (1 - gfraction)⁻¹ * ((d.ν k (p.γ a)).prod volume) G +
          (censusRate + (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal ε +
            (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
              ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
                (7 : ℝ) ^ 4)) + 81 * beta)) *
          (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) ∧
      ∀ x ∈ G, |((2 : ℝ) ^ p.T (p.lev a))⁻¹ / Parent.ParentSource.δ (d.N k) (p.r (p.lev a)) *
          Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
        ∑ j : Fin 3, row (clockParentCode p a (Parent.SignalGraph.ancestorSignal (d.N k) p a)
            (Submission.Lib.K4DyadicRowScales.mesh n) x) j *
          (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤
        80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) := by
  have : IsProbabilityMeasure (d.ν k (p.γ a)) := (hd.weights k).2.2 _
  -- the renewal of the record source on the census cut
  have hrenew := Source.OriginalAncestorRecordSource.graph_breadth_renewal data hd hp hHE hH
    hactive hbaseRef hhiddenRef hcut hfr (mesh := fineMesh * (2 : ℝ) ^ steps) (radius := radius)
    (ratio := ratio) (by positivity) hbaseBudget hhiddenBudget beta hbeta hbetaTop hwidth hratio
  have hkeptRef : ((d.ν k (p.γ a)).prod volume) data.kept ≤
      d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹) := by
    refine (measure_mono (fun z hz => hp.counted_subset_fullCylinder a ?_)).trans
      (le_of_eq (p.fullCylinder_mass (d.ν k (p.γ a)) a))
    exact hEdataF (data.kept_subset hz)
  have hrenewCost : 81 * beta * ((d.ν k (p.γ a)).prod volume) data.kept ≤
      81 * beta * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) :=
    mul_le_mul' le_rfl hkeptRef
  have hband := Parent.SignalGraph.ancestor_rows_band Q hpure.ceiling hd hp a hr hrL current
    hcurrent hcurE hcurBase hcurF hdim0 hprofile (coarse := coarse)
    (by rw [hcoarse]; exact Submission.Lib.K4DyadicRowScales.coarse_pos n) hbandResolved
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.1
  have hN0 : 0 ≤ d.N k := by linarith [hd.1 k]
  have hCband : 0 ≤ 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
      d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + ε₀) := by
    have h1 : 0 ≤ 64 * (max p.κ (d.K k)) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 4 ^ dimension := by positivity
    have h3 : 0 ≤ d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + ε₀) := Real.rpow_nonneg hN0 _
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hκ) h2) h3
  exact root_slice_of_census hd hp a hR hA hAmeas hV0 level data.kept current hcurrent hcensusMass
    steps hFine hFine1 hKcensus hsteps hresolved hcellRate hdurationRate hratio0 hcurF hcurGood
    hcensus hrenewCost (fun middle hm hsub => hrenew middle hm (hsub.trans hcurKept)) n hmesh
    hcoarse hdim0 hdim1 hCband hband hKgJ hKgRate hKgCount hbaseRho hcond hbaseRho4
    hwRho hwRadius hgfraction hgfrac hε hsmall

end Slice

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
