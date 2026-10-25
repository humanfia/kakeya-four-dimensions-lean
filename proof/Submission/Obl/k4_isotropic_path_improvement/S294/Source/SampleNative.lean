-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleNative, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeSampleHbox
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativePreStateMetadata

/-!
# The native root step of one sample (session x1082)

`native_root_step`: the input `hnative` of `Source.SampleFinal.sample_final`, for one
`OriginalRootScales` `scales` and its pre-state scales `ps` chosen before the root package. For
every root package whose graph mesh is the dyadic mesh `mesh nmesh`, whose row bound is
`28 Kg^6`, whose raw MK4 fit is at most `80 Kg^7 mesh^((1-d)/24)` and whose root slices satisfy the
census at `(fineMesh, Kcensus, dimension)`:

* x1096's global P1 cut `prepare_native_pre_state_metadata` gives the cut `E1'` of the root slices,
  of weighted loss `ps.charge`, with `NativeRootMetadata` on its slices;
* `native_sample_hbox` on the restricted package gives `SampleHbox` with the constants of `scales`.

All premises are scalar comparisons between `scales` and the sample's numbers.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual
  labelledVelocityPalette)
open Parent.Qualification
open Parent.Qualification.PhysicalModel
open Parent.Qualification.PhysicalModel.NativeAncestor
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- **The native root step of one sample**: `sample_final`'s `hnative` from one pair of scales. -/
theorem native_root_step
    {T : Type*} {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε₀ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} (hpure : Q.uniformPureBounds ε₀)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF}
    {rF frF : ℝ} {Rp : BroadResidual F rF frF} {c : ℕ} {K θ ε aA q d₁ h' a' : ℝ}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    {core : BroadMultiscaleCoreSource d k p original n depth Kcore e R}
    (scales : OriginalRootScales) (ps : OriginalPreStateScales scales)
    -- the levels
    (hib : i + c ≤ m - 1) (hT : scales.T = p.T (i + c) - p.T i)
    -- the graph mesh, the row bound and the raw fit of the root package
    {nmesh : ℕ} {Kg dimensionMK : ℝ}
    (hb : scales.b = Submission.Lib.K4DyadicRowScales.mesh nmesh) (hBrow : 28 * Kg ^ 6 ≤ scales.B)
    (hqaA : q / aA = ((2 : ℝ) ^ p.T i)⁻¹ / δ (d.N k) (p.r i))
    (herror : 80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimensionMK) / 24) ≤
      scales.error)
    -- the census of the root slices
    {fineMesh Kcensus : ℝ} (hKcensus0 : 0 ≤ Kcensus) (hKcensus : Kcensus ≤ scales.Kcensus)
    (hfineRes : fineMesh ≤ scales.resolution) (hcensusDim : scales.dimension = dimensionMK)
    -- the velocities
    {Vmax : ℝ} (hVmax : 0 ≤ Vmax) (hvelocity : ∀ w, ∀ z ∈ Rp.residual w, ‖Parent.v z.1‖ ≤ Vmax)
    (hcoeffH : coefficientBound (p := p) Vmax ≤ scales.H) (hVmaxU : Vmax ≤ scales.Uvelocity)
    -- the ratio coefficients
    (radius : ℝ) (beta : ENNReal)
    (hstripCoeff : ENNReal.ofReal ((8 * fraction) / cut) / beta ≤ ENNReal.ofReal scales.failure)
    (hpaletteCoeff : 4 * (ENNReal.ofReal ((8 * paletteRatio) / cut) / beta) ≤
      ENNReal.ofReal scales.incidence.Cstate)
    -- the pure caps of the retained records
    (hfinePv : 0 < finePv) (hfineWidth : finePv ≤ Jets2.dyadicParameterWidth scales.paletteFinest)
    (haux : 1 < d.N k ^ χ) (histop : i ≤ stop) (hri : 0 ≤ p.r i) (hrLi : p.r i ≤ d.L)
    (hdepth : p.r i + χ * finest ≤ d.L)
    (hbaseRef : 3 * baseRef ≤ (d.N k ^ χ) ^ (-finest))
    (hhiddenRef : 3 * hiddenRef ≤ (d.N k ^ χ) ^ (-finest))
    (hRatio : 0 ≤ paletteRatio) (hcut : 0 < cut) (hKcap : 0 ≤ Kcap)
    (hbaseLo : (d.N k ^ χ) ^ (-finest) ≤ scales.resolution)
    (hbaseHi : scales.resolution ≤ (d.N k ^ χ) ^ (-finest⁻¹))
    (hstartHi : Jets2.dyadicParameterWidth scales.floorStart ≤ (d.N k ^ χ) ^ (-finest⁻¹))
    (hCpure : 4 * 625 * ((8 * paletteRatio) / cut) * Kcap ≤ scales.Cpure)
    (hdimension : scales.dimension = dimension)
    -- the band of the ancestor signal
    {f₀ perror : ℝ}
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀ - scales.dimension * r| ≤ perror)
    (hCband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ scales.dimension *
      d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + ε₀) ≤ scales.Cband)
    (hresolved : d.N k ^ (-(d.L - p.r i)) ≤ 4 * scales.resolution) :
    ∀ RP : RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap core,
      RP.graphMesh = Submission.Lib.K4DyadicRowScales.mesh nmesh → RP.Brow = 28 * Kg ^ 6 →
      (∀ a, F.active a → ∀ x ∈ RP.E1 (p.γ a) ∩ p.F a,
        |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
          ∑ j : Fin 3, RP.row a (ancCode (d.N k) p a RP.graphMesh x) j *
            (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤
        80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimensionMK) / 24)) →
      (∀ a, F.active a → ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
        Kcensus ^ (100 : ℕ) * b ≤ 1 * w →
        (occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
          Kcensus / (b ^ 3 * w ^ dimensionMK)) →
      ∃ (E1' : Fin (d.W k) → Set Ev) (hmeas : ∀ w, MeasurableSet (E1' w))
        (hsub : ∀ w, E1' w ⊆ RP.E1 w),
        (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) ≤
          (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E1' w)) + ps.charge ∧
        SampleHbox hp (RP.restrict E1' hmeas hsub) radius scales.stripWidth beta
          scales.incidence.M scales.T scales.mesh scales.err scales.duration scales.bound
          scales.regularityFactor (scales.regularityFactor * scales.supportLoss)
          scales.nativeFailureBound scales.Lp scales.ρ := by
  intro RP hmesh hBrowEq hfitRaw hoccRaw
  -- the census of the root slices at the scales
  have hcensus : ∀ root, F.active root → ∀ b w : ℝ,
      scales.resolution ≤ b → b ≤ 1 → scales.resolution ≤ w → w ≤ 1 →
      scales.Kcensus ^ (100 : ℕ) * b ≤ w →
      (occupied (RP.E1 (p.γ root) ∩ p.F root) (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) b w).Finite ∧
      ((occupied (RP.E1 (p.γ root) ∩ p.F root) (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) b w).ncard : ℝ) ≤
          scales.Kcensus / (b ^ 3 * w ^ scales.dimension) := by
    intro root hroot b w hb1 hb2 hw1 hw2 hKw
    have hb0 : 0 < b := scales.hresolution.trans_le hb1
    have hw0 : 0 < w := scales.hresolution.trans_le hw1
    have hpow : Kcensus ^ (100 : ℕ) ≤ scales.Kcensus ^ (100 : ℕ) :=
      pow_le_pow_left₀ hKcensus0 hKcensus 100
    obtain ⟨hfin, hcard⟩ := hoccRaw root hroot b w (hfineRes.trans hb1) hb2 (hfineRes.trans hw1) hw2
      (by rw [one_mul]; exact (mul_le_mul_of_nonneg_right hpow hb0.le).trans hKw)
    refine ⟨hfin, hcard.trans ?_⟩
    rw [hcensusDim]
    exact div_le_div_of_nonneg_right hKcensus (by positivity)
  -- the global P1 cut with its metadata
  obtain ⟨E1', hmeas, hsub, hmass, ⟨nmeta⟩⟩ := prepare_native_pre_state_metadata hd hp hHE RP
    scales ps hdimension hVmax hvelocity hcoeffH haux histop hri hdepth hbaseRef hhiddenRef hRatio
    hcut hKcap hfinePv hfineWidth hbaseLo hstartHi hCpure hcensus
  refine ⟨E1', hmeas, hsub, hmass, ?_⟩
  -- the regularity/qualification input on the cut package
  exact native_sample_hbox hd hpure hp hHE hH (RP.restrict E1' hmeas hsub) scales nmeta hib hT
    (by rw [hb]; exact hmesh.symm) (by change RP.Brow ≤ _; rw [hBrowEq]; exact hBrow) hqaA
    (fun a ha x hx => (hfitRaw a ha x ⟨hsub _ hx.1, hx.2⟩).trans herror)
    hVmax hvelocity hcoeffH hVmaxU radius beta hstripCoeff hpaletteCoeff hfinePv hfineWidth haux
    histop hri hrLi hdepth hbaseRef hhiddenRef hRatio hcut hKcap hbaseLo hbaseHi hCpure hdimension
    (fun a ha b w h1 h2 h3 h4 h5 => by
      obtain ⟨hfin, hcard⟩ := hcensus a ha b w h1 h2 h3 h4 h5
      have hsubo : occupied (E1' (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w ⊆
          occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w := by
        rintro kk ⟨x, hx, rfl⟩
        exact ⟨x, ⟨hsub _ hx.1, hx.2⟩, rfl⟩
      exact ⟨hfin.subset hsubo, le_trans (by exact_mod_cast Set.ncard_le_ncard hsubo hfin) hcard⟩)
    hprofile hCband hresolved

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
