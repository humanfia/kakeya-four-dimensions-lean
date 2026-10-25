-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeSampleHbox, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeRootPreparationFromData
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeRootMetadata
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootPureCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.AncestorGraphRecordRatios
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRowInputs

/-!
# The regularity/qualification input of one sample from the native metadata (session x1082)

`native_sample_hbox`: on a root package whose root slices carry x1096's `NativeRootMetadata`
(one common original velocity reference per active ancestor, full-prior floors and actual
derivative tables), the input `SampleHbox` of `samplePost_of_rootPackage` holds with the
constants of one `OriginalRootScales`: `Pfac = regularityFactor`, `chargeR = regularityFactor *
supportLoss`, `η = nativeFailureBound`, the row Lipschitz constant `Lp`, `ρ` and the qualification
scalars of the scales. For every later cut `E2` of the root slices and the child graph ratios,
each active ancestor is prepared by x1096's `prepare_native_root_from_original_data` on its slice
of `E2`:

* the ancestor ratios aggregate the child ratios (x1095's
  `ancestor_graph_record_ratios_of_child_ratios`);
* the metadata restricts to the slice (`NativeRootMetadata.restrict`);
* the pure caps come from the retained records of the package (`original_root_pure_caps_of_records`)
  at the scales' resolution;
* the census of the root slices restricts to the slice (`occupied_bound_mono`);
* the band cap is `ancestor_rows_band` (the clock signal of the ancestor is its physical signal);
* the rows, the graph mesh and the fit are those of the package.

The codes of the ancestors are assembled by `exists_codes_of_per_root`.
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

/-- **The regularity/qualification input of one sample** from the native metadata of its root
package and one `OriginalRootScales`. -/
theorem native_sample_hbox
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
    (RP : RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap core)
    (scales : OriginalRootScales) {Vmax : ℝ}
    (nmeta : NativeRootMetadata hp {a | F.active a} RP.E1 Vmax finePv scales
      (fun a => (Q.coarseLaw (p.lev a) (F.code a)).map (labelledVelocityPalette finePv)))
    -- the levels
    (hib : i + c ≤ m - 1) (hT : scales.T = p.T (i + c) - p.T i)
    -- the rows and the fit of the package
    (hb : scales.b = RP.graphMesh) (hBrow : RP.Brow ≤ scales.B)
    (hqaA : q / aA = ((2 : ℝ) ^ p.T i)⁻¹ / δ (d.N k) (p.r i))
    (hfit : ∀ a, F.active a → ∀ x ∈ RP.E1 (p.γ a) ∩ p.F a,
      |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
        ∑ j : Fin 3, RP.row a (ancCode (d.N k) p a RP.graphMesh x) j *
          (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤ scales.error)
    -- the velocities
    (hVmax : 0 ≤ Vmax) (hvelocity : ∀ w, ∀ z ∈ Rp.residual w, ‖Parent.v z.1‖ ≤ Vmax)
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
    (hCpure : 4 * 625 * ((8 * paletteRatio) / cut) * Kcap ≤ scales.Cpure)
    (hdimension : scales.dimension = dimension)
    -- the census of the root slices
    (hcensus : ∀ a, F.active a → ∀ b w : ℝ,
      scales.resolution ≤ b → b ≤ 1 → scales.resolution ≤ w → w ≤ 1 →
      scales.Kcensus ^ (100 : ℕ) * b ≤ w →
      (occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
      ((occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
          scales.Kcensus / (b ^ 3 * w ^ scales.dimension))
    -- the band of the ancestor signal
    {f₀ perror : ℝ}
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀ - scales.dimension * r| ≤ perror)
    (hCband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ scales.dimension *
      d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + ε₀) ≤ scales.Cband)
    (hresolved : d.N k ^ (-(d.L - p.r i)) ≤ 4 * scales.resolution) :
    SampleHbox hp RP radius scales.stripWidth beta scales.incidence.M scales.T scales.mesh
      scales.err scales.duration scales.bound scales.regularityFactor
      (scales.regularityFactor * scales.supportLoss) scales.nativeFailureBound scales.Lp scales.ρ := by
  classical
  intro E2 hE2 hratios
  have hqroot (root : Fin p.C) :
      (hp.frozenPacket root).unitFrame.q = (((2 : ℝ) ^ p.T (p.lev root))⁻¹) := rfl
  have hFmeas (root : Fin p.C) : MeasurableSet (p.F root) := by
    simpa only [hp.frozenPacket_counted] using (hp.frozenPacket root).measurable_counted
  have hE2meas : ∀ w, MeasurableSet (E2 w) := fun w => (hE2 w).1
  have hE2sub : ∀ w, E2 w ⊆ RP.E1 w := fun w => (hE2 w).2
  have hE2base : ∀ w, E2 w ⊆ Q.base w := fun w =>
    (hE2sub w).trans ((RP.E1_res w).trans (broadResidual_subset_base Rp w))
  -- the ancestor ratios, aggregated from the child ratios
  have hancRatios (a : Fin p.C) (ha : F.active a) :=
    ancestor_graph_record_ratios_of_child_ratios Q hp hH {a | F.active a} a ha c
      (by have := (hp.2.2.2.2.2.2.2 a).1; rw [F.level a ha] at this ⊢; omega) E2 hE2meas hE2base
      (fun a => (Q.coarseLaw (p.lev a) (F.code a)).map (labelledVelocityPalette finePv))
      (fun b hb hact => hratios b (by rw [hb, F.level a ha]) hact)
  -- the metadata on the cut
  let nmeta2 := nmeta.restrict hp hE2sub
  -- every active ancestor, prepared on its slice of the cut
  have hroot : ∀ a, F.active a → ∃ U : Set (Fin 4 → ℤ),
      (((d.ν k (p.γ a)).prod volume) (E2 (p.γ a) ∩ p.F a) ≤
        scales.regularityFactor * ((d.ν k (p.γ a)).prod volume)
          ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U) +
        (scales.regularityFactor * scales.supportLoss) *
          (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))) ∧
      (∀ x ∈ (E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U,
        ∀ y ∈ (E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U,
          ‖RP.row a (ancCode (d.N k) p a RP.graphMesh x) -
            RP.row a (ancCode (d.N k) p a RP.graphMesh y)‖ ≤
          scales.Lp * (‖clockParentCoordinates p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) x -
            clockParentCoordinates p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) y‖ +
              scales.ρ)) ∧
      MeasurableSet (qualBad hp a (i + c)
        ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U) (RP.row a)
          RP.graphMesh scales.incidence.M scales.T scales.mesh scales.bound scales.err
          scales.duration) ∧
      ((d.ν k (p.γ a)).prod volume)
        (((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U) ∩
          qualBad hp a (i + c) ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U)
            (RP.row a) RP.graphMesh scales.incidence.M scales.T scales.mesh scales.bound
            scales.err scales.duration) ≤
        scales.nativeFailureBound *
          (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) := by
    intro a ha
    have hlev : p.lev a = i := F.level a ha
    have hS : MeasurableSet (E2 (p.γ a) ∩ p.F a) := (hE2meas _).inter (hFmeas a)
    have hsource : MeasurableSet (RP.E1 (p.γ a) ∩ p.F a) := (RP.E1_meas _).inter (hFmeas a)
    have hSsource : E2 (p.γ a) ∩ p.F a ⊆ RP.E1 (p.γ a) ∩ p.F a :=
      inter_subset_inter_left _ (hE2sub _)
    have hSE : E2 (p.γ a) ∩ p.F a ⊆ d.E k (p.γ a) := fun z hz =>
      hHE _ (Rp.subset_H _ (RP.E1_res _ (hE2sub _ hz.1)))
    have hSbase : E2 (p.γ a) ∩ p.F a ⊆ Q.base (p.γ a) := fun z hz => hE2base _ hz.1
    -- the ratios of the ancestor on its slice, at the scales' graph mesh
    have hratio := hancRatios a ha
    rw [← hb] at hratio
    -- the fit
    have hfit' : ∀ x ∈ E2 (p.γ a) ∩ p.F a,
        |((((2 : ℝ) ^ p.T (p.lev a))⁻¹) / δ (d.N k) (p.r (p.lev a))) *
          Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
            ∑ j, RP.row a (clockParentCode p a (Parent.SignalGraph.ancestorSignal (d.N k) p a)
              scales.b x) j * (![1, Parent.v x.1 0, Parent.v x.1 1] : Fin 3 → ℝ) j| ≤
          scales.error := by
      intro x hx
      have h := hfit a ha x (hSsource hx)
      rw [hqaA] at h
      rw [hlev, hb]
      exact h
    -- the pure caps of the retained records at the scales' resolution
    have hpure' : ∀ query : ℕ, query ≤ scales.paletteFinest →
        ∀ w : ℝ, scales.resolution ≤ w → w ≤ 1 →
        ∀ (base : Fin 3 → ℤ) (hidden : ℤ) (D : Set (Fin 2 → ℤ)), MeasurableSet D →
        (((d.ν k (p.γ a)).prod volume).restrict (E2 (p.γ a) ∩ p.F a)) {z |
          (fun l => ⌊unshearedPacketBase p a z l / scales.resolution⌋) = base ∧
          ⌊physicalParentSignal (d.N k) p a (p.R a) z / w⌋ = hidden ∧
          Jets2.parameterCode (Jets2.dyadicParameterWidth query) (fun l => Parent.v z.1 l) ∈ D} ≤
        (ENNReal.ofReal (scales.Cpure * scales.resolution ^ 3 * w ^ scales.dimension) *
          ((nmeta.palette a).map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) D) *
            (ENNReal.ofReal ((hp.frozenPacket a).unitFrame.q) * d.ν k (p.γ a) (p.A a)) := by
      intro query hquery w hw hw1 base hidden D hD
      have hh := original_root_pure_caps_of_records (RP.data a ha) haux
        (by rw [hlev]; exact histop) (by rw [hlev]; exact hri) (by rw [hlev]; exact hdepth)
        hbaseRef hhiddenRef hRatio hcut hKcap (hFmeas a)
        (E2 (p.γ a) ∩ p.F a) (fun z hz => RP.kept a ha (hSsource hz)) inter_subset_right
        (nmeta.reference a ha) hfinePv hfineWidth hbaseLo hbaseHi hCpure query hquery w hw hw1
        base hidden D hD
      simpa only [hdimension, hqroot] using hh
    -- the census of the root slice, on the slice of the cut
    have hcensus' : ∀ b w : ℝ, scales.resolution ≤ b → b ≤ 1 → scales.resolution ≤ w → w ≤ 1 →
        scales.Kcensus ^ (100 : ℕ) * b ≤ w →
        (occupied (E2 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((occupied (E2 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
            scales.Kcensus / (b ^ 3 * w ^ scales.dimension) := by
      intro b w h1 h2 h3 h4 h5
      obtain ⟨hfin, hcard⟩ := hcensus a ha b w h1 h2 h3 h4 h5
      have hsub : occupied (E2 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w ⊆
          occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w := by
        rintro kk ⟨x, hx, rfl⟩
        exact ⟨x, hSsource hx, rfl⟩
      exact ⟨hfin.subset hsub, le_trans (by exact_mod_cast Set.ncard_le_ncard hsub hfin) hcard⟩
    -- the band of the ancestor signal
    have hband' : ∀ R : ℝ, scales.resolution ≤ R → R ≤ 8 * scales.ρ →
        ∀ U : Set P3, MeasurableSet U →
        ∀ center : P3 → ℝ, Measurable center →
        (((d.ν k (p.γ a)).prod volume).restrict (E2 (p.γ a) ∩ p.F a)) {z |
          unshearedPacketBase p a z ∈ U ∧
          |physicalParentSignal (d.N k) p a (p.R a) z - center (unshearedPacketBase p a z)| ≤ R} ≤
        (ENNReal.ofReal (scales.Cband * R ^ scales.dimension) * volume U) *
          (ENNReal.ofReal ((hp.frozenPacket a).unitFrame.q) * d.ν k (p.γ a) (p.A a)) := by
      intro Rw hRlo hRhi U hU center hcenter
      have hR0 : 0 < Rw := scales.hresolution.trans_le hRlo
      have hres : d.N k ^ (-(d.L - p.r (p.lev a))) ≤ 4 * Rw := by
        rw [hlev]; linarith
      have hh := Parent.SignalGraph.ancestor_rows_band Q hpure.ceiling hd hp a
        (by rw [hlev]; exact hri) (by rw [hlev]; exact hrLi) (E2 (p.γ a) ∩ p.F a) hS hSE hSbase
        inter_subset_right scales.hdim hprofile hR0 hres U hU center hcenter
      have hset : {z | unshearedPacketBase p a z ∈ U ∧
          |physicalParentSignal (d.N k) p a (p.R a) z - center (unshearedPacketBase p a z)| ≤ Rw} =
          {x | unshearedPacketBase p a x ∈ U ∧
            |clockParentSignal p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) x -
              center (unshearedPacketBase p a x)| ≤ Rw} := by
        ext x
        simp only [mem_ofPred_eq, ← Parent.SignalGraph.ancestorSignal_clock (d.N k) p a x, one_mul]
      rw [hset]
      refine hh.trans ?_
      have hC : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ scales.dimension *
          d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + ε₀) * 1 ^ (-scales.dimension) *
            Rw ^ scales.dimension ≤ scales.Cband * Rw ^ scales.dimension := by
        rw [Real.one_rpow, mul_one]
        exact mul_le_mul_of_nonneg_right hCband (Real.rpow_nonneg hR0.le _)
      calc ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ scales.dimension *
            d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + ε₀) * 1 ^ (-scales.dimension) *
              Rw ^ scales.dimension) *
            (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) * volume U
          ≤ ENNReal.ofReal (scales.Cband * Rw ^ scales.dimension) *
            (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) * volume U := by
            gcongr
        _ = (ENNReal.ofReal (scales.Cband * Rw ^ scales.dimension) * volume U) *
            (ENNReal.ofReal ((hp.frozenPacket a).unitFrame.q) * d.ν k (p.γ a) (p.A a)) := by
            rw [hqroot]; ring
    obtain ⟨U, hU, hSrc, hmass, hLip, hbad, hfail⟩ := prepare_native_root_from_original_data hd hp a
      hVmax (RP.E1 (p.γ a) ∩ p.F a) hsource inter_subset_right (path_R_degree hp a)
      (fun z hz => hvelocity _ z (RP.E1_res _ hz.1)) (E2 (p.γ a) ∩ p.F a) hS hSsource scales
      hcoeffH hVmaxU (RP.row a) (fun cd j => (RP.row_bound a cd j).trans hBrow) hfit'
      (nmeta2.palette a) (nmeta2.pre a ha).floors (nmeta2.pre a ha).tables
      ((Q.coarseLaw (p.lev a) (F.code a)).map (labelledVelocityPalette finePv)) finePv radius
      (ENNReal.ofReal ((8 * fraction) / cut) / beta) (ENNReal.ofReal ((8 * paletteRatio) / cut) / beta)
      hratio hstripCoeff hpaletteCoeff (nmeta.reference a ha) hfinePv hfineWidth hpure' hcensus'
      hband' (i + c) (by omega) hib (fun z hz => RP.E1_end a ha z (hSsource hz))
      (fun z hz => hH _ (Rp.subset_H _ (RP.E1_res _ (hE2sub _ hz.1))))
      (by rw [hlev]; exact hT)
    set Mq := scales.incidence.M with hMq
    rw [hb] at hmass hLip hbad hfail
    refine ⟨U, ?_, hLip, hbad, ?_⟩
    · rw [hqroot, mul_comm (ENNReal.ofReal _) (d.ν k (p.γ a) (p.A a))] at hmass
      exact hmass
    · rw [hqroot, mul_comm (ENNReal.ofReal _) (d.ν k (p.γ a) (p.A a))] at hfail
      exact hfail
  obtain ⟨U, hU⟩ := exists_codes_of_per_root (fun a => F.active a) _ hroot
  exact ⟨U, fun a ha => (hU a ha).1, fun a ha => (hU a ha).2.1, fun a ha => (hU a ha).2.2.1,
    fun a ha => (hU a ha).2.2.2⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
