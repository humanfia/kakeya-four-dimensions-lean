-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleAssembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.ChildRecordRatioStates

/-!
# One sample of the relative source, from its root package (session x1082)

`RootPackage` is what the root stage of a sample hands over: the root survivors `E1` (inside the
broad residual and the multiscale core source, block endpoints removed), the record source of
every active ancestor containing its slice, the ancestor rows with their fit on the slice, and the
caps of every child slice. `samplePost_of_rootPackage` composes the remaining stages:

1. the states of all children (`child_states_of_records`);
2. the regularity/qualification stage on the post-state slices (an input `hbox`: whole graph codes
   `U a`, the regularity mass bound, Lipschitz rows on `Src_a`, the native failure);
3. the base-only lists (`lists_of_lipschitz`);
4. `post_state_assembly`, which returns the literal `StagesProducer` existential.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual
  labelledVelocityPalette)
open scoped ENNReal BigOperators

noncomputable section

section Package

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}

/-- **The root package of a sample.** -/
structure RootPackage (Q : PreparedAngularPath d k p m H u τ) {i stop : ℕ} {meshF envF : ℝ}
    {θF : ENNReal} (F : PaletteFamily Q i stop meshF envF θF) {rF frF : ℝ}
    (Rp : BroadResidual F rF frF) (c : ℕ) (K θ ε aA q d₁ h' a' : ℝ)
    (Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ)
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    (core : BroadMultiscaleCoreSource d k p original n depth Kcore e R) where
  E1 : Fin (d.W k) → Set Ev
  E1_meas : ∀ w, MeasurableSet (E1 w)
  E1_res : ∀ w, E1 w ⊆ Rp.residual w
  E1_core : ∀ w, E1 w ⊆ core.current w
  E1_end : ∀ a, F.active a → ∀ z ∈ E1 (p.γ a) ∩ p.F a,
    z ∉ p.oldEndpoints a ∧ z ∉ p.levelEndpoints (i + c)
  Edata : Fin p.C → Set Ev
  data : (a : Fin p.C) → F.active a → OriginalAncestorRecordSource F a (Edata a) Krecord
    baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension Kcap
  Edata_base : ∀ a, F.active a → Edata a ⊆ Q.base (p.γ a)
  kept : ∀ a (ha : F.active a), E1 (p.γ a) ∩ p.F a ⊆ (data a ha).kept
  row : Fin p.C → (Fin 4 → ℤ) → Fin 3 → ℝ
  Brow : ℝ
  Brow_nonneg : 0 ≤ Brow
  row_bound : ∀ a cd j, |row a cd j| ≤ Brow
  graphMesh : ℝ
  fit : ∀ a, F.active a → ∀ x ∈ E1 (p.γ a) ∩ p.F a,
    |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
      ∑ j : Fin 3, row a (ancCode (d.N k) p a graphMesh x) j *
        (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤ θ
  caps : ∀ b, p.lev b = i + c → F.active (p.par^[c] b) → ∀ Se : Set Ev, MeasurableSet Se →
    Se ⊆ E1 (p.γ b) ∩ p.F b →
    CapClauses K ε d₁ h' a'
      (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
      (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
      (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
        O204.Split.δ (d.N k) (p.r (p.lev b))) Se

/-- **Restricting a root package.** Every field of a root package is hereditary under shrinking
the root survivors to a measurable subfamily (e.g. after further root preparations). -/
def RootPackage.restrict {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {meshF envF : ℝ}
    {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF} {rF frF : ℝ}
    {Rp : BroadResidual F rF frF} {c : ℕ} {K θ ε aA q d₁ h' a' : ℝ}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    {core : BroadMultiscaleCoreSource d k p original n depth Kcore e R}
    (RP : RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap core)
    (E1' : Fin (d.W k) → Set Ev) (hmeas : ∀ w, MeasurableSet (E1' w)) (hsub : ∀ w, E1' w ⊆ RP.E1 w) :
    RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap core where
  E1 := E1'
  E1_meas := hmeas
  E1_res := fun w => (hsub w).trans (RP.E1_res w)
  E1_core := fun w => (hsub w).trans (RP.E1_core w)
  E1_end := fun a ha z hz => RP.E1_end a ha z ⟨hsub _ hz.1, hz.2⟩
  Edata := RP.Edata
  data := RP.data
  Edata_base := RP.Edata_base
  kept := fun a ha _ hz => RP.kept a ha ⟨hsub _ hz.1, hz.2⟩
  row := RP.row
  Brow := RP.Brow
  Brow_nonneg := RP.Brow_nonneg
  row_bound := RP.row_bound
  graphMesh := RP.graphMesh
  fit := fun a ha x hx => RP.fit a ha x ⟨hsub _ hx.1, hx.2⟩
  caps := fun b hb hact Se hSe hSeSub => RP.caps b hb hact Se hSe
    (fun _ hz => ⟨hsub _ (hSeSub hz).1, (hSeSub hz).2⟩)

/-- **Per-root cuts of a root package.** Cuts of the root slices of the active ancestors, each
losing at most a charge against the full reference of its ancestor, give a restricted root
package whose slices are exactly the cuts, at a total weighted loss of the charge. -/
theorem RootPackage.cut_per_root {Q : PreparedAngularPath d k p m H u τ} (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {i stop : ℕ} {meshF envF : ℝ}
    {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF} {rF frF : ℝ}
    {Rp : BroadResidual F rF frF} {c : ℕ} {K θ ε aA q d₁ h' a' : ℝ}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    {core : BroadMultiscaleCoreSource d k p original n depth Kcore e R}
    (RP : RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap core)
    (G : Fin p.C → Set Ev) (hGmeas : ∀ a, F.active a → MeasurableSet (G a))
    (hGsub : ∀ a, F.active a → G a ⊆ RP.E1 (p.γ a) ∩ p.F a) (charge : ENNReal)
    (hGmass : ∀ a, F.active a → ((d.ν k (p.γ a)).prod volume) (RP.E1 (p.γ a) ∩ p.F a) ≤
      ((d.ν k (p.γ a)).prod volume) (G a) +
        charge * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))) :
    ∃ (E1' : Fin (d.W k) → Set Ev) (hmeas : ∀ w, MeasurableSet (E1' w))
      (hsub : ∀ w, E1' w ⊆ RP.E1 w),
      (∀ a, F.active a → (RP.restrict E1' hmeas hsub).E1 (p.γ a) ∩ p.F a = G a) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) ≤
        (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) ((RP.restrict E1' hmeas hsub).E1 w)) +
          charge := by
  classical
  have hbase (w : Fin (d.W k)) : RP.E1 w ⊆ Q.base w := fun z hz =>
    broadResidual_subset_base Rp w (RP.E1_res w hz)
  have hcover : ∀ w, ∀ z ∈ RP.E1 w, ∃ a ∈ {a : Fin p.C | F.active a}, p.γ a = w ∧ z ∈ p.F a := by
    intro w z hz
    obtain ⟨a, -, hγ, hzF, hact, -⟩ := Rp.witness w z (RP.E1_res w hz)
    exact ⟨a, hact, hγ, hzF⟩
  obtain ⟨E1', hE1', hmass', hslice'⟩ := assemble_same_level_whole_cuts_charge Q hd hp
    {a : Fin p.C | F.active a} i (fun a ha => F.level a ha) RP.E1 RP.E1_meas hbase hcover G
    (fun a ha => hGmeas a ha) 1 charge (fun a ha => by
      have heq : (RP.E1 (p.γ a) ∩ p.F a) ∩ G a = G a := inter_eq_right.mpr (hGsub a ha)
      rw [heq, one_mul]; exact hGmass a ha)
  refine ⟨E1', fun w => (hE1' w).1, fun w => (hE1' w).2, fun a ha => ?_, ?_⟩
  · change E1' (p.γ a) ∩ p.F a = G a
    rw [hslice' a ha]; exact inter_eq_right.mpr (hGsub a ha)
  · have h := hmass'
    simp only [one_mul] at h
    exact h

/-- **Per-root choices of whole codes give one family of codes.** -/
theorem exists_codes_of_per_root {C₀ : ℕ} {X : Type*} (active : Fin C₀ → Prop)
    (P : Fin C₀ → Set X → Prop) (h : ∀ a, active a → ∃ U : Set X, P a U) :
    ∃ U : Fin C₀ → Set X, ∀ a, active a → P a (U a) := by
  classical
  refine ⟨fun a => if ha : active a then (h a ha).choose else ∅, fun a ha => ?_⟩
  simp only [ha, ↓reduceDIte]
  exact (h a ha).choose_spec

/-- **The regularity/qualification input of `samplePost_of_rootPackage`** (named, for the native
stage that supplies it). -/
def SampleHbox {Q : PreparedAngularPath d k p m H u τ}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {i stop : ℕ} {meshF envF : ℝ}
    {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF} {rF frF : ℝ}
    {Rp : BroadResidual F rF frF} {c : ℕ} {K θ ε aA q d₁ h' a' : ℝ}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    {core : BroadMultiscaleCoreSource d k p original n depth Kcore e R}
    (RP : RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap core)
    (radius stripWidth : ℝ) (beta : ENNReal)
    (M Tq : ℕ) (qmesh qerror qduration : ℝ) (qbound : ℤ)
    (Pfac chargeR η : ENNReal) (Lp ρ : ℝ) : Prop :=
  ∀ E2 : Fin (d.W k) → Set Ev, (∀ w, MeasurableSet (E2 w) ∧ E2 w ⊆ RP.E1 w) →
    (∀ b, p.lev b = i + c → F.active (p.par^[c] b) →
      GraphRecordRatios p (d.N k) (p.par^[c] b) RP.graphMesh finePv radius stripWidth
        (ENNReal.ofReal ((8 * fraction) / cut) / beta)
        (ENNReal.ofReal ((8 * paletteRatio) / cut) / beta)
        ((d.ν k (p.γ b)).prod volume) (E2 (p.γ b) ∩ p.F b)
        ((Q.coarseLaw (p.lev (p.par^[c] b)) (F.code (p.par^[c] b))).map
          (labelledVelocityPalette finePv))) →
    ∃ U : Fin p.C → Set (Fin 4 → ℤ),
      (∀ a, F.active a → ((d.ν k (p.γ a)).prod volume) (E2 (p.γ a) ∩ p.F a) ≤
        Pfac * ((d.ν k (p.γ a)).prod volume)
          ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a) +
        chargeR * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))) ∧
      (∀ a, F.active a →
        ∀ x ∈ (E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a,
        ∀ y ∈ (E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a,
          ‖RP.row a (ancCode (d.N k) p a RP.graphMesh x) -
            RP.row a (ancCode (d.N k) p a RP.graphMesh y)‖ ≤
          Lp * (‖clockParentCoordinates p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) x -
            clockParentCoordinates p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) y‖ + ρ)) ∧
      (∀ a, F.active a → MeasurableSet (qualBad hp a (i + c)
        ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a) (RP.row a)
          RP.graphMesh M Tq qmesh qbound qerror qduration)) ∧
      ∀ a, F.active a → ((d.ν k (p.γ a)).prod volume)
        (((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a) ∩
          qualBad hp a (i + c) ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a)
            (RP.row a) RP.graphMesh M Tq qmesh qbound qerror qduration) ≤
        η * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))

/-- **One sample from its root package.** -/
theorem samplePost_of_rootPackage (Q : PreparedAngularPath d k p m H u τ) {ε₀ : ℝ}
    (hpure : Q.uniformPureBounds ε₀) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF}
    {rF frF : ℝ} {Rp : BroadResidual F rF frF} {c : ℕ} (hib : i + c ≤ m - 1)
    (hstop : i + c ≤ stop)
    {K θ ε pv aA q d₁ h' a' : ℝ} (hK : 0 < K) (hθ : 0 < θ) (heps : 0 < ε) (haA : 0 < aA)
    (hq : 0 < q)
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    {core : BroadMultiscaleCoreSource d k p original n depth Kcore e R}
    (RP : RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap core)
    -- the record/state numerics
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    (hgraph : 0 < RP.graphMesh) (hfinePv : 0 < finePv) (hpv : finePv ≤ pv)
    (hgraphBase : 3 * baseRef ≤ RP.graphMesh) (hgraphHidden : 3 * hiddenRef ≤ RP.graphMesh)
    (hphysicalBase : ∀ b, p.lev b = i + c →
      3 * ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev (p.par^[c] b))) * baseRef ≤ ε)
    (hphysicalHidden : ∀ b, p.lev b = i + c →
      3 * (δ (d.N k) (p.r (p.lev (p.par^[c] b))) / δ (d.N k) (p.r (p.lev b))) * hiddenRef ≤
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev b))) * ε)
    (beta : ENNReal) (hbeta : beta ≠ 0) (hbetaTop : beta ≠ ⊤)
    (hstripWidth : ∀ b, p.lev b = i + c →
      (K / 4) ^ (-100 : ℝ) * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
        frontRadius * ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)) * |(p.Q (p.par^[c] b)).det|))
    (hstripRatio : ENNReal.ofReal ((8 * fraction) / cut) / beta ≤ (1 / 2000000000000 : ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8 * paletteRatio) / cut) / beta ≤ ENNReal.ofReal (K / 4))
    (hBK : RP.Brow ≤ K)
    (radius stripWidth : ℝ) (hNormalizedWidth : (6 * p.κ) * radius ≤ frontRadius)
    (hOriginalWidth : ∀ b, p.lev b = i + c →
      stripWidth * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
        frontRadius * ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)) * |(p.Q (p.par^[c] b)).det|))
    -- the regularity/qualification stage on the post-state slices
    (M Tq : ℕ) (qmesh qerror qduration : ℝ) (qbound : ℤ)
    (Pfac chargeR η : ENNReal) (hPfac : Pfac ≠ ⊤) (hPfac0 : Pfac ≠ 0) (hchargeR : chargeR ≠ ⊤)
    (hη : η ≠ ⊤) {Lp ρ : ℝ} (hLp : 0 ≤ Lp)
    (hbox : ∀ E2 : Fin (d.W k) → Set Ev, (∀ w, MeasurableSet (E2 w) ∧ E2 w ⊆ RP.E1 w) →
      (∀ b, p.lev b = i + c → F.active (p.par^[c] b) →
        GraphRecordRatios p (d.N k) (p.par^[c] b) RP.graphMesh finePv radius stripWidth
          (ENNReal.ofReal ((8 * fraction) / cut) / beta)
          (ENNReal.ofReal ((8 * paletteRatio) / cut) / beta)
          ((d.ν k (p.γ b)).prod volume) (E2 (p.γ b) ∩ p.F b)
          ((Q.coarseLaw (p.lev (p.par^[c] b)) (F.code (p.par^[c] b))).map
            (labelledVelocityPalette finePv))) →
      ∃ U : Fin p.C → Set (Fin 4 → ℤ),
        (∀ a, F.active a → ((d.ν k (p.γ a)).prod volume) (E2 (p.γ a) ∩ p.F a) ≤
          Pfac * ((d.ν k (p.γ a)).prod volume)
            ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a) +
          chargeR * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))) ∧
        (∀ a, F.active a →
          ∀ x ∈ (E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a,
          ∀ y ∈ (E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a,
            ‖RP.row a (ancCode (d.N k) p a RP.graphMesh x) -
              RP.row a (ancCode (d.N k) p a RP.graphMesh y)‖ ≤
            Lp * (‖clockParentCoordinates p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) x -
              clockParentCoordinates p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) y‖ + ρ)) ∧
        (∀ a, F.active a → MeasurableSet (qualBad hp a (i + c)
          ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a) (RP.row a)
            RP.graphMesh M Tq qmesh qbound qerror qduration)) ∧
        ∀ a, F.active a → ((d.ν k (p.γ a)).prod volume)
          (((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a) ∩
            qualBad hp a (i + c) ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a RP.graphMesh ⁻¹' U a)
              (RP.row a) RP.graphMesh M Tq qmesh qbound qerror qduration) ≤
          η * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)))
    -- the lists at the middle depth of the core source
    (hHEc : ∀ w, original w ⊆ d.E k w) (hHbasec : ∀ w, original w ⊆ Q.base w)
    (hKcore : 2304 ≤ Kcore) (hmax : max p.κ (d.K k) ≤ Kcore) (hpower : d.N k ^ (τ + ε₀) ≤ Kcore)
    (hκK : 3 * p.κ ≤ Kcore) {D J : ℕ} (hD : 5186 ≤ D) (hjets : Analytic.DenseJetBound D J)
    (jmid : Fin n) (hmidb : ∀ b, p.lev b = i + c → depth jmid ≤ p.lev b)
    (hmida : ∀ b, p.lev b = i + c → p.lev b - c ≤ depth jmid)
    (hrmid : 0 ≤ p.r (depth jmid)) (hrLmid : p.r (depth jmid) ≤ d.L)
    (hwidthmid : δ (d.N k) (p.r (depth jmid)) ≤ δ (d.N k) (p.r i))
    (hsmall : ∀ b, p.lev b = i + c →
      ((aA / q) * Lp) * ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
          ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)))⁻¹) * (2 * θ) +
        (2 * (Kcore ^ 14 * (Kcore ^ 6)⁻¹ * (δ (d.N k) (p.r (depth jmid)) /
          δ (d.N k) (p.r (p.lev (p.par^[c] b))))) +
          ((Kcore ^ (3 * R + 58 + 7)) ^ J * (p.κ + Kcore ^ 14 * (Kcore ^ 6)⁻¹)) *
            (Kcore ^ R * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
              ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
                ((2 : ℝ) ^ p.T (p.lev (p.par^[p.lev b - depth jmid] b)))⁻¹) * (6 * θ))))) +
        ρ) ≤ (aA / q) * θ)
    (hcount : (Kcore ^ 10 * (2 * Kcore ^ (3 * R + 18))) * 9 ^ 3 ≤ K)
    -- the qualification numerics
    (hqmesh : 0 ≤ qmesh) (hqbound : 0 ≤ qbound)
    (hcoeff : Parent.QualificationClock.coefficientCost M * (qmesh * qbound) ≤ K)
    (herror : qerror ≤ θ)
    (hduration : ∀ b, p.lev b = i + c → 1 / K ≤ qduration / ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) /
      (((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)))⁻¹)))
    -- the final mass
    (hfinal : Pfac * (ENNReal.ofReal (2 / K) + 10000 * η) + chargeR + 6561 * beta ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) :
    ∃ (density : ℝ) (E : Fin (d.W k) → Set Ev), 0 < density ∧
      (∀ w, E w ⊆ Rp.residual w) ∧
      ENNReal.ofReal density + ENNReal.ofReal density ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w) ∧
      ∀ b : Fin p.C, p.lev b = i + c → F.active (p.par^[c] b) → d.ν k (p.γ b) (p.A b) ≠ 0 →
        ENNReal.ofReal density *
            (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) ≤
          ((d.ν k (p.γ b)).prod volume) (E (p.γ b) ∩ p.F b) →
        ∃ (Se Er bad : Set Ev) (st : Ev → ℕ) (G : ℕ → Fin 3 → ℝ) (pal : Measure (Fin 2 → ℤ)),
          Se ⊆ E (p.γ b) ∩ p.F b ∧ Se ⊆ Er ∧
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) /
              ENNReal.ofReal K ≤ (((d.ν k (p.γ b)).prod volume).restrict Se) Set.univ ∧
          CapClauses K ε d₁ h' a'
            (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
            (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
            (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
              O204.Split.δ (d.N k) (p.r (p.lev b))) Se ∧
          StateClauses K ε pv (d.ν k (p.γ b))
            (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
            (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
              O204.Split.δ (d.N k) (p.r (p.lev b))) Se st pal ∧
          RowClauses K θ aA q (p.R (p.par^[c] b))
            (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b)) Se Er st G ∧
          QualClauses M K θ aA q (p.j b) ((2 : ℝ) ^ p.T (p.lev b))⁻¹ (d.ν k (p.γ b))
            Se Er bad st G := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hE1base (w : Fin (d.W k)) : RP.E1 w ⊆ Q.base w := fun z hz =>
    broadResidual_subset_base Rp w (RP.E1_res w hz)
  -- ancestry of the children
  have hanc : ∀ b ∈ {b : Fin p.C | p.lev b = i + c ∧ F.active (p.par^[c] b)},
      F.active (p.par^[c] b) ∧ p.γ b = p.γ (p.par^[c] b) ∧ p.lev b ≤ stop := by
    intro b hb
    obtain ⟨-, hγ, -⟩ := Broad.iterate_par_spec hp.toOriginal c b (show c ≤ p.lev b by
      rw [hb.1]; omega)
    exact ⟨hb.2, hγ.symm, by rw [hb.1]; exact hstop⟩
  have hFanc (b : Fin p.C) (hb : p.lev b = i + c) : p.F b ⊆ p.F (p.par^[c] b) :=
    (Broad.iterate_par_spec hp.toOriginal c b (show c ≤ p.lev b by rw [hb]; omega)).2.2
  have hlevanc (b : Fin p.C) (hb : p.lev b = i + c) : p.lev (p.par^[c] b) = i := by
    have h := (Broad.iterate_par_spec hp.toOriginal c b (show c ≤ p.lev b by rw [hb]; omega)).1
    change p.lev (p.par^[c] b) = p.lev b - c at h
    omega
  have hkept : ∀ b (hb : b ∈ {b : Fin p.C | p.lev b = i + c ∧ F.active (p.par^[c] b)}),
      RP.E1 (p.γ b) ∩ p.F b ⊆ (RP.data (p.par^[c] b) (hanc b hb).1).kept := by
    intro b hb z hz
    apply RP.kept (p.par^[c] b) (hanc b hb).1
    exact ⟨by rw [← (hanc b hb).2.1]; exact hz.1, hFanc b hb.1 hz.2⟩
  -- 1. the states of all children
  obtain ⟨E2, localKeep, state, value, palette, hE2, hloss2, hslices⟩ :=
    child_states_with_ratios Q hd hp hHE hH
      {b : Fin p.C | p.lev b = i + c ∧ F.active (p.par^[c] b)} (i + c) (fun b hb => hb.1)
      (fun b => p.par^[c] b) hanc RP.data RP.Edata_base RP.E1 RP.E1_meas hE1base hkept
      hK heps haA hq hbaseRef hhiddenRef hcut hfr hgraph hfinePv hpv hgraphBase hgraphHidden
      (fun b hb => hphysicalBase b hb.1) (fun b hb => hphysicalHidden b hb.1) beta hbeta hbetaTop
      (fun b hb => hstripWidth b hb.1) hstripRatio hpaletteRatio RP.row RP.Brow_nonneg
      RP.row_bound radius stripWidth hNormalizedWidth (fun b hb => hOriginalWidth b hb.1)
  -- 2. the regularity/qualification stage
  obtain ⟨U, hreg, hLip, hbadMeas, hfail⟩ := hbox E2 hE2
    (fun b hlev hact => (hslices b ⟨hlev, hact⟩).2.2.2.2.2)
  -- 3. the mass after the states
  have hfinal2 : Pfac * (ENNReal.ofReal (2 / K) + 10000 * η) + chargeR ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E2 w) := by
    have hsplit : (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) ≤
        (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E2 w)) +
          ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w \ E2 w) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun w _ => ?_
      rw [← mul_add]
      refine mul_le_mul' le_rfl ((measure_mono (fun z hz => ?_)).trans
        (measure_union_le (E2 w) (RP.E1 w \ E2 w)))
      by_cases h2 : z ∈ E2 w
      · exact Or.inl h2
      · exact Or.inr ⟨hz, h2⟩
    have h6561 : (6561 : ENNReal) * beta ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hbetaTop
    exact (ENNReal.add_le_add_iff_right h6561).mp
      (hfinal.trans (hsplit.trans (add_le_add le_rfl hloss2)))
  -- 4. the post-state assembly
  refine post_state_assembly Q Rp hd hp hH c hib hK haA hq RP.E1 RP.E1_res RP.E1_end RP.row
    RP.graphMesh hBK RP.fit RP.caps E2 hE2 state value palette
    (fun b hb => ⟨(hslices b hb).2.1, (hslices b hb).2.2.1, (hslices b hb).2.2.2.1,
      (hslices b hb).2.2.2.2.1⟩) U Pfac chargeR hPfac hPfac0 hchargeR hreg ?_ M Tq qmesh
    qerror qduration qbound hqmesh hqbound hcoeff herror hduration hbadMeas η hη hfail hfinal2
  -- the lists
  intro b hlev hact
  have hc : c ≤ p.lev b := by rw [hlev]; omega
  have hSrc : (E2 (p.γ (p.par^[c] b)) ∩ p.F (p.par^[c] b)) ∩
      ancCode (d.N k) p (p.par^[c] b) RP.graphMesh ⁻¹' U (p.par^[c] b) ⊆
      core.current (p.γ (p.par^[c] b)) ∩ p.F (p.par^[c] b) := fun z hz =>
    ⟨RP.E1_core _ ((hE2 _).2 hz.1.1), hz.1.2⟩
  have hwidth : δ (d.N k) (p.r (depth jmid)) ≤
      δ (d.N k) (p.r (p.lev (p.par^[c] b))) := by
    rw [hlevanc b hlev]; exact hwidthmid
  exact lists_of_lipschitz core Q hpure hd hp hHEc hHbasec hKcore hmax hpower hκK hD hjets c b hc
    jmid (hmidb b hlev) (hmida b hlev) hrmid hrLmid hwidth _ hSrc (RP.row (p.par^[c] b))
    RP.graphMesh hLp hθ haA hq (hLip _ hact) (hsmall b hlev) hcount

/-- **The root package from per-ancestor slices.** Given the records' kept family `K2` inside the
core source and, for every active ancestor, a slice of `K2` carrying a fraction of its mass up to
a full-reference charge, with rows, fit, endpoints removed and child caps, the assembled family is
a root package whose slices are exactly the given ones. -/
theorem rootPackage_of_slices (Q : PreparedAngularPath d k p m H u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF}
    {rF frF : ℝ} {Rp : BroadResidual F rF frF} {c : ℕ}
    {K θ ε aA q d₁ h' a' : ℝ}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    (core : BroadMultiscaleCoreSource d k p original n depth Kcore e R)
    (hcoreRes : ∀ w, core.current w ⊆ Rp.residual w)
    (data : (a : Fin p.C) → F.active a → OriginalAncestorRecordSource F a
      (core.current (p.γ a) ∩ p.F a) Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius
        fraction χ finest dimension Kcap)
    (K2 : Fin (d.W k) → Set Ev) (hK2 : ∀ w, MeasurableSet (K2 w) ∧ K2 w ⊆ core.current w)
    (hK2slice : ∀ a (ha : F.active a), K2 (p.γ a) ∩ p.F a = (data a ha).kept)
    (G : Fin p.C → Set Ev) (hGmeas : ∀ a, F.active a → MeasurableSet (G a))
    (hGsub : ∀ a, F.active a → G a ⊆ K2 (p.γ a) ∩ p.F a) (cfrac charge : ENNReal)
    (hGmass : ∀ a, F.active a → ((d.ν k (p.γ a)).prod volume) (K2 (p.γ a) ∩ p.F a) ≤
      cfrac * ((d.ν k (p.γ a)).prod volume) (G a) +
        charge * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)))
    (hGend : ∀ a, F.active a → ∀ z ∈ G a, z ∉ p.oldEndpoints a ∧ z ∉ p.levelEndpoints (i + c))
    (row : Fin p.C → (Fin 4 → ℤ) → Fin 3 → ℝ) (Brow : ℝ) (hBrow : 0 ≤ Brow)
    (hrow : ∀ a cd j, |row a cd j| ≤ Brow) (graphMesh : ℝ)
    (hfit : ∀ a, F.active a → ∀ x ∈ G a,
      |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
        ∑ j : Fin 3, row a (ancCode (d.N k) p a graphMesh x) j *
          (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤ θ)
    (hcaps : ∀ b, p.lev b = i + c → F.active (p.par^[c] b) → ∀ Se : Set Ev, MeasurableSet Se →
      Se ⊆ G (p.par^[c] b) ∩ p.F b →
      CapClauses K ε d₁ h' a'
        (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
        (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
        (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
          O204.Split.δ (d.N k) (p.r (p.lev b))) Se) :
    ∃ RP : RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
        cut frontRadius fraction χ finest dimension Kcap core,
      (∀ a, F.active a → RP.E1 (p.γ a) ∩ p.F a = G a) ∧ RP.graphMesh = graphMesh ∧
      RP.row = row ∧ RP.Brow = Brow ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (K2 w)) ≤
        cfrac * (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) + charge := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hK2base (w : Fin (d.W k)) : K2 w ⊆ Q.base w := fun z hz =>
    broadResidual_subset_base Rp w (hcoreRes w ((hK2 w).2 hz))
  have hcover : ∀ w, ∀ z ∈ K2 w, ∃ a ∈ {a : Fin p.C | F.active a}, p.γ a = w ∧ z ∈ p.F a := by
    intro w z hz
    obtain ⟨a, -, hγ, hzF, hact, -⟩ := Rp.witness w z (hcoreRes w ((hK2 w).2 hz))
    exact ⟨a, hact, hγ, hzF⟩
  obtain ⟨E1, hE1, hmass1, hslice1⟩ := assemble_same_level_whole_cuts_charge Q hd hp
    {a : Fin p.C | F.active a} i (fun a ha => F.level a ha) K2 (fun w => (hK2 w).1) hK2base
    hcover G (fun a ha => hGmeas a ha) cfrac charge (fun a ha => by
      have heq : (K2 (p.γ a) ∩ p.F a) ∩ G a = G a := inter_eq_right.mpr (hGsub a ha)
      rw [heq]; exact hGmass a ha)
  have hslice (a : Fin p.C) (ha : F.active a) : E1 (p.γ a) ∩ p.F a = G a := by
    rw [hslice1 a ha]; exact inter_eq_right.mpr (hGsub a ha)
  -- the ancestry of children
  have hanc (b : Fin p.C) (hb : p.lev b = i + c) :
      p.γ (p.par^[c] b) = p.γ b ∧ p.F b ⊆ p.F (p.par^[c] b) := by
    obtain ⟨-, hγ, hFb⟩ := Broad.iterate_par_spec hp.toOriginal c b (show c ≤ p.lev b by omega)
    exact ⟨hγ, hFb⟩
  refine ⟨{
    E1 := E1
    E1_meas := fun w => (hE1 w).1
    E1_res := fun w => (hE1 w).2.trans (((hK2 w).2).trans (hcoreRes w))
    E1_core := fun w => (hE1 w).2.trans (hK2 w).2
    E1_end := fun a ha z hz => hGend a ha z (by rw [← hslice a ha]; exact hz)
    Edata := fun a => core.current (p.γ a) ∩ p.F a
    data := data
    Edata_base := fun a _ z hz => broadResidual_subset_base Rp _ (hcoreRes _ hz.1)
    kept := fun a ha z hz => by
      rw [← hK2slice a ha]
      have hz' : z ∈ G a := by rw [← hslice a ha]; exact hz
      exact hGsub a ha hz'
    row := row
    Brow := Brow
    Brow_nonneg := hBrow
    row_bound := hrow
    graphMesh := graphMesh
    fit := fun a ha x hx => hfit a ha x (by rw [← hslice a ha]; exact hx)
    caps := fun b hb hact Se hSe hSeSub => hcaps b hb hact Se hSe (fun z hz => by
      obtain ⟨hγ, hFb⟩ := hanc b hb
      have hz1 : z ∈ E1 (p.γ (p.par^[c] b)) ∩ p.F (p.par^[c] b) :=
        ⟨by rw [hγ]; exact (hSeSub hz).1, hFb (hSeSub hz).2⟩
      rw [hslice _ hact] at hz1
      exact ⟨hz1, (hSeSub hz).2⟩) }, fun a ha => hslice a ha, rfl, rfl, rfl, hmass1⟩

end Package

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
