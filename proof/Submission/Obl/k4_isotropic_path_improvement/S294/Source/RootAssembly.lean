-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RootAssembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootSlice
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleAssembly

/-!
# The root package of a sample (session x1082)

`rootPackage_exists`: from the records' kept family inside the core source (x1095's
`exists_all_ancestor_record_sources`), a census cut of every active ancestor's kept slice with its
occupancy (for the MK4 rows) and the child caps on it, every active ancestor gets its root slice
(`root_slice_full`: MK4 rows with renewal and band, endpoints removed), and the slices assemble
into a `RootPackage` (`rootPackage_of_slices`) with `M(K2) ≤ (1 - gf)⁻¹ M(E1) + charge`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual)
open scoped ENNReal

noncomputable section

section Path

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem path_R_degree
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (a : Fin p.C) : (p.R a).totalDegree ≤ 2 := by
  rcases (hp.2.2.2.2.2.2.2 a).2.2 with ⟨_, _, _, _, hR, _⟩
  exact hR

theorem path_A_meas
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (a : Fin p.C) : MeasurableSet (p.A a) :=
  (hp.2.2.2.2.2.2.2 a).2.2.2.2.2.2.2.2.1

end Path

open Submission.Lib.K4ParentSignalPreparation.Census in
/-- **Occupancy bounds pass to subsets.** -/
theorem occupied_bound_mono {Ω : Type*} {S S' : Set Ω} (hSS : S ⊆ S') (z : Ω → Fin 3 → ℝ)
    (X : Ω → ℝ) {fineMesh Kc dimension : ℝ}
    (h : ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 → Kc ^ (100 : ℕ) * b ≤ 1 * w →
      (occupied S' z X b w).Finite ∧ ((occupied S' z X b w).ncard : ℝ) ≤ Kc / (b ^ 3 * w ^ dimension)) :
    ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 → Kc ^ (100 : ℕ) * b ≤ 1 * w →
      (occupied S z X b w).Finite ∧ ((occupied S z X b w).ncard : ℝ) ≤ Kc / (b ^ 3 * w ^ dimension) := by
  intro b w h1 h2 h3 h4 h5
  obtain ⟨hfin, hcard⟩ := h b w h1 h2 h3 h4 h5
  have hsub : occupied S z X b w ⊆ occupied S' z X b w := by
    rintro k ⟨x, hx, rfl⟩
    exact ⟨x, hSS hx, rfl⟩
  exact ⟨hfin.subset hsub, le_trans (by exact_mod_cast Set.ncard_le_ncard hsub hfin) hcard⟩

section Root

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}

/-- **The root package of a sample.** -/
theorem rootPackage_exists (Q : PreparedAngularPath d k p m H u τ) {ε₀ : ℝ}
    (hpure : Q.uniformPureBounds ε₀) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF}
    {rF frF : ℝ} {Rp : BroadResidual F rF frF} {c : ℕ}
    {K θ ε aA q d₁ h' a' : ℝ}
    (hqaA : q / aA = ((2 : ℝ) ^ p.T i)⁻¹ / Parent.ParentSource.δ (d.N k) (p.r i))
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension'
      Kcap : ℝ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    (core : BroadMultiscaleCoreSource d k p original n depth Kcore e R)
    (hcoreRes : ∀ w, core.current w ⊆ Rp.residual w)
    (data : (a : Fin p.C) → F.active a → OriginalAncestorRecordSource F a
      (core.current (p.γ a) ∩ p.F a) Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius
        fraction χ finest dimension' Kcap)
    (K2 : Fin (d.W k) → Set Ev) (hK2 : ∀ w, MeasurableSet (K2 w) ∧ K2 w ⊆ core.current w)
    (hK2slice : ∀ a (ha : F.active a), K2 (p.γ a) ∩ p.F a = (data a ha).kept)
    -- the velocity bound on the residual
    {Vmax : ℝ} (hV0 : 0 ≤ Vmax) (hvel : ∀ w, ∀ z ∈ Rp.residual w, ‖Parent.v z.1‖ ≤ Vmax)
    -- the census cut of every active ancestor, its MK4 occupancy and the child caps
    {fineMesh Kcensus dimension : ℝ} {censusRate : ℝ≥0∞}
    (hcensusRoot : ∀ a (ha : F.active a), ∃ current : Set Ev, MeasurableSet current ∧
      current ⊆ (data a ha).kept ∧
      ((d.ν k (p.γ a)).prod volume) (data a ha).kept ≤ ((d.ν k (p.γ a)).prod volume) current +
        censusRate * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) ∧
      (∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
        Kcensus ^ (100 : ℕ) * b ≤ 1 * w →
        (Submission.Lib.K4ParentSignalPreparation.Census.occupied current
          (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((Submission.Lib.K4ParentSignalPreparation.Census.occupied current
          (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
          Kcensus / (b ^ 3 * w ^ dimension)) ∧
      ∀ b, p.lev b = i + c → p.par^[c] b = a → ∀ Se : Set Ev, MeasurableSet Se →
        Se ⊆ current ∩ p.F b →
        CapClauses K ε d₁ h' a'
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
          (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
          (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
            O204.Split.δ (d.N k) (p.r (p.lev b))) Se)
    -- the MK4 numerics
    {cellRate durationRate coarse radius ratio : ℝ} (steps : ℕ)
    (hFine : 0 < fineMesh) (hFine1 : fineMesh ≤ 1) (hKcensus : 1 ≤ Kcensus)
    (hsteps : Kcensus ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : fineMesh * (2 : ℝ) ^ steps ≤ 1)
    (hcellRate : 0 < cellRate) (hdurationRate : 0 < durationRate) (hratio0 : 0 ≤ ratio)
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    (hbaseBudget : 3 * baseRef ≤ fineMesh * (2 : ℝ) ^ steps)
    (hhiddenBudget : 3 * hiddenRef ≤ fineMesh * (2 : ℝ) ^ steps)
    (betaR : ENNReal) (hbetaR : betaR ≠ 0) (hbetaRTop : betaR ≠ ⊤)
    (hwidth : (6 * p.κ) * radius ≤ frontRadius)
    (hratio : ENNReal.ofReal ((8 * fraction) / cut) / betaR ≤ ENNReal.ofReal ratio)
    (hr : 0 ≤ p.r i) (hrL : p.r i ≤ d.L)
    {f₀ perror : ℝ} (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀ - dimension * r| ≤ perror)
    (nmesh : ℕ) (hmesh : fineMesh * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse nmesh)
    (hbandResolved : d.N k ^ (-(d.L - p.r i)) ≤ 4 * coarse)
    (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    {Kg baseRho w gfraction εMK : ℝ}
    (hKgJ : 6 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) ≤ Kg) (hKgRate : durationRate⁻¹ ≤ Kg)
    (hKgCount : 8 * (64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
      d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + ε₀)) / cellRate ≤ Kg)
    (hbaseRho : 0 ≤ baseRho) (hcond : 1 ≤ Kg * baseRho ^ 3) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (Vmax + 1) * baseRho ≤ w)
    (hwRadius : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction) (hgfrac : gfraction < 1 - ratio) (hεMK : 0 < εMK)
    (hsmall : Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24) ≤
      min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
        ((gfraction / 4) ^ 4 * εMK ^ 4 /
          (256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 * Kg ^ 9 + 1))))
    (hθ80 : 80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24) ≤ θ) :
    ∃ RP : RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
        cut frontRadius fraction χ finest dimension' Kcap core,
      RP.graphMesh = Submission.Lib.K4DyadicRowScales.mesh nmesh ∧ RP.Brow = 28 * Kg ^ 6 ∧
      (∀ a, F.active a → ∀ x ∈ RP.E1 (p.γ a) ∩ p.F a,
        |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
          ∑ j : Fin 3, RP.row a (ancCode (d.N k) p a RP.graphMesh x) j *
            (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤
        80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24)) ∧
      (∀ a, F.active a → ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
        Kcensus ^ (100 : ℕ) * b ≤ 1 * w →
        (Submission.Lib.K4ParentSignalPreparation.Census.occupied (RP.E1 (p.γ a) ∩ p.F a)
          (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((Submission.Lib.K4ParentSignalPreparation.Census.occupied (RP.E1 (p.γ a) ∩ p.F a)
          (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
          Kcensus / (b ^ 3 * w ^ dimension)) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (K2 w)) ≤
        ENNReal.ofReal (1 - gfraction)⁻¹ *
          (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) +
        (censusRate + (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal εMK +
          (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
            ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
              (7 : ℝ) ^ 4)) + 81 * betaR)) := by
  classical
  have hN0 : 0 < d.N k := by linarith [hd.1 k]
  -- every active ancestor gets its root slice
  have hslice : ∀ a (ha : F.active a), ∃ (G : Set Ev) (row : (Fin 4 → ℤ) → Fin 3 → ℝ),
      MeasurableSet G ∧ G ⊆ (data a ha).kept ∧ (∀ cd j, |row cd j| ≤ 28 * Kg ^ 6) ∧
      (∀ z ∈ G, z ∉ p.oldEndpoints a ∧ z ∉ p.levelEndpoints (i + c)) ∧
      ((d.ν k (p.γ a)).prod volume) (data a ha).kept ≤
        ENNReal.ofReal (1 - gfraction)⁻¹ * ((d.ν k (p.γ a)).prod volume) G +
          (censusRate + (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal εMK +
            (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
              ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
                (7 : ℝ) ^ 4)) + 81 * betaR)) *
          (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) ∧
      (∀ x ∈ G, |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
        ∑ j : Fin 3, row (ancCode (d.N k) p a (Submission.Lib.K4DyadicRowScales.mesh nmesh) x) j *
          (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤
        80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24)) ∧
      (∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
        Kcensus ^ (100 : ℕ) * b ≤ 1 * w →
        (Submission.Lib.K4ParentSignalPreparation.Census.occupied G
          (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((Submission.Lib.K4ParentSignalPreparation.Census.occupied G
          (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
          Kcensus / (b ^ 3 * w ^ dimension)) ∧
      ∀ b, p.lev b = i + c → p.par^[c] b = a → ∀ Se : Set Ev, MeasurableSet Se →
        Se ⊆ G ∩ p.F b →
        CapClauses K ε d₁ h' a'
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
          (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
          (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
            O204.Split.δ (d.N k) (p.r (p.lev b))) Se := by
    intro a ha
    have hla : p.lev a = i := F.level a ha
    obtain ⟨current, hcurM, hcurKept, hcurMass, hcurOcc, hcurCaps⟩ := hcensusRoot a ha
    have hkeptSub : (data a ha).kept ⊆ core.current (p.γ a) ∩ p.F a := (data a ha).kept_subset
    have hcurF : current ⊆ p.F a := fun z hz => (hkeptSub (hcurKept hz)).2
    have hcurRes : current ⊆ Rp.residual (p.γ a) := fun z hz =>
      hcoreRes _ (hkeptSub (hcurKept hz)).1
    have hcurE : current ⊆ d.E k (p.γ a) := fun z hz => hHE _ (Rp.subset_H _ (hcurRes hz))
    have hcurBase : current ⊆ Q.base (p.γ a) := fun z hz => broadResidual_subset_base Rp _ (hcurRes hz)
    have hcurGood : current ⊆ Prod.fst ⁻¹' Parent.SignalGraph.ancestorGood p a Vmax := by
      intro z hz
      refine ⟨((hp.frozenPacket a).counted_inside_original (hcurF hz)).2.1, ?_⟩
      exact hvel _ z (hcurRes hz)
    have hA : d.ν k (p.γ a) (p.A a) ≠ 0 := (hp.assignment_mass_pos hN0 a).ne'
    obtain ⟨G, row, hGm, hGsub, hrowB, hGend, hGmass, hGfit⟩ :=
      root_slice_full Q hpure hd hp hHE hH a ha (data a ha) (fun z hz => hz.2)
        (path_R_degree hp a) hA (path_A_meas hp a) hV0 (i + c) current hcurM hcurKept hcurMass
        hcurF hcurE hcurBase hcurGood steps hFine hFine1 hKcensus hsteps hresolved hcellRate
        hdurationRate hratio0 hcurOcc hbaseRef hhiddenRef hcut hfr hbaseBudget hhiddenBudget
        betaR hbetaR hbetaRTop hwidth hratio (by rw [hla]; exact hr) (by rw [hla]; exact hrL)
        hprofile nmesh hmesh hcoarse (by rw [hla]; exact hbandResolved) hdim0 hdim1 hKgJ
        hKgRate hKgCount hbaseRho hcond hbaseRho4 hwRho hwRadius hgfraction hgfrac hεMK hsmall
    refine ⟨G, row, hGm, hGsub.trans hcurKept, hrowB, hGend, hGmass, ?_,
      occupied_bound_mono hGsub _ _ hcurOcc, ?_⟩
    · intro x hx
      have h := hGfit x hx
      rw [hqaA, ← hla]
      exact h
    · intro b hb hab Se hSe hSeSub
      exact hcurCaps b hb hab Se hSe (fun z hz => ⟨hGsub (hSeSub hz).1, (hSeSub hz).2⟩)
  choose Gf rowf hGm hGsub hrowB hGend hGmass hGfit hGocc hGcaps using hslice
  let G : Fin p.C → Set Ev := fun a => if ha : F.active a then Gf a ha else ∅
  let row : Fin p.C → (Fin 4 → ℤ) → Fin 3 → ℝ := fun a => if ha : F.active a then rowf a ha else 0
  have hGa (a : Fin p.C) (ha : F.active a) : G a = Gf a ha := by simp only [G, ha, ↓reduceDIte]
  have hrowa (a : Fin p.C) (ha : F.active a) : row a = rowf a ha := by
    simp only [row, ha, ↓reduceDIte]
  have hKg0 : 0 ≤ 28 * Kg ^ 6 := by positivity
  obtain ⟨RP, hRPslice, hRPmesh, hRProw, hRPB, hRPmass⟩ := rootPackage_of_slices Q hd hp core
    hcoreRes data K2 hK2 hK2slice G
    (fun a ha => by rw [hGa a ha]; exact hGm a ha)
    (fun a ha => by rw [hGa a ha, hK2slice a ha]; exact hGsub a ha)
    (ENNReal.ofReal (1 - gfraction)⁻¹)
    (censusRate + (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal εMK +
      (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
        ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
          (7 : ℝ) ^ 4)) + 81 * betaR))
    (fun a ha => by rw [hGa a ha, hK2slice a ha]; exact hGmass a ha)
    (fun a ha => by rw [hGa a ha]; exact hGend a ha)
    row (28 * Kg ^ 6) hKg0
    (fun a cd j => by
      by_cases ha : F.active a
      · rw [hrowa a ha]; exact hrowB a ha cd j
      · simp only [row, ha, ↓reduceDIte, Pi.zero_apply, abs_zero]; exact hKg0)
    (Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (fun a ha x hx => by
      rw [hGa a ha] at hx
      rw [hrowa a ha]
      exact (hGfit a ha x hx).trans hθ80)
    (fun b hb hact Se hSe hSeSub => by
      rw [hGa _ hact] at hSeSub
      exact hGcaps (p.par^[c] b) hact b hb rfl Se hSe hSeSub)
  refine ⟨RP, hRPmesh, hRPB, ?_, ?_, hRPmass⟩
  · intro a ha x hx
    rw [hRPslice a ha, hGa a ha] at hx
    rw [hRProw, hrowa a ha, hRPmesh]
    exact hGfit a ha x hx
  · intro a ha
    rw [hRPslice a ha, hGa a ha]
    exact hGocc a ha

end Root

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
