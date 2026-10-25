-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RootRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.PostStateAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRowInputs

/-!
# The rows of one active ancestor at the root (session x1082)

`Forward/AncestorRows.ancestor_velocity_rows` returns the MK4 rows of an ancestor `a` with a
retained set of MODEL events (the frozen packet's time change of the original events) and a
real-valued retention estimate in the model law. This file converts that estimate to the
original law, with a fraction and a charge against the full reference of `a`:

* `retained_original_mass`: `μ(current) ≤ (1 - gf)⁻¹ (μ(current ∩ timeChange⁻¹ retained) + ε ref_a)`;
* `root_rows_of_source`: the MK4 rows of `a` on a source, with the kept set `G` on which the fit
  holds, the bound `28 Kg⁶`, and `μ(source) ≤ (1 - gf)⁻¹ μ(G) + charge · ref_a`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open scoped ENNReal

noncomputable section

/-- **Retention in the original law.** The model retention estimate of a frozen packet, with
denominator the full assignment times the block length, transported to the original law. -/
theorem retained_original_mass (P : Broad.Source.FrozenPacket) (ν : Measure Ln)
    [IsFiniteMeasure ν] (hA : ν P.assigned ≠ 0) {current retained : Set Ev}
    (hcur : MeasurableSet current) (hsub : current ⊆ P.counted)
    (hfin : (ν.prod volume) current ≠ ⊤)
    (hret : MeasurableSet retained) (hretsub : retained ⊆ P.selectedEvent current)
    {ε gf : ℝ} (hε : 0 ≤ ε) (hgf : gf < 1)
    (hmass : ((P.prior ν).prod volume).real (P.selectedEvent current) ≤
      ((P.prior ν).prod volume).real retained + ε +
        gf * ((P.prior ν).prod volume).real (P.selectedEvent current)) :
    (ν.prod volume) current ≤ ENNReal.ofReal (1 - gf)⁻¹ *
      ((ν.prod volume) (current ∩ P.timeChange ⁻¹' retained) +
        ENNReal.ofReal ε * (ENNReal.ofReal P.unitFrame.q * ν P.assigned)) := by
  set B := ENNReal.ofReal P.unitFrame.q * ν P.assigned with hB
  have hB0 : B ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr P.unitFrame_length_pos).ne' hA
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  set G := current ∩ P.timeChange ⁻¹' retained with hG
  have hGmeas : MeasurableSet G := hcur.inter (P.timeChange.measurable hret)
  have hGsub : G ⊆ P.counted := inter_subset_left.trans hsub
  have hselG : P.selectedEvent G = retained := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := hretsub hz
      exact ⟨x, ⟨hx, hz⟩, rfl⟩
  have hmodel (J : Set Ev) (hJ : MeasurableSet J) (hJsub : J ⊆ P.counted) :
      ((P.prior ν).prod volume) (P.selectedEvent J) = B⁻¹ * (ν.prod volume) J := by
    have h := P.selectedLaw_mass_original ν hA hJ hJsub
    simp only [Broad.Source.FrozenPacket.selectedLaw, Measure.restrict_apply_univ] at h
    exact h
  have hGfin : (ν.prod volume) G ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  have hcurModel := hmodel current hcur hsub
  have hretModel : ((P.prior ν).prod volume) retained = B⁻¹ * (ν.prod volume) G := by
    rw [← hselG]; exact hmodel G hGmeas hGsub
  -- real arithmetic
  set x := ((ν.prod volume) current).toReal with hx
  set y := ((ν.prod volume) G).toReal with hy
  set b := B.toReal with hb
  have hbpos : 0 < b := ENNReal.toReal_pos hB0 hBt
  have hreal1 : ((P.prior ν).prod volume).real (P.selectedEvent current) = x / b := by
    rw [measureReal_def, hcurModel, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]
  have hreal2 : ((P.prior ν).prod volume).real retained = y / b := by
    rw [measureReal_def, hretModel, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]
  rw [hreal1, hreal2] at hmass
  have hgf1 : 0 < 1 - gf := by linarith
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
  have hkey : x ≤ (1 - gf)⁻¹ * (y + ε * b) := by
    rw [le_inv_mul_iff₀ hgf1]
    have h1 : x / b * b = x := div_mul_cancel₀ x hbpos.ne'
    have h2 : y / b * b = y := div_mul_cancel₀ y hbpos.ne'
    have hm := mul_le_mul_of_nonneg_right hmass hbpos.le
    nlinarith
  calc (ν.prod volume) current = ENNReal.ofReal x := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal ((1 - gf)⁻¹ * (y + ε * b)) := ENNReal.ofReal_le_ofReal hkey
    _ = ENNReal.ofReal (1 - gf)⁻¹ * ((ν.prod volume) G + ENNReal.ofReal ε * B) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hgf1.le),
          ENNReal.ofReal_add hy0 (mul_nonneg hε hbpos.le), ENNReal.ofReal_toReal hGfin,
          ENNReal.ofReal_mul hε, ENNReal.ofReal_toReal hBt]

section Rows

variable {d : Native.ProblemData} {k m : ℕ} {p : Native.PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

open Parent.SignalGraph Submission.Lib.K4ParentSignalPreparation.Census
  Parent.ParentSource.Broad.Velocity in
/-- **The rows of one ancestor on a source, in the original law.** -/
theorem root_rows_of_source (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (a : Fin p.C) (hR : (p.R a).totalDegree ≤ 2) (hA : d.ν k (p.γ a) (p.A a) ≠ 0)
    (hAmeas : MeasurableSet (p.A a)) {Vmax : ℝ} (hV0 : 0 ≤ Vmax)
    {fineMesh Kcensus dimension cellRate durationRate coarse radius ratio : ℝ} (steps : ℕ)
    (hFine : 0 < fineMesh) (hFine1 : fineMesh ≤ 1) (hKcensus : 1 ≤ Kcensus)
    (hsteps : Kcensus ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : fineMesh * (2 : ℝ) ^ steps ≤ 1)
    (hcellRate : 0 < cellRate) (hdurationRate : 0 < durationRate) (hratio0 : 0 ≤ ratio)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source ⊆ p.F a)
    (hsourceGood : source ⊆ Prod.fst ⁻¹' ancestorGood p a Vmax)
    (hcensus : ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
      Kcensus ^ (100 : ℕ) * b ≤ 1 * w →
      (occupied source (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
      ((occupied source (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
        Kcensus / (b ^ 3 * w ^ dimension))
    {renewCost renewRate : ℝ≥0∞}
    (hrenewCost : renewCost ≤ renewRate *
      (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)))
    (hrenew : ∀ middle : Set Ev, MeasurableSet middle → middle ⊆ source →
      ∃ current : Set Ev, MeasurableSet current ∧ current ⊆ middle ∧
        ((d.ν k (p.γ a)).prod volume) middle ≤
          ((d.ν k (p.γ a)).prod volume) current + renewCost ∧
        ∀ label (n center : P2), ‖n‖ = 1 →
          (((d.ν k (p.γ a)).prod volume).restrict current)
            {z | clockParentCode p a (ancestorSignal (d.N k) p a) (fineMesh * (2 : ℝ) ^ steps) z =
                label ∧
              |Inner.inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity a z - center)| ≤ radius} ≤
            ENNReal.ofReal ratio *
              (((d.ν k (p.γ a)).prod volume).restrict current)
                (clockParentCode p a (ancestorSignal (d.N k) p a) (fineMesh * (2 : ℝ) ^ steps) ⁻¹'
                  {label}))
    (n : ℕ) (hmesh : fineMesh * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse n)
    (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    {Cband : ℝ} (hCband : 0 ≤ Cband)
    (hband : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ a)).prod volume).restrict source)
        {x | unshearedPacketBase p a x ∈ U ∧
          |clockParentSignal p a (ancestorSignal (d.N k) p a) x -
            c (unshearedPacketBase p a x)| ≤ coarse} ≤
      ENNReal.ofReal (Cband * 1 ^ (-dimension) * coarse ^ dimension) *
        (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) * volume U)
    {Kg baseRho w gfraction ε : ℝ}
    (hKgJ : 6 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) ≤ Kg) (hKgRate : durationRate⁻¹ ≤ Kg)
    (hKgCount : 8 * Cband / cellRate ≤ Kg)
    (hbaseRho : 0 ≤ baseRho) (hcond : 1 ≤ Kg * baseRho ^ 3) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (Vmax + 1) * baseRho ≤ w)
    (hwRadius : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction) (hgfrac : gfraction < 1 - ratio) (hε : 0 < ε)
    (hsmall : Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) ≤
      min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
        ((gfraction / 4) ^ 4 * ε ^ 4 / (256 * curvatureRowConstant ^ 3 * Kg ^ 9 + 1)))) :
    ∃ (G : Set Ev) (row : (Fin 4 → ℤ) → Fin 3 → ℝ),
      MeasurableSet G ∧ G ⊆ source ∧ (∀ c j, |row c j| ≤ 28 * Kg ^ 6) ∧
      ((d.ν k (p.γ a)).prod volume) source ≤
        ENNReal.ofReal (1 - gfraction)⁻¹ * ((d.ν k (p.γ a)).prod volume) G +
          (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal ε +
            (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
              ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
                (7 : ℝ) ^ 4)) + renewRate) *
          (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) ∧
      ∀ x ∈ G, |((2 : ℝ) ^ p.T (p.lev a))⁻¹ / Parent.ParentSource.δ (d.N k) (p.r (p.lev a)) *
          Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
        ∑ j : Fin 3, row (clockParentCode p a (ancestorSignal (d.N k) p a)
            (Submission.Lib.K4DyadicRowScales.mesh n) x) j *
          (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤
        80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) := by
  have : IsProbabilityMeasure (d.ν k (p.γ a)) := (hd.weights k).2.2 _
  obtain ⟨current, row, retained, hcurM, hcurSub, hcost, hrowM, hretM, hretSub, hrowB, hmass,
    hfit⟩ := ancestor_velocity_rows hd hp a hR hAmeas hV0 steps hFine hFine1 hKcensus hsteps
      hresolved hcellRate hdurationRate hratio0 source hsource hsourceF hsourceGood hcensus hrenew
      n hmesh hcoarse hdim0 hdim1 hCband hband hKgJ hKgRate hKgCount hbaseRho hcond hbaseRho4
      hwRho hwRadius hgfraction hgfrac hε hsmall
  have hgf1 : gfraction < 1 := by linarith
  have hcurF : current ⊆ p.F a := hcurSub.trans hsourceF
  have hfin : ((d.ν k (p.γ a)).prod volume) current ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun z hz => hp.counted_subset_fullCylinder a
      (hcurF hz)))
    rw [p.fullCylinder_mass (d.ν k (p.γ a)) a]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hret := retained_original_mass (hp.frozenPacket a) (d.ν k (p.γ a)) hA hcurM hcurF hfin
    hretM hretSub hε.le hgf1 hmass
  refine ⟨current ∩ (hp.frozenPacket a).timeChange ⁻¹' retained, row,
    hcurM.inter ((hp.frozenPacket a).timeChange.measurable hretM),
    inter_subset_left.trans hcurSub, hrowB, ?_, ?_⟩
  · set ref := d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹) with href
    have hrefq : ENNReal.ofReal (hp.frozenPacket a).unitFrame.q *
        (d.ν k (p.γ a)) (hp.frozenPacket a).assigned = ref := by
      rw [href, mul_comm]; rfl
    rw [hrefq] at hret
    calc ((d.ν k (p.γ a)).prod volume) source
        ≤ ((d.ν k (p.γ a)).prod volume) current +
            (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
              ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
                (7 : ℝ) ^ 4)) * ref + renewCost := hcost
      _ ≤ ENNReal.ofReal (1 - gfraction)⁻¹ *
            (((d.ν k (p.γ a)).prod volume) (current ∩ (hp.frozenPacket a).timeChange ⁻¹' retained) +
              ENNReal.ofReal ε * ref) +
            (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
              ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
                (7 : ℝ) ^ 4)) * ref + renewRate * ref :=
          add_le_add (add_le_add hret le_rfl) hrenewCost
      _ = _ := by ring
  · intro x hx
    exact hfit x hx.1 hx.2

/-- **Removing the block endpoints is free.** -/
theorem remove_endpoints_mass {W : ℕ} (p : Native.PathData W) (μ : Measure Ln) (a : Fin p.C)
    (level : ℕ) (S : Set Ev) :
    (μ.prod volume) ((S \ p.oldEndpoints a) \ p.levelEndpoints level) = (μ.prod volume) S := by
  rw [p.remove_levelEndpoints_mass, p.remove_oldEndpoints_mass]

/-- **The root slice of one ancestor.** A census cut of the records' slice, then the MK4 rows, then
the endpoint removal: the kept slice carries a `(1 - gf)⁻¹` fraction of the records' slice up to
a full-reference charge, and the fit holds on it. -/
theorem root_slice_of_census (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (a : Fin p.C) (hR : (p.R a).totalDegree ≤ 2) (hA : d.ν k (p.γ a) (p.A a) ≠ 0)
    (hAmeas : MeasurableSet (p.A a)) {Vmax : ℝ} (hV0 : 0 ≤ Vmax) (level : ℕ)
    (slice current : Set Ev) (hcurrent : MeasurableSet current)
    {censusRate : ℝ≥0∞}
    (hcensusMass : ((d.ν k (p.γ a)).prod volume) slice ≤ ((d.ν k (p.γ a)).prod volume) current +
      censusRate * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)))
    {fineMesh Kcensus dimension cellRate durationRate coarse radius ratio : ℝ} (steps : ℕ)
    (hFine : 0 < fineMesh) (hFine1 : fineMesh ≤ 1) (hKcensus : 1 ≤ Kcensus)
    (hsteps : Kcensus ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : fineMesh * (2 : ℝ) ^ steps ≤ 1)
    (hcellRate : 0 < cellRate) (hdurationRate : 0 < durationRate) (hratio0 : 0 ≤ ratio)
    (hcurF : current ⊆ p.F a)
    (hcurGood : current ⊆ Prod.fst ⁻¹' Parent.SignalGraph.ancestorGood p a Vmax)
    (hcensus : ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
      Kcensus ^ (100 : ℕ) * b ≤ 1 * w →
      (Submission.Lib.K4ParentSignalPreparation.Census.occupied current
        (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
      ((Submission.Lib.K4ParentSignalPreparation.Census.occupied current
        (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
        Kcensus / (b ^ 3 * w ^ dimension))
    {renewCost renewRate : ℝ≥0∞}
    (hrenewCost : renewCost ≤ renewRate *
      (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)))
    (hrenew : ∀ middle : Set Ev, MeasurableSet middle → middle ⊆ current →
      ∃ cur : Set Ev, MeasurableSet cur ∧ cur ⊆ middle ∧
        ((d.ν k (p.γ a)).prod volume) middle ≤
          ((d.ν k (p.γ a)).prod volume) cur + renewCost ∧
        ∀ label (n center : P2), ‖n‖ = 1 →
          (((d.ν k (p.γ a)).prod volume).restrict cur)
            {z | clockParentCode p a (Parent.SignalGraph.ancestorSignal (d.N k) p a)
                (fineMesh * (2 : ℝ) ^ steps) z = label ∧
              |Inner.inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity a z - center)| ≤ radius} ≤
            ENNReal.ofReal ratio *
              (((d.ν k (p.γ a)).prod volume).restrict cur)
                (clockParentCode p a (Parent.SignalGraph.ancestorSignal (d.N k) p a)
                  (fineMesh * (2 : ℝ) ^ steps) ⁻¹' {label}))
    (n : ℕ) (hmesh : fineMesh * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse n)
    (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    {Cband : ℝ} (hCband : 0 ≤ Cband)
    (hband : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ a)).prod volume).restrict current)
        {x | unshearedPacketBase p a x ∈ U ∧
          |clockParentSignal p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) x -
            c (unshearedPacketBase p a x)| ≤ coarse} ≤
      ENNReal.ofReal (Cband * 1 ^ (-dimension) * coarse ^ dimension) *
        (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) * volume U)
    {Kg baseRho w gfraction ε : ℝ}
    (hKgJ : 6 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) ≤ Kg) (hKgRate : durationRate⁻¹ ≤ Kg)
    (hKgCount : 8 * Cband / cellRate ≤ Kg)
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
      ((d.ν k (p.γ a)).prod volume) slice ≤
        ENNReal.ofReal (1 - gfraction)⁻¹ * ((d.ν k (p.γ a)).prod volume) G +
          (censusRate + (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal ε +
            (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
              ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
                (7 : ℝ) ^ 4)) + renewRate)) *
          (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) ∧
      ∀ x ∈ G, |((2 : ℝ) ^ p.T (p.lev a))⁻¹ / Parent.ParentSource.δ (d.N k) (p.r (p.lev a)) *
          Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
        ∑ j : Fin 3, row (clockParentCode p a (Parent.SignalGraph.ancestorSignal (d.N k) p a)
            (Submission.Lib.K4DyadicRowScales.mesh n) x) j *
          (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤
        80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) := by
  obtain ⟨G, row, hGm, hGsub, hrowB, hmass, hfit⟩ := root_rows_of_source hd hp a hR hA hAmeas hV0
    steps hFine hFine1 hKcensus hsteps hresolved hcellRate hdurationRate hratio0 current hcurrent
    hcurF hcurGood hcensus hrenewCost hrenew n hmesh hcoarse hdim0 hdim1 hCband hband hKgJ
    hKgRate hKgCount hbaseRho hcond hbaseRho4 hwRho hwRadius hgfraction hgfrac hε hsmall
  refine ⟨(G \ p.oldEndpoints a) \ p.levelEndpoints level, row,
    (hGm.diff (p.oldEndpoints_measurable a)).diff (p.levelEndpoints_measurable level),
    fun z hz => hGsub hz.1.1, hrowB, fun z hz => ⟨hz.1.2, hz.2⟩, ?_,
    fun x hx => hfit x hx.1.1⟩
  rw [remove_endpoints_mass]
  calc ((d.ν k (p.γ a)).prod volume) slice
      ≤ ((d.ν k (p.γ a)).prod volume) current +
          censusRate * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) :=
        hcensusMass
    _ ≤ _ := by
        refine (add_le_add hmass le_rfl).trans (le_of_eq ?_)
        ring

end Rows

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
