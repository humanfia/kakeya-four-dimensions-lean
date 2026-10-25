-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.ChildStage, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.AncestorRecordStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.PointwiseChildQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRowLists

/-!
# The child stage of the relative source (session x1082)

At a dense child `b` of an active ancestor `a`, the root stage leaves a measurable set
`Sb ⊆ E(γ b) ∩ F_b` of root survivors. This file turns the root's per-ancestor products into the
literal CHILD conclusion of `Source.StagesProducer`:

* the states, palette and graph readout of x1095's `OriginalAncestorRecordSource.relative_states`
  (the readout is fed the ancestor rows scaled by `aA/q`), giving `StateClauses` on the kept set
  `Se ⊆ Sb` at a loss `6561 β ref_b`;
* `RowClauses` from the readout identity: the bound from the row bound, the graph clause from the
  root's pointwise fit of `rate R_a` (in clock units), the lists from the root's base-only row
  lists on `Er = Eref ∩ F_b` (`Forward/AncestorRowLists`);
* `QualClauses` with empty exception from x1096's `pointwise_child_qual_clauses` on the same `Er`;
* `CapClauses` restricted from `Sb` to `Se`;
* the final mass `ref_b/K` from the root mass of `Sb` minus the state loss.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily)
open Parent.Qualification.Jets2
open scoped ENNReal

noncomputable section

/-- ENNReal bookkeeping of the final mass: a kept set losing at most `c` from a set of mass at
least `x + c` has mass at least `x`. -/
theorem mass_of_loss {x c μS μK : ENNReal} (hc : c ≠ ⊤) (hS : x + c ≤ μS) (hloss : μS ≤ μK + c) :
    x ≤ μK := by
  have h := hS.trans hloss
  exact (ENNReal.add_le_add_iff_right hc).mp h

section Child

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal}
    {F : PaletteFamily Q i stop meshF envF θF}

/-- **The child stage.** The root's per-ancestor products at a dense child give the literal
child clauses of `StagesProducer`. -/
theorem child_stage_clauses (hd : d.Valid) {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (a b : Fin p.C) (hactive : F.active a) (hworld : p.γ b = p.γ a) (hchild : p.lev b ≤ stop)
    (hlevel : p.lev a ≤ p.lev b) (hlast : p.lev b ≤ m - 1)
    -- the per-sample scalars
    {K θ ε pv aA q d₁ h' a' : ℝ}
    (haA : aA = δ (d.N k) (p.r (p.lev a))) (hq : q = ((2 : ℝ) ^ p.T (p.lev a))⁻¹)
    (hK : 0 < K) (heps : 0 < ε)
    -- the root survivors of the child
    (E : Fin (d.W k) → Set Ev) (Sb : Set Ev) (hSbMeas : MeasurableSet Sb)
    (hSbE : Sb ⊆ E (p.γ b) ∩ p.F b)
    -- the ancestor's record source and the state stage
    {Edata : Set Ev} {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ
      finest dimension Kcap : ℝ}
    (data : OriginalAncestorRecordSource F a Edata Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap)
    (hEbase : Edata ⊆ Q.base (p.γ a)) (hSbkept : Sb ⊆ data.kept)
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    {graphMesh : ℝ} (hgraph : 0 < graphMesh) (hfinePv : 0 < finePv) (hpv : finePv ≤ pv)
    (hgraphBase : 3 * baseRef ≤ graphMesh) (hgraphHidden : 3 * hiddenRef ≤ graphMesh)
    (hphysicalBase : 3 * ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev a)) * baseRef ≤ ε)
    (hphysicalHidden : 3 * (δ (d.N k) (p.r (p.lev a)) / δ (d.N k) (p.r (p.lev b))) * hiddenRef ≤
      (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev b))) * ε)
    (beta : ENNReal) (hbeta : beta ≠ 0) (hbetaTop : beta ≠ ⊤)
    (hstripWidth : (K / 4) ^ (-100 : ℝ) * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q a j l|) ≤
      frontRadius * ((2 : ℝ) ^ p.T (p.lev a) * |(p.Q a).det|))
    (hstripRatio : ENNReal.ofReal ((8 * fraction) / cut) / beta ≤ (1 / 2000000000000 : ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8 * paletteRatio) / cut) / beta ≤ ENNReal.ofReal (K / 4))
    -- the ancestor's rows on its clock code, their bound and their fit on the survivors
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) {Brow : ℝ} (hBrow : 0 ≤ Brow)
    (hrow : ∀ c j, |row c j| ≤ Brow) (hBK : Brow ≤ K)
    (hfit : ∀ x ∈ Sb, |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
      ∑ j : Fin 3, row (clockParentCode p a (Parent.SignalGraph.ancestorSignal (d.N k) p a)
        graphMesh x) j * (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤ θ)
    -- the row reference, its base-only lists and the native qualification
    (Eref : Set Ev) (hErefF : Eref ⊆ p.F a)
    (hterminal : ∀ z ∈ Eref, ∃ terminal : Fin p.C,
      p.lev terminal = m - 1 ∧ p.γ terminal = p.γ a ∧ z ∈ p.F terminal)
    (hErefMeas : MeasurableSet Eref)
    (hSbRef : Sb ⊆ p.childReference a (p.lev b) Eref)
    (hlist : ∀ c' : Fin 3 → ℝ, ∃ Fc : Finset (Fin 3 → ℤ), (Fc.card : ℝ) ≤ K ∧
      ∀ x ∈ Eref ∩ p.F b, (∀ j : Fin 3, |unshearedPacketBase p b x j - c' j| ≤ θ) →
        (fun j : Fin 3 => ⌊(aA / q) * row (clockParentCode p a
          (Parent.SignalGraph.ancestorSignal (d.N k) p a) graphMesh x) j / ((aA / q) * θ)⌋) ∈ Fc)
    (M Tq : ℕ) (qmesh qerror qduration : ℝ) (qbound : ℤ)
    (hqmesh : 0 ≤ qmesh) (hqbound : 0 ≤ qbound)
    (hcoeff : Parent.QualificationClock.coefficientCost M * (qmesh * qbound) ≤ K)
    (herror : qerror ≤ θ)
    (hduration : 1 / K ≤ qduration / ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) /
      (((2 : ℝ) ^ p.T (p.lev a))⁻¹)))
    (hqualified : ∀ z ∈ (hp.frozenPacket a).selectedEvent Sb,
      NativeGridQualified (p.childClockReference a (p.lev b) Eref)
        (p.childClockLabel a (p.lev b) (p.γ a))
        (row ∘ (clockParentCode p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) graphMesh ∘
          p.childClockPoint a)) M Tq qmesh qbound qerror qduration z)
    -- the caps on the survivors
    (hcap : CapClauses K ε d₁ h' a'
      (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
      (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
      (fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b))) Sb)
    -- the mass of the survivors
    (hmass : (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) /
        ENNReal.ofReal K + (6561 : ENNReal) * beta *
          (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) ≤
        ((d.ν k (p.γ b)).prod volume) Sb) :
    ∃ (Se Er bad : Set Ev) (st : Ev → ℕ) (G : ℕ → Fin 3 → ℝ) (pal : Measure (Fin 2 → ℤ)),
      Se ⊆ E (p.γ b) ∩ p.F b ∧ Se ⊆ Er ∧
      (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) / ENNReal.ofReal K ≤
        (((d.ν k (p.γ b)).prod volume).restrict Se) Set.univ ∧
      CapClauses K ε d₁ h' a'
        (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
        (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
        (fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b))) Se ∧
      StateClauses K ε pv (d.ν k (p.γ b))
        (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
        (fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b)))
        Se st pal ∧
      RowClauses K θ aA q (p.R a)
        (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b)) Se Er st G ∧
      QualClauses M K θ aA q (p.j b) ((2 : ℝ) ^ p.T (p.lev b))⁻¹ (d.ν k (p.γ b)) Se Er bad st G := by
  classical
  have haA0 : 0 < aA := by rw [haA]; unfold δ; positivity
  have hq0 : 0 < q := by rw [hq]; positivity
  have hscale0 : 0 ≤ aA / q := (div_pos haA0 hq0).le
  let code := clockParentCode p a (Parent.SignalGraph.ancestorSignal (d.N k) p a) graphMesh
  let row' : (Fin 4 → ℤ) → Fin 3 → ℝ := fun c => (aA / q) • row c
  have hrow' : ∀ c j, |row' c j| ≤ (aA / q) * Brow := by
    intro c j
    simp only [row', Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hscale0]
    exact mul_le_mul_of_nonneg_left (hrow c j) hscale0
  have hδb : 0 < δ (d.N k) (p.r (p.lev b)) := by unfold δ; positivity
  -- the state stage
  obtain ⟨keep, state, value, palette, hkeepSub, hloss, hstates, hvalue, hvalueBound⟩ :=
    Source.OriginalAncestorRecordSource.relative_states data hd hp hHE hH hactive hEbase b hworld hchild hbaseRef hhiddenRef hcut hfr
      hgraph heps hδb hfinePv hpv hK hgraphBase hgraphHidden hphysicalBase hphysicalHidden
      Sb hSbMeas (fun z hz => ⟨hSbkept hz, (hSbE hz).2⟩) beta hbeta hbetaTop row'
      (mul_nonneg hscale0 hBrow) hrow' hstripWidth hstripRatio hpaletteRatio
  have hread : ∀ z, value (state z) = (aA / q) • row (code z) := fun z => hvalue z
  refine ⟨keep, Eref ∩ p.F b, ∅, state, value, palette,
    fun z hz => hSbE (hkeepSub hz),
    fun z hz => ⟨(hSbRef (hkeepSub hz)).1.1, (hSbE (hkeepSub hz)).2⟩, ?_, hcap.mono hkeepSub,
    ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- the final mass
    rw [Measure.restrict_apply_univ]
    have hfin : (6561 : ENNReal) * beta *
        (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) ≠ ⊤ := by
      have : IsProbabilityMeasure (d.ν k (p.γ b)) := (hd.weights k).2.2 _
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hbetaTop)
        (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)
    have hloss' : ((d.ν k (p.γ b)).prod volume) Sb ≤ ((d.ν k (p.γ b)).prod volume) keep +
        (6561 : ENNReal) * beta *
          (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) := by
      simpa only [hworld] using hloss
    exact mass_of_loss hfin hmass hloss'
  · -- the states
    rw [hworld]
    exact hstates
  · -- bounded rows
    intro c j
    by_cases hc : ∃ z, state z = c
    · obtain ⟨z, rfl⟩ := hc
      exact (hvalueBound _ j).trans (by rw [mul_comm K]; exact mul_le_mul_of_nonneg_left hBK hscale0)
    · exact (hvalueBound c j).trans (by rw [mul_comm K]; exact mul_le_mul_of_nonneg_left hBK hscale0)
  · -- the graph clause
    intro z hz
    have hf := hfit z (hkeepSub hz)
    rw [hread z]
    have hsum : ∑ j : Fin 3, (![1, z.1.2 3, z.1.2 4] : Fin 3 → ℝ) j * ((aA / q) • row (code z)) j =
        (aA / q) * ∑ j : Fin 3, row (code z) j * (![1, z.1.2 3, z.1.2 4] : Fin 3 → ℝ) j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hrate : Submission.Lib.K4GlobalParentSignal.rate (p.R a) z.1 z.2 =
        (aA / q) * (q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) z.1 z.2) := by
      field_simp
    rw [hsum, hrate, ← mul_sub, abs_mul, abs_of_nonneg hscale0]
    exact mul_le_mul_of_nonneg_left hf hscale0
  · -- the row lists
    intro c'
    obtain ⟨Fc, hFc, hmem⟩ := hlist c'
    refine ⟨Fc, hFc, fun x hx hbox => ?_⟩
    have h := hmem x hx hbox
    rw [hread x]
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  · -- qualification with empty exception
    have hG : Measurable (row ∘ code) := by
      have hc : Measurable code := measurable_clockParentCode p a _ graphMesh
      exact (measurable_of_countable row).comp hc
    exact pointwise_child_qual_clauses hp a (p.lev b) hlevel hlast Eref hErefF hterminal hErefMeas
      keep (fun z hz => hSbRef (hkeepSub hz)) code row hG b rfl hworld
      (fun z hz => (hSbE (hkeepSub hz)).2) state value M Tq qmesh qerror qduration aA q K θ qbound
      (fun z _ => by rw [hread z]; rfl) hqmesh hqbound hscale0 hcoeff herror hduration
      (fun z hz => hqualified z (image_mono hkeepSub hz)) (d.ν k (p.γ b))

end Child

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
