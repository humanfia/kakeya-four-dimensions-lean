-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.RetainedVelocityCurrentCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Strengthens this obligation's RetainedVelocityNumerators original-history
-- construction by retaining BOTH conclusions of the same current floor cut.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.RetainedVelocityNumerators
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.CurrentReferenceCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette

open Set MeasureTheory
open ParentSource ParentSource.Native
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A a₀ R : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (hst : i ≤ stop) (hR : 0 ≤ R)
    (horiginal : ∀ b, F.active b → F.U b ⊆
      likelihoodGood Q.law (labelledSupport Q.residual)
        (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R)

include hd hp hHE hst hR horiginal

/-- The actual original histories yield one retained set with both
original-reference numerators and conditional current-record palette
ratios, simultaneously for all Borel original-velocity events. -/
theorem exists_original_reference_palette_cut_and_current
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (b : Fin p.C) (hb : F.active b)
    {Index : Type*} [Fintype Index]
    (fine : Index → Fin p.C) (hinj : Function.Injective fine)
    (hf : ∀ v, p.lev (fine v)=stop) (hfγ : ∀ v, p.γ (fine v)=p.γ b)
    (hretained : ∀ v, F.coding.code (fine v)∉
      fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1/8 : ℝ)))
    (E : Set Ev) (hE : MeasurableSet E)
    (piecesPerHistory : Index → ℕ) (J : ℕ)
    (hpieces : ∀ v, piecesPerHistory v ≤ J)
    (piece : (Σ v, Fin (piecesPerHistory v)) → Set Ev)
    (hpiece : ∀ r, MeasurableSet (piece r))
    (hpieceSub : ∀ r, piece r ⊆ E∩F.fineOriginalEvent b (fine r.1) univ)
    (μ : Measure Ev) (hμ : μ ≤ ((d.ν k (p.γ b)).prod volume).restrict E)
    (delta : ℝ) (hdelta : 0 < delta)
    : ∃ G : Set Ev, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal delta*(J:ENNReal)*
        ((d.ν k (p.γ b)).prod volume) {z | (p.γ b,z)∈F.U b} ∧
      (∀ r : Σ v, Fin (piecesPerHistory v), (μ.restrict G) (piece r)=0 ∨
        ENNReal.ofReal delta*((d.ν k (p.γ b)).prod volume)
          (F.fineOriginalEvent b (fine r.1) univ) ≤ (μ.restrict G) (piece r)) ∧
      ∀ (r : Σ v, Fin (piecesPerHistory v)) (D : Set (ℤ×ℤ)), MeasurableSet D →
        (μ.restrict G) {z | z∈piece r ∧ velocityPalette a₀ (v z.1)∈D} ≤
          ENNReal.ofReal ((8*R)/delta)*
            (((d.ν k (p.γ b)).prod volume).restrict E) (piece r)*
            ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D ∧
        (μ.restrict G) {z | z∈piece r ∧ velocityPalette a₀ (v z.1)∈D} ≤
          ENNReal.ofReal ((8*R)/delta)*(μ.restrict G) (piece r)*
            ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D := by
  classical
  let raw := (d.ν k (p.γ b)).prod (volume : Measure ℝ)
  let U : Set Ev := {z | (p.γ b,z)∈F.U b}
  let νref : Measure Ev := raw.restrict E
  let Old : Index → Set Ev := fun v => F.fineOriginalEvent b (fine v) univ
  let Record := Σ v, Fin (piecesPerHistory v)
  let weights : Record → ENNReal := fun r => raw (Old r.1)
  let π := (Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)
  let control : Ev → ℤ×ℤ := fun z => velocityPalette a₀ (v z.1)
  have hOld : ∀ v, MeasurableSet (Old v) :=
    fun v => F.fine_original_event_measurable hp b (fine v) hb univ MeasurableSet.univ
  have hOldSub : ∀ v, Old v ⊆ U := fun _ z hz => hz.2.1
  have hpacket (v : Index) {z : Ev} (hz : z∈Old v) :
      z∈p.F (fine v) ∧ packetUnique p.lev p.γ p.F (p.γ b) z := by
    have hh : (z∈p.F (fine v) ∧ packetUnique p.lev p.γ p.F (p.γ b) z) ∧
        z∈p.terminalCoverage m (p.γ b) := by
      simpa only [PathData.packetWitness,ite_eq_left (And.intro (hf v) (hfγ v)),
        mem_inter_iff,mem_ofPred_eq] using hz.1
    exact hh.1
  have hdisjOld : Pairwise (fun v w => Disjoint (Old v) (Old w)) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    intro z hzv hzw
    have hv := hpacket v hzv
    have hw := hpacket w hzw
    exact hvw (hinj (hv.2 (fine v) (fine w) ((hf v).trans (hf w).symm)
      (hfγ v) (hfγ w) hv.1 hw.1))
  have hsumOld : (∑ v, raw (Old v)) ≤ raw U := by
    calc
      _ = raw (⋃ v, Old v) := by
        simpa only [tsum_fintype] using (measure_iUnion hdisjOld hOld).symm
      _ ≤ raw U := measure_mono (iUnion_subset hOldSub)
  have hsum : (∑ r, weights r) ≤ (J:ENNReal)*raw U := by
    calc
      _ = ∑ v, (piecesPerHistory v:ENNReal)*raw (Old v) := by
        rw [Fintype.sum_sigma]
        simp [weights]
      _ ≤ ∑ v, (J:ENNReal)*raw (Old v) := by
        apply Finset.sum_le_sum
        intro v _
        exact mul_le_mul' (by exact_mod_cast hpieces v) le_rfl
      _ = (J:ENNReal)*(∑ v, raw (Old v)) := by rw [Finset.mul_sum]
      _ ≤ (J:ENNReal)*raw U := mul_le_mul' le_rfl hsumOld
  let Tests := {D : Set (ℤ×ℤ) // MeasurableSet D}
  let test : Tests → Set Ev := fun D => control ⁻¹' D.1
  let mass : Tests → ENNReal := fun D => π D.1
  have hnum (r : Record) (D : Tests) :
      μ (piece r∩test D) ≤ ENNReal.ofReal (8*R)*weights r*mass D := by
    have hh := fine_original_physical_palette_cap_with_current_mass F hd hp hHE hst hR
      horiginal hH b (fine r.1) hb (hf r.1) (hfγ r.1) (hretained r.1) D.1 D.2
    apply ((hμ.trans Measure.restrict_le_self) _).trans
    apply (measure_mono _).trans hh
    intro z hz
    exact ⟨(hpieceSub r hz.1).2,hz.2⟩
  obtain ⟨G,hG,hloss,hfloor,hcaps,hcurrent⟩ :=
    exists_record_reference_and_current_restriction
      νref μ hμ piece hpiece weights (8*R) delta hdelta test mass hnum
  refine ⟨G,hG,?_,hfloor,?_⟩
  · exact (hloss.trans (mul_le_mul' le_rfl hsum)).trans_eq (by ring)
  · intro r D hD
    exact ⟨hcaps r ⟨D,hD⟩,hcurrent r ⟨D,hD⟩⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
