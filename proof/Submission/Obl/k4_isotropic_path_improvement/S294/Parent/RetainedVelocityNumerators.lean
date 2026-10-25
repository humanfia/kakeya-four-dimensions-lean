-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.RetainedVelocityNumerators, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/RetainedVelocityNumerators.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityNumerators
import Submission.Lib.K4ReferenceMeshPreparation.ReferenceFloors

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

/-- The original-reference palette pruning is chosen BEFORE all later
geometric queries. One G controls every retained record and every
Borel test under the same fixed physical palette. -/
theorem exists_original_reference_palette_cut
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
      ∀ (r : Σ v, Fin (piecesPerHistory v)) (D : Set (ℤ×ℤ)), MeasurableSet D →
        (μ.restrict G) {z | z∈piece r ∧ velocityPalette a₀ (v z.1)∈D} ≤
          ENNReal.ofReal ((8*R)/delta)*
            (((d.ν k (p.γ b)).prod volume).restrict E) (piece r)*
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
  obtain ⟨G,hG,hloss,hcaps⟩ :=
    Submission.Lib.K4ReferenceMeshPreparation.exists_record_reference_restriction
      νref μ hμ piece hpiece weights (8*R) delta hdelta test mass hnum
  refine ⟨G,hG,?_,?_⟩
  · exact (hloss.trans (mul_le_mul' le_rfl hsum)).trans_eq (by ring)
  · intro r D hD
    exact hcaps r ⟨D,hD⟩

/-- ONE measurable original-law restriction gives fixed-palette cell
caps on a retained geometric source E. Only the pieces of the true
fine histories inside E must localize geometrically.

The accepted original-reference floor construction makes the retained
reference weights legal simultaneously for EVERY Borel palette test.
Each history may have at most J disjoint core pieces. The deletion
cost is delta*J times the full original coarse event; it does not pay
the number of histories, a geometric cell floor, or a conditional prior. -/
theorem exists_retained_cell_palette_cap_of_refined_fine_histories
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (b : Fin p.C) (hb : F.active b)
    {Index Code PureCode : Type*} [Fintype Index]
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
    (hpieceDisj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (μ : Measure Ev) (hμ : μ ≤ ((d.ν k (p.γ b)).prod volume).restrict E)
    (delta : ℝ) (hdelta : 0 < delta)
    (state : Ev → Code) (options : (Σ v, Fin (piecesPerHistory v)) → Finset Code)
    (cell : Ev → PureCode) (paddingCells : Code → Finset PureCode)
    (M : ℕ) (hcard : ∀ q, (paddingCells q).card ≤ M)
    (hcover : ∀ᵐ z ∂μ, ∃ r, z∈piece r)
    (hoptions : ∀ r, ∀ z∈piece r, state z∈options r)
    (hlocal : ∀ r q, q∈options r → ∀ z∈piece r, cell z∈paddingCells q)
    (Bpure : ENNReal)
    (hpure : ∀ c, ((d.ν k (p.γ b)).prod volume)
      (E ∩ {z | cell z=c}) ≤ Bpure) :
    ∃ G : Set Ev, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal delta*(J:ENNReal)*
        ((d.ν k (p.γ b)).prod volume) {z | (p.γ b,z)∈F.U b} ∧
      ∀ q (D : Set (ℤ×ℤ)), MeasurableSet D →
        (μ.restrict G) {z | state z=q ∧ velocityPalette a₀ (v z.1)∈D} ≤
          ENNReal.ofReal ((8*R)/delta)*(M:ENNReal)*Bpure*
            ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D := by
  classical
  let raw := (d.ν k (p.γ b)).prod (volume : Measure ℝ)
  let νref : Measure Ev := raw.restrict E
  let Record := Σ v, Fin (piecesPerHistory v)
  let π := (Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)
  let control : Ev → ℤ×ℤ := fun z => velocityPalette a₀ (v z.1)
  have hdisj : Pairwise (fun r s => AEDisjoint νref (piece r) (piece s)) :=
    fun _ _ hne => (hpieceDisj hne).aedisjoint
  obtain ⟨G,hG,hloss,hcaps⟩ := exists_original_reference_palette_cut F hd hp hHE hst hR
    horiginal hH b hb fine hinj hf hfγ hretained E hE piecesPerHistory J hpieces
    piece hpiece hpieceSub μ hμ delta hdelta
  have hcover' : ∀ᵐ z ∂μ.restrict G, ∃ r, z∈piece r := ae_restrict_of_ae hcover
  have hoptions' : ∀ r, ∀ᵐ z ∂μ.restrict G, z∈piece r → state z∈options r :=
    fun r => Filter.Eventually.of_forall (fun z hz => hoptions r z hz)
  have hlocal' : ∀ r q, q∈options r → piece r ≤ᵐ[νref] {z | cell z∈paddingCells q} :=
    fun r q hq => Filter.Eventually.of_forall (fun z hz => hlocal r q hq z hz)
  have hpure' (c : PureCode) : νref {z | cell z=c} ≤ Bpure := by
    dsimp only [νref]
    rw [Measure.restrict_apply' hE]
    simpa only [inter_comm] using hpure c
  have hnum' (r : Record) (D : Set (ℤ×ℤ)) (hD : MeasurableSet D) :
      (μ.restrict G) {z | z∈piece r ∧ control z∈D} ≤
        ENNReal.ofReal ((8*R)/delta)*νref (piece r)*π D := hcaps r D hD
  refine ⟨G,hG,hloss,?_⟩
  exact Submission.Lib.K4ReferenceMeshPreparation.localized_reference_mesh_palette_cap
      νref (μ.restrict G) π control state piece hpiece hdisj options
      (fun r => νref (piece r)) (fun _ => le_rfl) cell paddingCells M hcard
      hlocal' Bpure hpure' (ENNReal.ofReal ((8*R)/delta)) hcover' hoptions' hnum'

/-- A SINGLE retained set serves an arbitrary family of geometric
queries, including every real scale and every coefficient world.
Their pure grids may depend on the query: only the original record
law and fixed palette must stay the same. -/
theorem exists_simultaneous_retained_cell_palette_caps
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (b : Fin p.C) (hb : F.active b)
    {Index Query Code PureCode : Type*} [Fintype Index]
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
    (hpieceDisj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (μ : Measure Ev) (hμ : μ ≤ ((d.ν k (p.γ b)).prod volume).restrict E)
    (delta : ℝ) (hdelta : 0 < delta)
    (state : Query → Ev → Code)
    (options : Query → (Σ v, Fin (piecesPerHistory v)) → Finset Code)
    (cell : Query → Ev → PureCode) (paddingCells : Query → Code → Finset PureCode)
    (M : Query → ℕ) (hcard : ∀ t q, (paddingCells t q).card ≤ M t)
    (hcover : ∀ᵐ z ∂μ, ∃ r, z∈piece r)
    (hoptions : ∀ t r, ∀ z∈piece r, state t z∈options t r)
    (hlocal : ∀ t r q, q∈options t r → ∀ z∈piece r, cell t z∈paddingCells t q)
    (Bpure : Query → ENNReal)
    (hpure : ∀ t c, ((d.ν k (p.γ b)).prod volume)
      (E ∩ {z | cell t z=c}) ≤ Bpure t) :
    ∃ G : Set Ev, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal delta*(J:ENNReal)*
        ((d.ν k (p.γ b)).prod volume) {z | (p.γ b,z)∈F.U b} ∧
      ∀ t q (D : Set (ℤ×ℤ)), MeasurableSet D →
        (μ.restrict G) {z | state t z=q ∧ velocityPalette a₀ (v z.1)∈D} ≤
          ENNReal.ofReal ((8*R)/delta)*(M t:ENNReal)*Bpure t*
            ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D := by
  classical
  let raw := (d.ν k (p.γ b)).prod (volume : Measure ℝ)
  let νref : Measure Ev := raw.restrict E
  let Record := Σ v, Fin (piecesPerHistory v)
  let π := (Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)
  let control : Ev → ℤ×ℤ := fun z => velocityPalette a₀ (v z.1)
  have hdisj : Pairwise (fun r s => AEDisjoint νref (piece r) (piece s)) :=
    fun _ _ hne => (hpieceDisj hne).aedisjoint
  obtain ⟨G,hG,hloss,hcaps⟩ := exists_original_reference_palette_cut F hd hp hHE hst hR
    horiginal hH b hb fine hinj hf hfγ hretained E hE piecesPerHistory J hpieces
    piece hpiece hpieceSub μ hμ delta hdelta
  have hcover' : ∀ᵐ z ∂μ.restrict G, ∃ r, z∈piece r := ae_restrict_of_ae hcover
  have hoptions' (t : Query) : ∀ r, ∀ᵐ z ∂μ.restrict G, z∈piece r → state t z∈options t r :=
    fun r => Filter.Eventually.of_forall (fun z hz => hoptions t r z hz)
  have hlocal' (t : Query) : ∀ r q, q∈options t r →
      piece r ≤ᵐ[νref] {z | cell t z∈paddingCells t q} :=
    fun r q hq => Filter.Eventually.of_forall (fun z hz => hlocal t r q hq z hz)
  have hpure' (t : Query) (c : PureCode) : νref {z | cell t z=c} ≤ Bpure t := by
    dsimp only [νref]
    rw [Measure.restrict_apply' hE]
    simpa only [inter_comm] using hpure t c
  have hnum' (r : Record) (D : Set (ℤ×ℤ)) (hD : MeasurableSet D) :
      (μ.restrict G) {z | z∈piece r ∧ control z∈D} ≤
        ENNReal.ofReal ((8*R)/delta)*νref (piece r)*π D := hcaps r D hD
  refine ⟨G,hG,hloss,?_⟩
  intro t
  exact Submission.Lib.K4ReferenceMeshPreparation.localized_reference_mesh_palette_cap
    νref (μ.restrict G) π control (state t) piece hpiece hdisj (options t)
    (fun r => νref (piece r)) (fun _ => le_rfl) (cell t) (paddingCells t) (M t) (hcard t)
    (hlocal' t) (Bpure t) (hpure' t) (ENNReal.ofReal ((8*R)/delta)) hcover' (hoptions' t) hnum'

end Prepared

/-- Turn actual finite core covers of disjoint fine histories into a
measurable disjoint record family. Every piece retains its original
history and core, so all pointwise geometric bounds pass to it. The
number of possible records PER HISTORY is unchanged. -/
theorem exists_disjoint_core_records
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index]
    (E : Set Ω) (Hist : Index → Set Ω)
    (hHist : Pairwise (fun v w => Disjoint (Hist v) (Hist w)))
    (n : Index → ℕ) (core : (v : Index) → Fin (n v) → Set Ω)
    (hcore : ∀ v i, MeasurableSet (core v i))
    (hsub : ∀ v i, core v i ⊆ E∩Hist v)
    (hcover : ∀ z∈E, ∃ v i, z∈core v i) :
    ∃ piece : (Σ v, Fin (n v)) → Set Ω,
      (∀ r, MeasurableSet (piece r)) ∧
      (∀ r, piece r ⊆ core r.1 r.2) ∧
      Pairwise (fun r s => Disjoint (piece r) (piece s)) ∧
      ∀ z∈E, ∃ r, z∈piece r := by
  classical
  let piece : (Σ v, Fin (n v)) → Set Ω := fun r => disjointed (core r.1) r.2
  have hpiece (r : Σ v, Fin (n v)) : MeasurableSet (piece r) := by
    dsimp only [piece]
    rw [disjointed_eq_inter_compl]
    exact (hcore r.1 r.2).inter (MeasurableSet.iInter (fun i =>
      MeasurableSet.iInter (fun _ => (hcore r.1 i).compl)))
  have hpieceSub (r : Σ v, Fin (n v)) : piece r ⊆ core r.1 r.2 :=
    disjointed_subset _ _
  refine ⟨piece,hpiece,hpieceSub,?_,?_⟩
  · rintro ⟨v,i⟩ ⟨w,j⟩ hne
    by_cases hvw : v=w
    · subst w
      have hij : i≠j := fun h => hne (by subst j; rfl)
      exact disjoint_disjointed (core v) hij
    · exact (hHist hvw).mono
        (fun z hz => (hsub v i (hpieceSub ⟨v,i⟩ hz)).2)
        (fun z hz => (hsub w j (hpieceSub ⟨w,j⟩ hz)).2)
  · intro z hz
    obtain ⟨v,i,hi⟩ := hcover z hz
    have hu : z∈⋃ i, disjointed (core v) i := by
      rw [iUnion_disjointed]
      exact mem_iUnion.mpr ⟨i,hi⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hu
    exact ⟨⟨v,j⟩,hj⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
