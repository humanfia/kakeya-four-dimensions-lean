-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.RetainedHistoryQueries, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.RetainedVelocityCurrentCaps

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

/-- One original-reference pruning precedes every later region that is
a union of complete fine-history records. The region, its cell grids
and its pure caps may be chosen afterwards. -/
theorem exists_simultaneous_subhistory_cell_palette_caps
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (b : Fin p.C) (hb : F.active b)
    {Index Query Code PureCode : Type*} [Fintype Index]
    (fine : Index → Fin p.C) (hinj : Function.Injective fine)
    (hf : ∀ v, p.lev (fine v)=stop) (hfγ : ∀ v, p.γ (fine v)=p.γ b)
    (hretained : ∀ v, F.coding.code (fine v)∉
      fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1/8 : ℝ)))
    (E : Set Ev) (hE : MeasurableSet E)
    (n : Index → ℕ) (J : ℕ) (hn : ∀ v, n v ≤ J)
    (piece : (Σ v, Fin (n v)) → Set Ev)
    (hm : ∀ r, MeasurableSet (piece r))
    (hs : ∀ r, piece r ⊆ E∩F.fineOriginalEvent b (fine r.1) univ)
    (hdj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (μ : Measure Ev) (hμ : μ ≤ ((d.ν k (p.γ b)).prod volume).restrict E)
    (cut : ℝ) (hcut : 0 < cut)
    (region : Query → Set Ev) (hregion : ∀ t, MeasurableSet (region t))
    (hwhole : ∀ t r, (piece r∩region t).Nonempty → piece r⊆region t)
    (state : Query → Ev → Code)
    (options : Query → (Σ v, Fin (n v)) → Finset Code)
    (cell : Query → Ev → PureCode) (padding : Query → Code → Finset PureCode)
    (M : Query → ℕ) (hcard : ∀ t q, (padding t q).card ≤ M t)
    (hcover : ∀ᵐ z ∂μ, ∃ r, z∈piece r)
    (hoptions : ∀ t r, ∀ z∈piece r∩region t, state t z∈options t r)
    (hlocal : ∀ t r q, q∈options t r → ∀ z∈piece r∩region t, cell t z∈padding t q)
    (pure : Query → ENNReal)
    (hpure : ∀ t c, ((d.ν k (p.γ b)).prod volume)
      ((E∩region t)∩{z | cell t z=c}) ≤ pure t) :
    ∃ G : Set Ev, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal cut*(J:ENNReal)*
        ((d.ν k (p.γ b)).prod volume) {z | (p.γ b,z)∈F.U b} ∧
      (∀ r : Σ v, Fin (n v), (μ.restrict G) (piece r)=0 ∨
        ENNReal.ofReal cut*((d.ν k (p.γ b)).prod volume)
          (F.fineOriginalEvent b (fine r.1) univ) ≤ (μ.restrict G) (piece r)) ∧
      (∀ (r : Σ v, Fin (n v)) (D : Set (ℤ×ℤ)), MeasurableSet D →
        (μ.restrict G) {z | z∈piece r ∧ velocityPalette a₀ (v z.1)∈D} ≤
          ENNReal.ofReal ((8*R)/cut)*(μ.restrict G) (piece r)*
            ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D) ∧
      ∀ t q (D : Set (ℤ×ℤ)), MeasurableSet D →
        ((μ.restrict G).restrict (region t))
          {z | state t z=q ∧ velocityPalette a₀ (v z.1)∈D} ≤
          ENNReal.ofReal ((8*R)/cut)*(M t:ENNReal)*pure t*
            ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D := by
  classical
  let raw := (d.ν k (p.γ b)).prod (volume : Measure ℝ)
  obtain ⟨G,hG,hloss,hfloor,hcaps⟩ := exists_original_reference_palette_cut_and_current F hd hp hHE hst hR
    horiginal hH b hb fine hinj hf hfγ hretained E hE n J hn piece hm hs μ hμ cut hcut
  refine ⟨G,hG,hloss,hfloor,(fun r D hD => (hcaps r D hD).2),?_⟩
  intro t
  let νref := raw.restrict (E∩region t)
  let μquery := (μ.restrict G).restrict (region t)
  let pieces := fun r => piece r∩region t
  let π := (Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)
  let control : Ev → ℤ×ℤ := fun z => velocityPalette a₀ (v z.1)
  have hpieces : ∀ r, MeasurableSet (pieces r) := fun r => (hm r).inter (hregion t)
  have hdisj : Pairwise (fun r s => AEDisjoint νref (pieces r) (pieces s)) := by
    intro r s hrs
    exact ((hdj hrs).mono inter_subset_left inter_subset_left).aedisjoint
  have hcoverage : ∀ᵐ z ∂μquery, ∃ r, z∈pieces r := by
    have hc : ∀ᵐ z ∂μquery, ∃ r, z∈piece r := ae_restrict_of_ae (ae_restrict_of_ae hcover)
    have hr : ∀ᵐ z ∂μquery, z∈region t := ae_restrict_mem (hregion t)
    filter_upwards [hc,hr] with z hz hzr
    obtain ⟨r,hr⟩ := hz
    exact ⟨r,hr,hzr⟩
  have hopt : ∀ r, ∀ᵐ z ∂μquery, z∈pieces r → state t z∈options t r :=
    fun r => Filter.Eventually.of_forall (fun z hz => hoptions t r z hz)
  have hloc : ∀ r q, q∈options t r → pieces r ≤ᵐ[νref] {z | cell t z∈padding t q} :=
    fun r q hq => Filter.Eventually.of_forall (fun z hz => hlocal t r q hq z hz)
  have hpc (c : PureCode) : νref {z | cell t z=c} ≤ pure t := by
    dsimp only [νref]
    rw [Measure.restrict_apply' (hE.inter (hregion t))]
    simpa only [inter_comm] using hpure t c
  have hnum (r : Σ v, Fin (n v)) (D : Set (ℤ×ℤ)) (hD : MeasurableSet D) :
      μquery {z | z∈pieces r ∧ control z∈D} ≤
        ENNReal.ofReal ((8*R)/cut)*νref (pieces r)*π D := by
    by_cases hr : (pieces r).Nonempty
    · have hsub : piece r⊆region t := hwhole t r hr
      have hpieceEq : pieces r=piece r := inter_eq_left.mpr hsub
      have hmass : νref (pieces r)=raw.restrict E (piece r) := by
        dsimp only [νref]
        rw [hpieceEq,Measure.restrict_apply' (hE.inter (hregion t)),Measure.restrict_apply' hE]
        congr 1
        exact Set.Subset.antisymm
          (fun z hz => ⟨hz.1,hz.2.1⟩)
          (fun z hz => ⟨hz.1,hz.2,hsub hz.1⟩)
      rw [hmass]
      apply le_trans ?_ (hcaps r D hD).1
      apply (show μquery {z | z∈pieces r ∧ control z∈D} ≤
          (μ.restrict G) {z | z∈pieces r ∧ control z∈D} from Measure.restrict_le_self _).trans
      apply measure_mono
      intro z hz
      exact ⟨hz.1.1,hz.2⟩
    · have hempty : pieces r=∅ := Set.not_nonempty_iff_eq_empty.mp hr
      simp only [hempty,mem_empty_iff_false,false_and,setOf_false,measure_empty,zero_le]
  exact Submission.Lib.K4ReferenceMeshPreparation.localized_reference_mesh_palette_cap
    νref μquery π control (state t) pieces hpieces hdisj (options t)
    (fun r => νref (pieces r)) (fun _ => le_rfl) (cell t) (padding t) (M t) (hcard t)
    hloc (pure t) hpc (ENNReal.ofReal ((8*R)/cut)) hcoverage hopt hnum

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
