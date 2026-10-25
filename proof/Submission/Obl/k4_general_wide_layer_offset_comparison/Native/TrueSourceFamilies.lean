-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/TrueSourceFamilies.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SourceSheetFamilies
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.FiniteOriginalAssignments
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.AllParentSheets

/-!
# Original true sheet families on one literal common domain

A true label is a parent of accepted o253's prepared model together with a native branch:
`Fin (a.n k s) × Bool`, numbered by `trueLabel n : Fin n × Bool ≃ Fin (n * 2)`.

`trueSourceFamily` builds the `OriginalSheetFamily` (x0934's `SourceSheetFamilies`) of one
literal domain `D₀` from

* a measurable core `G` carrying the current law, on which every incidence has code `D₀`, and
* a measurable label map `label` (the true priority parent and its native branch) such that
  every point of `G` is native-good for its own label (`TrueNativeGood`: packet geometry,
  `SheetOn` of the native sheet at its zoomed base, native fit).

Its witnesses are `G ∩ label⁻¹ {l}`, its index is `trueLabel (label z)`, and the candidate of a
label `(i, σ)` is the native sheet `g i σ` read in the common frame of `D₀` (`trueCandidate`),
for every nonempty witness. `IsSheet 4` and the Lipschitz bound come from
`parent_common_sheet` at an actual witness point; the fit at every witness point is that
point's own native fit, through the exact pullback `affC_common_coords` and
`parentZoomPoint_base`. The decoder `trueSourceDecode` is the inverse numbering, so it is
injective and returns `label z` at every source point.

`exists_true_source_core` constructs such `G` and `label` for the actual prepared model at one
depth: the label is the measurable priority assignment of accepted o253's true witnesses
(`prepared_true_first_assignment`) and its native branch, and `G` is a measurable core of full
original mass outside the deleted event `E` of `all_parents_native_sheets`.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain
open Submission.Lib.K4FinitePlankAtlases

noncomputable section

/-- The numbering of true labels: a parent and a native branch. -/
def trueLabel (n : ℕ) : Fin n × Bool ≃ Fin (n * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finProdFinEquiv

/-- The base of an incidence in the common coordinates of the literal domain `D₀`. -/
def commonBase {α : Type} [MeasurableSpace α] (a : PreparedModel α) (k : ℕ) (q χ g m : ℝ)
    (D₀ : Code) (z : α × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (coords q χ g m D₀ (point (a.b k z.1) z.2))

/-- The actual candidate of a true label `l = (i, σ)` in the domain `D₀`: the native sheet
`g i σ` of parent `i`, branch `σ`, composed with the common frame of `D₀`. -/
def trueCandidate {α : Type} [MeasurableSpace α] (p : Parameters) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
    (q χ g' m : ℝ) (D₀ : Code) (l : Fin (a.n k s) × Bool) :
    EuclideanSpace ℂ (Fin 3) → ℂ :=
  fun z => g l.1 l.2
    (affC (commonOffset (parentMatrix (p.K k) (a.q k s) (narrow p k s) (a.c k s l.1))
        (a.parentSupportZoom p k s l.1).baseShift q χ m D₀)
      (commonMatrix (parentMatrix (p.K k) (a.q k s) (narrow p k s) (a.c k s l.1)) q χ g' m D₀) z)

/-- An incidence `z` is native-good for the true label `l = (i, σ)`: packet geometry of
parent `i` at `z`, the native sheet `g i σ` is a stable sheet at the zoomed base of `z`, and
it fits the signal there. -/
def TrueNativeGood {α : Type} [MeasurableSpace α] (p : Parameters) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ)
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ) (ρ V err g' : ℝ)
    (signal : α × ℝ → ℝ) (z : α × ℝ) (l : Fin (a.n k s) × Bool) : Prop :=
  z.2 ∈ Icc (0 : ℝ) 1 ∧ |a.c k s l.1 4| ≤ p.K k ∧ |a.b k z.1 3| ≤ p.K k ∧
  |a.b k z.1 4 - a.c k s l.1 3 - a.c k s l.1 4 * a.b k z.1 3| ≤ p.K k * g' ∧
  SheetOn (Rel l.1) (g l.1 l.2) (toEuc (rootBaseCoordinates (parentZoomPoint p a k s l.1 z)))
    (4 * ρ) V ∧
  |signal z - (g l.1 l.2 (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s l.1 z))))).re|
    ≤ err

/-- A complex number with zero imaginary part is as far from a real number as its real part. -/
theorem norm_ofReal_sub_of_im_eq_zero {x : ℝ} {w : ℂ} (hw : w.im = 0) :
    ‖(x : ℂ) - w‖ = |x - w.re| := by
  have h : (x : ℂ) - w = ((x - w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hw]
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- The native fit of a good incidence, read through the candidate of its label at its
common base. -/
theorem trueCandidate_fit {α : Type} [MeasurableSpace α] (p : Parameters) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) {Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ}
    {g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ} {ρ V err g' : ℝ}
    {signal : α × ℝ → ℝ} {q χ m : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m) (hρ : 0 < ρ)
    (D₀ : Code) {z : α × ℝ} {l : Fin (a.n k s) × Bool}
    (hz : TrueNativeGood p a k s Rel g ρ V err g' signal z l) :
    ‖(signal z : ℂ) - trueCandidate p a k s g q χ g' m D₀ l (emb (commonBase a k q χ g' m D₀ z))‖
      ≤ err := by
  obtain ⟨-, -, -, -, hS, hfit⟩ := hz
  have hpull : trueCandidate p a k s g q χ g' m D₀ l (emb (commonBase a k q χ g' m D₀ z)) =
      g l.1 l.2 (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s l.1 z)))) := by
    unfold trueCandidate commonBase
    rw [affC_common_coords _ _ hq hχ hm, parentZoomPoint_base]
  have him : (g l.1 l.2 (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s l.1 z))))).im
      = 0 := hS.2.2.2 _ (by simpa only [sub_self, norm_zero] using (by positivity : (0 : ℝ) < 4 * ρ))
  rw [hpull, norm_ofReal_sub_of_im_eq_zero him]
  exact hfit

/-- The candidate of a label is a stable sheet with the frame bounds, from one actual
native-good incidence of that label in the domain `D₀`. -/
theorem trueCandidate_sheet {α : Type} [MeasurableSpace α] (p : Parameters)
    (a : PreparedModel α) (k : ℕ) (s : ℝ) {Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ}
    {g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ} {ρ V err : ℝ}
    {signal : α × ℝ → ℝ} {q χ g' m : ℝ} (D₀ : Code)
    (hRel : ∀ i, Rel i ≠ 0 ∧ (Rel i).totalDegree ≤ 4) (hV : 0 ≤ V)
    (hK : 1 ≤ p.K k) (hQ : 0 < a.q k s) (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hgg : g' = narrow p k s) (hg : 0 < g') (hg1 : g' ≤ 1) (hχg : χ ≤ g') (hm : 0 < m)
    (hqg : q * g' ≤ m) (hρ : 0 < ρ)
    (hqsmall : q ≤ ρ * a.q k s / 10000) (hχsmall : χ ≤ ρ * (a.q k s * g') / 10000)
    (hmsmall : m ≤ ρ * (a.q k s * g') / 10000)
    {z₀ : α × ℝ} {l : Fin (a.n k s) × Bool} (hcode : code q χ g' m (a.b k z₀.1) z₀.2 = D₀)
    (hz₀ : TrueNativeGood p a k s Rel g ρ V err g' signal z₀ l) :
    IsSheet 4 (trueCandidate p a k s g q χ g' m D₀ l) ∧
    LipschitzOnWith ⟨4 * V, by positivity⟩
      (fun x => trueCandidate p a k s g q χ g' m D₀ l (emb x)) (closedBall 0 (1 / 2)) := by
  obtain ⟨ht, hc, hb, hslope, hS, -⟩ := hz₀
  obtain ⟨h1, -, h3, -⟩ := parent_common_sheet p a k s l.1 z₀ hS (hRel l.1).1 (hRel l.1).2 hV
    hK hQ hq hχ hχ1 hgg hg hg1 hχg hm hqg hρ ht hqsmall hχsmall hmsmall hc hb hslope
  simp only [hcode] at h1 h3
  subst hgg
  exact ⟨h1, h3⟩

/-- The original true sheet family of the literal domain `D₀` under the current law `μD`.
Witnesses: `G ∩ label⁻¹ {l}`; index: `trueLabel (label z)`; candidates: `trueCandidate` (the
zero sheet only on empty witnesses). -/
def trueSourceFamily {α : Type} [MeasurableSpace α] (p : Parameters) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (μD : Measure (α × ℝ)) (Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ)
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ) {ρ V err : ℝ} (aT : ℝ)
    (Kc : NNReal) (signal : α × ℝ → ℝ) {q χ g' m : ℝ} (D₀ : Code)
    (G : Set (α × ℝ)) (hG : MeasurableSet G) (hGμ : ∀ᵐ z ∂μD, z ∈ G)
    (label : α × ℝ → Fin (a.n k s) × Bool) (hlabel : Measurable label)
    (hRel : ∀ i, Rel i ≠ 0 ∧ (Rel i).totalDegree ≤ 4) (hV : 0 ≤ V) (hKc : 4 * V ≤ Kc)
    (herr : err ≤ aT / 4)
    (hK : 1 ≤ p.K k) (hQ : 0 < a.q k s) (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hgg : g' = narrow p k s) (hg : 0 < g') (hg1 : g' ≤ 1) (hχg : χ ≤ g') (hm : 0 < m)
    (hqg : q * g' ≤ m) (hρ : 0 < ρ)
    (hqsmall : q ≤ ρ * a.q k s / 10000) (hχsmall : χ ≤ ρ * (a.q k s * g') / 10000)
    (hmsmall : m ≤ ρ * (a.q k s * g') / 10000)
    (hgood : ∀ z ∈ G, code q χ g' m (a.b k z.1) z.2 = D₀ ∧
      TrueNativeGood p a k s Rel g ρ V err g' signal z (label z)) :
    OriginalSheetFamily μD 4 aT Kc (commonBase a k q χ g' m D₀) signal :=
  originalSheetFamilyOfPointRules μD (by norm_num) aT Kc (commonBase a k q χ g' m D₀) signal
    (fun z => trueLabel (a.n k s) (label z)) (measurable_of_countable _ |>.comp hlabel)
    (fun j => G ∩ {z | trueLabel (a.n k s) (label z) = j})
    (fun j => hG.inter ((measurable_of_countable _ |>.comp hlabel) (measurableSet_singleton j)))
    (by
      intro j j' hjj'
      refine Set.disjoint_left.mpr fun z hz hz' => hjj' ?_
      exact hz.2.symm.trans hz'.2)
    (by
      filter_upwards [hGμ] with z hz
      exact ⟨hz, rfl⟩)
    (by
      intro j z hz
      have h := hgood z hz.1
      have hn := coords_norm_le hq hχ hg hm hqg (a.b k z.1) h.2.1
      rw [h.1] at hn
      exact hn)
    (fun j => trueCandidate p a k s g q χ g' m D₀ ((trueLabel (a.n k s)).symm j))
    (by
      intro j z₀ hz₀
      have hl : (trueLabel (a.n k s)).symm j = label z₀ := by
        rw [← hz₀.2, Equiv.symm_apply_apply]
      have h₀ := hgood z₀ hz₀.1
      rw [hl]
      obtain ⟨h1, h3⟩ := trueCandidate_sheet p a k s D₀ hRel hV hK hQ hq hχ hχ1 hgg hg hg1
        hχg hm hqg hρ hqsmall hχsmall hmsmall h₀.1 h₀.2
      refine ⟨h1, h3.weaken hKc, ?_⟩
      intro z hz
      have hlz : label z = label z₀ := by
        apply (trueLabel (a.n k s)).injective
        exact hz.2.trans hz₀.2.symm
      rw [← hlz]
      exact (trueCandidate_fit p a k s hq hχ hm hρ D₀ (hgood z hz.1).2).trans herr)

/-- The decoder of true labels of a family: back to a parent and a native branch. -/
def trueSourceDecode (n : ℕ) : Fin (n * 2) → Fin n × Bool := (trueLabel n).symm

theorem trueSourceDecode_injective (n : ℕ) : Function.Injective (trueSourceDecode n) :=
  (trueLabel n).symm.injective

/-- The native branch of parent `i` at an incidence `z` (the branch of its zoomed native
polynomial at its zoomed native point), as in `all_parents_native_sheets`. -/
def nativeBranch {α : Type} [MeasurableSpace α] (p : Parameters) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) (z : α × ℝ) : Bool :=
  branch ((a.parentSupportZoom p k s i).push (a.F k s i))
    (rootBaseCoordinates (parentZoomPoint p a k s i z)) (parentZoomPoint p a k s i z 3)

theorem measurable_parentZoomPoint {α : Type} [MeasurableSpace α] (p : Parameters)
    (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) (hb : Measurable (a.b k)) :
    Measurable (parentZoomPoint p a k s i) :=
  (a.parentSupportZoom p k s i).measurable_nativePoint.comp (a.measurable_nativePoint k hb)

theorem measurable_nativeBranch {α : Type} [MeasurableSpace α] (p : Parameters)
    (a : PreparedModel α) (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) (hb : Measurable (a.b k)) :
    Measurable (nativeBranch p a k s i) := by
  apply measurable_to_bool
  have hset : nativeBranch p a k s i ⁻¹' {true} =
      {z | 0 < eval (fun j => parentZoomPoint p a k s i z j)
        (pderiv 3 ((a.parentSupportZoom p k s i).push (a.F k s i)))} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, nativeBranch, branch, snoc_rootBase,
      decide_eq_true_eq, mem_ofPred_eq]
  rw [hset]
  have hcoord : Measurable (fun z => fun j => parentZoomPoint p a k s i z j) :=
    measurable_pi_iff.mpr fun j =>
      ((PiLp.continuous_apply 2 _ j).measurable).comp (measurable_parentZoomPoint p a k s i hb)
  exact measurableSet_lt measurable_const ((MvPolynomial.continuous_eval _).measurable.comp hcoord)

/-- The labels `z ↦ (assign z, nativeBranch (assign z) z)` of a measurable assignment are
measurable. -/
theorem measurable_trueNativeLabel {α : Type} [MeasurableSpace α] (p : Parameters)
    (a : PreparedModel α) (k : ℕ) (s : ℝ) (hb : Measurable (a.b k))
    {assign : α × ℝ → Fin (a.n k s)} (hassign : Measurable assign) :
    Measurable (fun z => (assign z, nativeBranch p a k s (assign z) z)) := by
  refine hassign.prodMk ?_
  apply measurable_to_countable'
  intro σ
  have hset : (fun z => nativeBranch p a k s (assign z) z) ⁻¹' {σ} =
      ⋃ i, (assign ⁻¹' {i} ∩ nativeBranch p a k s i ⁻¹' {σ}) := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨assign z, rfl, h⟩
    · rintro ⟨i, hi, h⟩
      rw [hi]
      exact h
  rw [hset]
  exact MeasurableSet.iUnion fun i =>
    (hassign (measurableSet_singleton i)).inter
      (measurable_nativeBranch p a k s i hb (measurableSet_singleton σ))

/-- The actual true source core at one depth. The label of an incidence is its priority true
parent (accepted o253's true witnesses, `prepared_true_first_assignment`) with its native
branch. Outside the deleted event `E` of the native sheets, almost every incidence lies in a
measurable core `G` on which it is native-good for its own label. -/
theorem exists_true_source_core {α : Type} [MeasurableSpace α] (p : Parameters)
    (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ}
    (hatlas : a.AtlasAt p R k s)
    (Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ)
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
    (E : Set (α × ℝ)) (hE : MeasurableSet E) {ρ V err : ℝ}
    (hae : ∀ i, ∀ᵐ z ∂a.mu k, z ∈ a.parentSet k s i → z ∉ E →
      SheetOn (Rel i) (g i (nativeBranch p a k s i z))
          (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))) (4 * ρ) V ∧
        |eval (a.x k z.1 z.2) (a.P k) -
          (g i (nativeBranch p a k s i z)
            (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))))).re| ≤ err) :
    ∃ (assign : α × ℝ → Fin (a.n k s)) (G : Set (α × ℝ)),
      Measurable assign ∧
      Measurable (fun z => (assign z, nativeBranch p a k s (assign z) z)) ∧
      MeasurableSet G ∧ Disjoint G E ∧
      (∀ᵐ z ∂a.mu k, z ∉ E → z ∈ G) ∧
      (∑ i, (a.mu k).restrict (firstAssignment (trueWitness a k s) i)) = a.mu k ∧
      ∀ z ∈ G, z ∈ firstAssignment (trueWitness a k s) (assign z) ∧
        TrueNativeGood p a k s Rel g ρ V err (narrow p k s)
          (fun z => eval (a.x k z.1 z.2) (a.P k)) z
          (assign z, nativeBranch p a k s (assign z) z) := by
  obtain ⟨assign, hassign, hfirst, hsum⟩ := prepared_true_first_assignment p hp a hcommon hatlas
  rcases hcommon k with ⟨hbmeas, hnu, _hpi, hdom, _hrho, _hsupp, _hmass, _hPdeg, hb, _hP⟩
  have : IsProbabilityMeasure (a.nu k) := hnu
  have hbprod : ∀ᵐ (z : α × ℝ) ∂(a.nu k).prod volume,
      |a.b k z.1 0| + |a.b k z.1 1| + |a.b k z.1 3| + |a.b k z.1 4| ≤ p.K k :=
    (Measure.quasiMeasurePreserving_fst (μ := a.nu k) (ν := (volume : Measure ℝ))).ae hb
  have hbmu := (Measure.absolutelyContinuous_of_le_smul hdom).ae_le hbprod
  have hall := ae_all_iff.mpr hae
  let P : α × ℝ → Prop := fun z => z ∉ E →
    z ∈ firstAssignment (trueWitness a k s) (assign z) ∧
      TrueNativeGood p a k s Rel g ρ V err (narrow p k s)
        (fun z => eval (a.x k z.1 z.2) (a.P k)) z
        (assign z, nativeBranch p a k s (assign z) z)
  have hP : ∀ᵐ z ∂a.mu k, P z := by
    filter_upwards [hfirst, hbmu, hall] with z hz hzb hzall hzE
    have hmem : z ∈ a.parentSet k s (assign z) := hz.1
    have ht : z.2 ∈ Icc (0 : ℝ) 1 := interval_subset_unit _ _ hmem.2
    rcases hatlas.2.2.2.2.1 (assign z) with ⟨-, -, -, hc, -, hpacket, -, -⟩
    have hA : z.1 ∈ a.A k s (assign z) := ((hatlas.2.2.1 (assign z)).2.2) hmem.1
    have hslope := (hpacket z.1 hA z.2 hmem.2).2.2
    obtain ⟨hS, hfit⟩ := hzall (assign z) hmem hzE
    refine ⟨hz, ht, hc 4, ?_, hslope, hS, hfit⟩
    have h0 := abs_nonneg (a.b k z.1 0)
    have h1 := abs_nonneg (a.b k z.1 1)
    have h4 := abs_nonneg (a.b k z.1 4)
    linarith
  obtain ⟨G₀, hG₀, hG₀c, hG₀P⟩ := measurable_full_source (a.mu k) P hP
  refine ⟨assign, G₀ ∩ Eᶜ, hassign, measurable_trueNativeLabel p a k s hbmeas hassign,
    hG₀.inter hE.compl, Set.disjoint_left.mpr fun z hz hzE => hz.2 hzE, ?_, hsum, ?_⟩
  · have hG₀ae : ∀ᵐ z ∂a.mu k, z ∈ G₀ := mem_ae_iff.mpr hG₀c
    filter_upwards [hG₀ae] with z hz hzE
    exact ⟨hz, hzE⟩
  · intro z hz
    exact hG₀P z hz.1 hz.2

/-- The actual original true families of all literal common domains at one depth, built on
ONE measurable priority assignment `assign` of the true parents. For every current law `μD`
absolutely continuous to the original law, null on the deleted event `E` and carried by the
literal domain `D₀`, the family of `D₀` has an injective decoder into `Fin (a.n k s) × Bool`;
every witness point decodes to its priority parent and its native branch, lies in that
parent's priority set, outside `E` and in `D₀`, and is native-good; every nonempty witness
carries the actual candidate `trueCandidate`; and almost every source point decodes to its own
priority parent and native branch. -/
theorem exists_true_source_families {α : Type} [MeasurableSpace α] (p : Parameters)
    (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hatlas : a.AtlasAt p R k s)
    (Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ)
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
    (E : Set (α × ℝ)) (hE : MeasurableSet E) {ρ V err : ℝ}
    (hRel : ∀ i, Rel i ≠ 0 ∧ (Rel i).totalDegree ≤ 4)
    (hae : ∀ i, ∀ᵐ z ∂a.mu k, z ∈ a.parentSet k s i → z ∉ E →
      SheetOn (Rel i) (g i (nativeBranch p a k s i z))
          (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))) (4 * ρ) V ∧
        |eval (a.x k z.1 z.2) (a.P k) -
          (g i (nativeBranch p a k s i z)
            (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))))).re| ≤ err)
    (aT : ℝ) (Kc : NNReal) (hV : 0 ≤ V) (hKc : 4 * V ≤ Kc) (herr : err ≤ aT / 4)
    {q χ m : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hχg : χ ≤ narrow p k s)
    (hm : 0 < m) (hqg : q * narrow p k s ≤ m) (hρ : 0 < ρ)
    (hqsmall : q ≤ ρ * a.q k s / 10000)
    (hχsmall : χ ≤ ρ * (a.q k s * narrow p k s) / 10000)
    (hmsmall : m ≤ ρ * (a.q k s * narrow p k s) / 10000) :
    ∃ assign : α × ℝ → Fin (a.n k s), Measurable assign ∧
      Measurable (fun z => (assign z, nativeBranch p a k s (assign z) z)) ∧
      (∑ i, (a.mu k).restrict (firstAssignment (trueWitness a k s) i)) = a.mu k ∧
      ∀ (μD : Measure (α × ℝ)) (D₀ : Code), μD ≪ a.mu k → μD E = 0 →
        (∀ᵐ z ∂μD, code q χ (narrow p k s) m (a.b k z.1) z.2 = D₀) →
        ∃ (f : OriginalSheetFamily μD 4 aT Kc (commonBase a k q χ (narrow p k s) m D₀)
            (fun z => eval (a.x k z.1 z.2) (a.P k)))
          (decode : Fin f.n → Fin (a.n k s) × Bool),
          Function.Injective decode ∧
          (∀ j, ∀ z ∈ f.witness j,
            decode j = (assign z, nativeBranch p a k s (assign z) z) ∧
            z ∈ firstAssignment (trueWitness a k s) (assign z) ∧ z ∉ E ∧
            code q χ (narrow p k s) m (a.b k z.1) z.2 = D₀ ∧
            TrueNativeGood p a k s Rel g ρ V err (narrow p k s)
              (fun z => eval (a.x k z.1 z.2) (a.P k)) z (decode j)) ∧
          (∀ j, ∀ z ∈ f.witness j,
            f.f j = trueCandidate p a k s g q χ (narrow p k s) m D₀ (decode j)) ∧
          ∀ᵐ z ∂μD, decode (f.index z) = (assign z, nativeBranch p a k s (assign z) z) := by
  obtain ⟨assign, G, hassign, hlabel, hG, hGE, hGae, hsum, hgood⟩ :=
    exists_true_source_core p hp a hcommon hatlas Rel g E hE hae
  refine ⟨assign, hassign, hlabel, hsum, ?_⟩
  intro μD D₀ hac hE0 hcode
  have hbmeas : Measurable (a.b k) := (hcommon k).1
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hQ : 0 < a.q k s := by unfold PreparedModel.q; positivity
  have hN : 1 ≤ p.N k := by linarith [hp.1 k]
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos (by linarith) _
  have hg1 : narrow p k s ≤ 1 := by
    unfold narrow
    apply Real.rpow_le_one_of_one_le_of_nonpos hN
    have hell : 0 < p.ell := hp.2.2.2.2.2.2.2.1
    nlinarith
  let label : α × ℝ → Fin (a.n k s) × Bool := fun z => (assign z, nativeBranch p a k s (assign z) z)
  let GD : Set (α × ℝ) := G ∩ {z | code q χ (narrow p k s) m (a.b k z.1) z.2 = D₀}
  have hGD : MeasurableSet GD :=
    hG.inter (measurable_code (a.b k) hbmeas q χ (narrow p k s) m (measurableSet_singleton D₀))
  have hGDμ : ∀ᵐ z ∂μD, z ∈ GD := by
    have h1 : ∀ᵐ z ∂μD, z ∉ E → z ∈ G := hac.ae_le hGae
    have h2 : ∀ᵐ z ∂μD, z ∉ E := measure_eq_zero_iff_ae_notMem.mp hE0
    filter_upwards [h1, h2, hcode] with z hz1 hz2 hz3
    exact ⟨hz1 hz2, hz3⟩
  have hgoodD : ∀ z ∈ GD, code q χ (narrow p k s) m (a.b k z.1) z.2 = D₀ ∧
      TrueNativeGood p a k s Rel g ρ V err (narrow p k s)
        (fun z => eval (a.x k z.1 z.2) (a.P k)) z (label z) :=
    fun z hz => ⟨hz.2, (hgood z hz.1).2⟩
  let f := trueSourceFamily p a k s μD Rel g aT Kc (fun z => eval (a.x k z.1 z.2) (a.P k)) D₀
    GD hGD hGDμ label hlabel hRel hV hKc herr hK hQ hq hχ hχ1 rfl hg hg1 hχg hm hqg hρ
    hqsmall hχsmall hmsmall hgoodD
  have hwit (j : Fin (a.n k s * 2)) (z : α × ℝ) (hz : z ∈ f.witness j) :
      z ∈ GD ∧ trueLabel (a.n k s) (label z) = j := hz
  have hdec (j : Fin (a.n k s * 2)) (z : α × ℝ) (hz : z ∈ f.witness j) :
      trueSourceDecode (a.n k s) j = label z := by
    rw [← (hwit j z hz).2]
    exact Equiv.symm_apply_apply _ _
  refine ⟨f, trueSourceDecode (a.n k s), trueSourceDecode_injective _, ?_, ?_, ?_⟩
  · intro j z hz
    have hzG := (hwit j z hz).1
    refine ⟨hdec j z hz, (hgood z hzG.1).1, fun hzE => hGE.ne_of_mem hzG.1 hzE rfl, hzG.2, ?_⟩
    rw [hdec j z hz]
    exact (hgood z hzG.1).2
  · intro j z hz
    have h := witnessCandidate_eq (fun j => GD ∩ {z | trueLabel (a.n k s) (label z) = j})
      (fun j => trueCandidate p a k s g q χ (narrow p k s) m D₀ ((trueLabel (a.n k s)).symm j)) hz
    exact h
  · filter_upwards [f.assigned] with z hz
    exact hdec _ z hz

/-- `exists_true_source_families` for the native sheets of `all_parents_native_sheets`: one
deleted event `E` of original mass at most `K ζ`, common radius `ρ = (2K · 442368 K⁶)^(-n)`,
sheet bound `V = (2K · 442368 K⁶)^n` and native error `32 (2K)⁹ · width`, with
`n = αc A + βc` linear in the loss exponent `A`. -/
theorem exists_actual_true_source_families :
    ∃ αc βc : ℕ, 1 ≤ βc ∧ ∀ (A : ℕ) {α : Type} [MeasurableSpace α] (p : Parameters), p.Valid →
      ∀ a : PreparedModel α, a.Common p → ∀ (R : ℝ) (k : ℕ) (s : ℝ), 0 ≤ s →
      a.AtlasAt p R k s → ∀ δ₀ σ₀ δ₁ σ₁ : ℝ,
      0 < δ₀ → 0 < σ₀ → 0 < δ₁ → 0 < σ₁ →
      δ₀ * (2 * p.K k + 2) ≤ σ₀ * (16 * p.K k * a.q k s * narrow p k s) →
      δ₁ * (2 * p.K k + 2) ≤ σ₁ * (16 * p.K k * a.q k s * narrow p k s) →
      (2 * p.K k * parentFilling (p.K k) (width p k s)) ^ (αc * A + βc) * σ₀ ≤ 1 →
      (2 * p.K k * parentFilling (p.K k) (width p k s)) ^ (αc * A + βc) * σ₁ ≤ width p k s →
      (2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc) * σ₁ ≤ 1 →
      (∀ q : Fin 3 → ℤ, a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₀
          (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = q} ≤
        ENNReal.ofReal ((4 * p.K k + 2) * p.K k * δ₀ ^ 3)) →
      (∀ (q : Fin 3 → ℤ) (x₀ : ℤ), a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₁
          (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = q ∧
          ⌊eval (a.x k z.1 z.2) (a.P k) / width p k s⌋ = x₀} ≤
        ENNReal.ofReal (p.K k * width p k s ^ p.d * δ₁ ^ 3)) →
      ∀ (aT : ℝ) (Kc : NNReal),
      4 * (2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc) ≤ Kc →
      32 * (2 * p.K k) ^ 9 * width p k s ≤ aT / 4 →
      ∀ q χ m : ℝ, 0 < q → 0 < χ → χ ≤ 1 → χ ≤ narrow p k s → 0 < m →
      q * narrow p k s ≤ m →
      q ≤ ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc))⁻¹ * a.q k s / 10000 →
      χ ≤ ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc))⁻¹ *
        (a.q k s * narrow p k s) / 10000 →
      m ≤ ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc))⁻¹ *
        (a.q k s * narrow p k s) / 10000 →
      ∃ (Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ)
        (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ) (E : Set (α × ℝ))
        (assign : α × ℝ → Fin (a.n k s)),
        MeasurableSet E ∧
        a.mu k E ≤ ENNReal.ofReal (p.K k *
          (((2 * p.K k * parentFilling (p.K k) (width p k s)) ^ A)⁻¹ +
            ((2 * p.K k * parentBinCap (p.K k)) ^ A)⁻¹)) ∧
        Measurable assign ∧
        Measurable (fun z => (assign z, nativeBranch p a k s (assign z) z)) ∧
        (∑ i, (a.mu k).restrict (firstAssignment (trueWitness a k s) i)) = a.mu k ∧
        ∀ (μD : Measure (α × ℝ)) (D₀ : Code), μD ≪ a.mu k → μD E = 0 →
          (∀ᵐ z ∂μD, code q χ (narrow p k s) m (a.b k z.1) z.2 = D₀) →
          ∃ (f : OriginalSheetFamily μD 4 aT Kc (commonBase a k q χ (narrow p k s) m D₀)
              (fun z => eval (a.x k z.1 z.2) (a.P k)))
            (decode : Fin f.n → Fin (a.n k s) × Bool),
            Function.Injective decode ∧
            (∀ j, ∀ z ∈ f.witness j,
              decode j = (assign z, nativeBranch p a k s (assign z) z) ∧
              z ∈ firstAssignment (trueWitness a k s) (assign z) ∧ z ∉ E ∧
              code q χ (narrow p k s) m (a.b k z.1) z.2 = D₀ ∧
              TrueNativeGood p a k s Rel g ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc))⁻¹
                ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc))
                (32 * (2 * p.K k) ^ 9 * width p k s) (narrow p k s)
                (fun z => eval (a.x k z.1 z.2) (a.P k)) z (decode j)) ∧
            (∀ j, ∀ z ∈ f.witness j,
              f.f j = trueCandidate p a k s g q χ (narrow p k s) m D₀ (decode j)) ∧
            ∀ᵐ z ∂μD, decode (f.index z) = (assign z, nativeBranch p a k s (assign z) z) := by
  obtain ⟨αc, βc, hβc, hall⟩ := all_parents_native_sheets
  refine ⟨αc, βc, hβc, ?_⟩
  intro A α _ p hp a hcommon R k s hs hatlas δ₀ σ₀ δ₁ σ₁ hδ₀ hσ₀ hδ₁ hσ₁ hr₀ hr₁ hm₀ hm₁ hm₂
    hcap₀ hcapS aT Kc hKc herr q χ m hq hχ hχ1 hχg hm hqg hqsmall hχsmall hmsmall
  obtain ⟨Rel, g, E, hRel, hEm, hEmass, hae⟩ := hall A p hp a hcommon R k s hs hatlas
    δ₀ σ₀ δ₁ σ₁ hδ₀ hσ₀ hδ₁ hσ₁ hr₀ hr₁ hm₀ hm₁ hm₂ hcap₀ hcapS
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hB : 0 < 2 * p.K k * parentBinCap (p.K k) := by
    unfold parentBinCap
    have : 0 < p.K k := by linarith
    positivity
  have hV : 0 ≤ (2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc) := by positivity
  have hρ : 0 < ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc))⁻¹ := by positivity
  obtain ⟨assign, hassign, hlabel, hsum, hfam⟩ := exists_true_source_families p hp a hcommon hs
    hatlas Rel g E hEm hRel hae aT Kc hV hKc herr hq hχ hχ1 hχg hm hqg hρ hqsmall hχsmall
    hmsmall
  exact ⟨Rel, g, E, assign, hEm, hEmass, hassign, hlabel, hsum, hfam⟩

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
