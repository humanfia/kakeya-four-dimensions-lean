import Submission.Obl.k4_scalar_guarded_entropic_path.Info.WeightedReadout
import Submission.Obl.k4_scalar_guarded_entropic_path.Interface

/-!
# The information budget of `ReferenceLaws` as a finite score

`rlScore` is the per-world information expression of the frozen `ReferenceLaws` for a
finite code `X, Y, Z`. `rlScore_eq` rewrites it as the original-likelihood score of the
finite atom masses of `X`. A window whose world laws are, up to their world weights and one
common factor, the world slices of the pushforward of one common law has weighted score
equal to that factor times the total mass times the finite positive score of any common
atom code through which the window codes factor (`weighted_rlScore_eq`). This is the bridge
from the measured windows to the finite window choice of `WeightedReadout`/`StateReadout`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory Set
open Submission.Obl.k4_matching_palette_likelihood
open scoped ENNReal

noncomputable section

/-- The information score of one world in `ReferenceLaws`, for a finite code. -/
def rlScore {n : ℕ} (σ : Measure Incidence) (X : Incidence → Fin n) (Y : Fin n → ℕ)
    (Z : Fin n → ℤ) : ℝ :=
  ∑ i : Fin n, (σ {z | X z = i}).toReal *
    max 0 (Real.log (((σ {z | Y (X z) = Y i ∧ Z (X z) = Z i}).toReal * (σ Set.univ).toReal) /
      ((σ {z | Y (X z) = Y i}).toReal * (σ {z | Z (X z) = Z i}).toReal)))

/-- An injective coding of integer labels by natural numbers. -/
def zEnc (z : ℤ) : ℕ := Encodable.encode z

theorem zEnc_injective : Function.Injective zEnc := Encodable.encode_injective

/-- Masses of the atoms of a measurable finite code. -/
def atomMass {n : ℕ} (σ : Measure Incidence) (X : Incidence → Fin n) (i : Fin n) : ℝ :=
  (σ {z | X z = i}).toReal

theorem measure_preimage_finset {n : ℕ} (σ : Measure Incidence) [IsFiniteMeasure σ]
    {X : Incidence → Fin n} (hX : Measurable X) (s : Finset (Fin n)) :
    (σ {z | X z ∈ s}).toReal = ∑ i ∈ s, atomMass σ X i := by
  classical
  have hset : {z | X z ∈ s} = ⋃ i ∈ s, {z | X z = i} := by
    ext z; simp
  rw [hset, measure_biUnion_finset]
  · rw [ENNReal.toReal_sum]
    · rfl
    · intro i _; exact measure_ne_top _ _
  · intro i _ j _ hij
    exact Set.disjoint_left.mpr fun z hz hz' => hij (hz.symm.trans hz')
  · intro i _
    exact hX (measurableSet_singleton i)

theorem measure_pred_toReal {n : ℕ} (σ : Measure Incidence) [IsFiniteMeasure σ]
    {X : Incidence → Fin n} (hX : Measurable X) (Q : Fin n → Prop) [DecidablePred Q] :
    (σ {z | Q (X z)}).toReal = ∑ x ∈ Finset.univ.filter Q, atomMass σ X x := by
  have := measure_preimage_finset σ hX (Finset.univ.filter Q)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

theorem rlScore_eq {n : ℕ} (σ : Measure Incidence) [IsFiniteMeasure σ]
    {X : Incidence → Fin n} (hX : Measurable X) (Y : Fin n → ℕ) (Z : Fin n → ℤ) :
    rlScore σ X Y Z = ∑ i, atomMass σ X i *
      max 0 (Real.log (originalLikelihood (atomMass σ X) Y (zEnc ∘ Z) i)) := by
  classical
  unfold rlScore originalLikelihood
  apply Finset.sum_congr rfl
  intro i _
  have h1 : (σ {z | Y (X z) = Y i ∧ Z (X z) = Z i}).toReal =
      colorMass (atomMass σ X) Y (zEnc ∘ Z) (Y i) ((zEnc ∘ Z) i) := by
    rw [measure_pred_toReal σ hX (fun x => Y x = Y i ∧ Z x = Z i)]
    unfold colorMass
    simp only [Function.comp_apply, zEnc_injective.eq_iff]
  have h2 : (σ {z | Y (X z) = Y i}).toReal = fiberMass (atomMass σ X) Y (Y i) := by
    rw [measure_pred_toReal σ hX (fun x => Y x = Y i)]
    rfl
  have h3 : (σ {z | Z (X z) = Z i}).toReal =
      fiberMass (atomMass σ X) (zEnc ∘ Z) ((zEnc ∘ Z) i) := by
    rw [measure_pred_toReal σ hX (fun x => Z x = Z i)]
    unfold fiberMass
    simp only [Function.comp_apply, zEnc_injective.eq_iff]
  have h4 : (σ Set.univ).toReal = ∑ j, atomMass σ X j := by
    have := measure_pred_toReal σ hX (fun _ => True)
    simpa using this
  rw [h1, h2, h3, h4]
  rfl


/-- Push a finite law forward along a map of finite types. -/
def pushLaw {α β : Type*} [Fintype α] [DecidableEq β] (p : α → ℝ) (φ : α → β) (b : β) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => φ x = b), p x

theorem pushLaw_filter_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → ℝ) (φ : α → β) (Q : β → Prop) [DecidablePred Q] :
    (∑ b ∈ Finset.univ.filter Q, pushLaw p φ b) =
      ∑ x ∈ Finset.univ.filter (fun x => Q (φ x)), p x := by
  classical
  unfold pushLaw
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => Q (φ x)))
    (t := Finset.univ.filter Q) (g := φ) (fun x hx => by simpa using hx)]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx; exact ⟨hx ▸ (Finset.mem_filter.mp hb).2, hx⟩
  · exact fun h => h.2

theorem fiberMass_pushLaw {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → ℝ) (φ : α → β) (Y : β → ℕ) (e : ℕ) :
    fiberMass (pushLaw p φ) Y e = fiberMass p (Y ∘ φ) e := by
  classical
  unfold fiberMass
  rw [pushLaw_filter_sum p φ (fun b => Y b = e)]
  rfl

theorem colorMass_pushLaw {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → ℝ) (φ : α → β) (Y Z : β → ℕ) (e z : ℕ) :
    colorMass (pushLaw p φ) Y Z e z = colorMass p (Y ∘ φ) (Z ∘ φ) e z := by
  classical
  unfold colorMass
  rw [pushLaw_filter_sum p φ (fun b => Y b = e ∧ Z b = z)]
  rfl

theorem sum_pushLaw {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → ℝ) (φ : α → β) : ∑ b, pushLaw p φ b = ∑ x, p x := by
  classical
  unfold pushLaw
  rw [Finset.sum_fiberwise]

/-- The positive original-likelihood score depends only on the joint law of the two
records: pushing the finite law forward along any map through which both records
factor leaves it unchanged. -/
theorem score_pushLaw {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → ℝ) (φ : α → β) (Y Z : β → ℕ) :
    (∑ b, pushLaw p φ b * max 0 (Real.log (originalLikelihood (pushLaw p φ) Y Z b))) =
      ∑ x, p x * max 0 (Real.log (originalLikelihood p (Y ∘ φ) (Z ∘ φ) x)) := by
  classical
  have hL : ∀ x, originalLikelihood (pushLaw p φ) Y Z (φ x) =
      originalLikelihood p (Y ∘ φ) (Z ∘ φ) x := by
    intro x
    unfold originalLikelihood
    rw [colorMass_pushLaw, fiberMass_pushLaw, fiberMass_pushLaw, sum_pushLaw]
    rfl
  calc (∑ b, pushLaw p φ b * max 0 (Real.log (originalLikelihood (pushLaw p φ) Y Z b)))
      = ∑ b, ∑ x ∈ Finset.univ.filter (fun x => φ x = b),
          p x * max 0 (Real.log (originalLikelihood (pushLaw p φ) Y Z b)) := by
        apply Finset.sum_congr rfl
        intro b _
        unfold pushLaw
        rw [Finset.sum_mul]
    _ = ∑ b, ∑ x ∈ Finset.univ.filter (fun x => φ x = b),
          p x * max 0 (Real.log (originalLikelihood p (Y ∘ φ) (Z ∘ φ) x)) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro x hx
        rw [← (Finset.mem_filter.mp hx).2, hL]
    _ = _ := Finset.sum_fiberwise _ _ _

/-- Scaling a law does not change its likelihood ratios. -/
theorem score_const_mul {α : Type*} [Fintype α] (p : α → ℝ) (Y Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) {c : ℝ} (hc : 0 ≤ c) :
    (∑ x, (c * p x) * max 0 (Real.log (originalLikelihood (fun y => c * p y) Y Z x))) =
      c * ∑ x, p x * max 0 (Real.log (originalLikelihood p Y Z x)) := by
  rcases hc.eq_or_lt with hc0 | hcpos
  · subst hc0; simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p x = 0
  · simp [hx]
  · rw [originalLikelihood_const_mul p Y Z hp (lt_of_le_of_ne (hp x) (Ne.symm hx)) hcpos.ne']
    ring


theorem atomMass_smul {n : ℕ} (σ : Measure Incidence) (X : Incidence → Fin n) (a : ℝ≥0∞) :
    atomMass (a • σ) X = fun i => a.toReal * atomMass σ X i := by
  funext i
  simp [atomMass, ENNReal.toReal_mul]

/-- The world score is homogeneous under scaling the law. -/
theorem rlScore_smul {n : ℕ} (σ : Measure Incidence) [IsFiniteMeasure σ]
    {X : Incidence → Fin n} (hX : Measurable X) (Y : Fin n → ℕ) (Z : Fin n → ℤ)
    {a : ℝ≥0∞} (ha : a ≠ ∞) :
    rlScore (a • σ) X Y Z = a.toReal * rlScore σ X Y Z := by
  have : IsFiniteMeasure (a • σ) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ha) (measure_lt_top σ _)
  rw [rlScore_eq (a • σ) hX, rlScore_eq σ hX, atomMass_smul]
  exact score_const_mul (atomMass σ X) Y (zEnc ∘ Z) (fun _ => ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg

/-- Real masses of the atoms of a finite code of a measure. -/
def codeLaw {Ω T : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Φ : Ω → T) (t : T) : ℝ :=
  (P {ω | Φ ω = t}).toReal

/-- The normalized finite law of a code. -/
def codeProb {Ω T : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Φ : Ω → T) (t : T) : ℝ :=
  codeLaw P Φ t / (P Set.univ).toReal

/-- One world of a world-tagged pushforward. -/
def tagSlice {Ω : Type*} [MeasurableSpace Ω] {W : ℕ} (P : Measure Ω)
    (π : Ω → Fin W × Incidence) (i : Fin W) : Measure Incidence :=
  (P.restrict {ω | (π ω).1 = i}).map (fun ω => (π ω).2)

/-- The masses of a finite code on a measurable finite partition. -/
theorem codeLaw_pred {Ω T : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (P : Measure Ω) [IsFiniteMeasure P] {Φ : Ω → T}
    (hΦ : Measurable Φ) (Q : T → Prop) [DecidablePred Q] :
    (P {ω | Q (Φ ω)}).toReal = ∑ t ∈ Finset.univ.filter Q, codeLaw P Φ t := by
  classical
  have hset : {ω | Q (Φ ω)} = ⋃ t ∈ Finset.univ.filter Q, {ω | Φ ω = t} := by
    ext ω; simp
  rw [hset, measure_biUnion_finset]
  · rw [ENNReal.toReal_sum]
    · rfl
    · intro t _; exact measure_ne_top _ _
  · intro t _ t' _ htt
    exact Set.disjoint_left.mpr fun ω h h' => htt (h.symm.trans h')
  · intro t _
    exact hΦ (measurableSet_singleton t)

theorem sum_codeLaw {Ω T : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (P : Measure Ω) [IsFiniteMeasure P] {Φ : Ω → T}
    (hΦ : Measurable Φ) : ∑ t, codeLaw P Φ t = (P Set.univ).toReal := by
  classical
  have := codeLaw_pred P hΦ (fun _ => True)
  simpa using this.symm


variable {Ω T : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T]
  [MeasurableSingletonClass T]

/-- The world-`i` slice of the finite code law. -/
def sliceLaw (P : Measure Ω) (Φ : Ω → T) {W : ℕ} (f : T → Fin W) (i : Fin W) (t : T) : ℝ :=
  if f t = i then codeLaw P Φ t else 0

theorem atomMass_tagSlice (P : Measure Ω) [IsFiniteMeasure P] {Φ : Ω → T}
    (hΦ : Measurable Φ) {W : ℕ} {π : Ω → Fin W × Incidence} (hπ : Measurable π)
    {f : T → Fin W} (hf : ∀ᵐ ω ∂P, (π ω).1 = f (Φ ω))
    {n : ℕ} {X : Incidence → Fin n} (hX : Measurable X) {φ : T → Fin n}
    (hφ : ∀ᵐ ω ∂P, X (π ω).2 = φ (Φ ω)) (i : Fin W) :
    atomMass (tagSlice P π i) X = pushLaw (sliceLaw P Φ f i) φ := by
  classical
  funext x
  have hπ1 : Measurable (fun ω => (π ω).1) := measurable_fst.comp hπ
  have hπ2 : Measurable (fun ω => (π ω).2) := measurable_snd.comp hπ
  have hW : MeasurableSet {ω | (π ω).1 = i} := hπ1 (measurableSet_singleton i)
  have hXs : MeasurableSet {z : Incidence | X z = x} := hX (measurableSet_singleton x)
  unfold atomMass tagSlice
  rw [Measure.map_apply hπ2 hXs, Measure.restrict_apply (hπ2 hXs)]
  have hcongr : P ((fun ω => (π ω).2) ⁻¹' {z | X z = x} ∩ {ω | (π ω).1 = i}) =
      P {ω | (fun t => f t = i ∧ φ t = x) (Φ ω)} := by
    apply measure_congr
    filter_upwards [hf, hφ] with ω h1 h2
    apply propext
    simp only [mem_inter_iff, mem_preimage, Set.mem_ofPred_eq]
    rw [h1, h2]
    exact and_comm
  rw [hcongr, codeLaw_pred P hΦ (fun t => f t = i ∧ φ t = x)]
  unfold pushLaw sliceLaw
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h1 : f t = i <;> by_cases h2 : φ t = x <;> simp [h1, h2]

/-- The frozen world score of one world slice, as a finite score on the common atoms. -/
theorem rlScore_tagSlice (P : Measure Ω) [IsFiniteMeasure P] {Φ : Ω → T}
    (hΦ : Measurable Φ) {W : ℕ} {π : Ω → Fin W × Incidence} (hπ : Measurable π)
    {f : T → Fin W} (hf : ∀ᵐ ω ∂P, (π ω).1 = f (Φ ω))
    {n : ℕ} {X : Incidence → Fin n} (hX : Measurable X) {φ : T → Fin n}
    (hφ : ∀ᵐ ω ∂P, X (π ω).2 = φ (Φ ω)) (Yc : Fin n → ℕ) (Zc : Fin n → ℤ) (i : Fin W) :
    rlScore (tagSlice P π i) X Yc Zc =
      ∑ t, sliceLaw P Φ f i t * max 0 (Real.log
        (originalLikelihood (sliceLaw P Φ f i) (Yc ∘ φ) ((zEnc ∘ Zc) ∘ φ) t)) := by
  have hfin : IsFiniteMeasure (tagSlice P π i) := by
    unfold tagSlice; infer_instance
  rw [rlScore_eq _ hX, atomMass_tagSlice P hΦ hπ hf hX hφ i]
  exact score_pushLaw _ φ Yc (zEnc ∘ Zc)


/-- Remembering a label that is constant on the support does not change likelihoods. -/
theorem originalLikelihood_pair_of_support {α : Type*} [Fintype α] (r : α → ℝ)
    (F Y V : α → ℕ) (t : α) (hr : ∀ s, F s ≠ F t → r s = 0) :
    originalLikelihood r (pairedRecord F Y) V t = originalLikelihood r Y V t := by
  classical
  have hcol : colorMass r (pairedRecord F Y) V (pairedRecord F Y t) (V t) =
      colorMass r Y V (Y t) (V t) := by
    unfold colorMass
    apply Finset.sum_subset
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairedRecord,
        Nat.pair_eq_pair] at hs ⊢
      exact ⟨hs.1.2, hs.2⟩
    · intro s hs hs'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairedRecord,
        Nat.pair_eq_pair] at hs hs'
      apply hr
      intro hF
      exact hs' ⟨⟨hF, hs.1⟩, hs.2⟩
  have hfib : fiberMass r (pairedRecord F Y) (pairedRecord F Y t) = fiberMass r Y (Y t) := by
    unfold fiberMass
    apply Finset.sum_subset
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairedRecord,
        Nat.pair_eq_pair] at hs ⊢
      exact hs.2
    · intro s hs hs'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairedRecord,
        Nat.pair_eq_pair] at hs hs'
      apply hr
      intro hF
      exact hs' ⟨hF, hs⟩
  unfold originalLikelihood
  rw [hcol, hfib]

theorem rlScore_zero {n : ℕ} (X : Incidence → Fin n) (Y : Fin n → ℕ) (Z : Fin n → ℤ) :
    rlScore 0 X Y Z = 0 := by
  simp [rlScore]


/-- **Window score transfer.** When each world law of a window is, up to its world weight
and one common factor `c`, the world slice of the pushforward of one common law, the
weighted frozen information expression is `c` times the total mass times the finite
positive score of the common atom code. -/
theorem weighted_rlScore_eq (P : Measure Ω) [IsFiniteMeasure P] {Φ : Ω → T}
    (hΦ : Measurable Φ) {W : ℕ} {π : Ω → Fin W × Incidence} (hπ : Measurable π)
    {f : T → Fin W} (hf : ∀ᵐ ω ∂P, (π ω).1 = f (Φ ω))
    {n : ℕ} {X : Incidence → Fin n} (hX : Measurable X) {φ : T → Fin n}
    (hφ : ∀ᵐ ω ∂P, X (π ω).2 = φ (Φ ω)) (Yc : Fin n → ℕ) (Zc : Fin n → ℤ)
    (ω : Fin W → ℝ) (hω : ∀ i, 0 ≤ ω i) {c : ℝ} (hc : 0 ≤ c)
    (σ : Fin W → Measure Incidence) [∀ i, IsFiniteMeasure (σ i)]
    (hσ : ∀ i, ENNReal.ofReal (ω i) • σ i = ENNReal.ofReal c • tagSlice P π i) :
    (∑ i, ω i * rlScore (σ i) X Yc Zc) =
      c * ((P Set.univ).toReal * positiveScore (codeProb P Φ) (fun t => (f t).val)
        (pairedRecord (fun t => (f t).val) (Yc ∘ φ)) ((zEnc ∘ Zc) ∘ φ)) := by
  classical
  have hfin : ∀ i, IsFiniteMeasure (tagSlice P π i) := fun i => by
    unfold tagSlice; infer_instance
  -- world by world, the weight cancels against the normalization
  have hworld : ∀ i, ω i * rlScore (σ i) X Yc Zc = c * rlScore (tagSlice P π i) X Yc Zc := by
    intro i
    have h1 : rlScore (ENNReal.ofReal (ω i) • σ i) X Yc Zc =
        rlScore (ENNReal.ofReal c • tagSlice P π i) X Yc Zc := by rw [hσ i]
    rw [rlScore_smul _ hX _ _ ENNReal.ofReal_ne_top, rlScore_smul _ hX _ _ ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (hω i), ENNReal.toReal_ofReal hc] at h1
    exact h1
  simp_rw [hworld, ← Finset.mul_sum]
  congr 1
  simp_rw [rlScore_tagSlice P hΦ hπ hf hX hφ Yc Zc]
  set E := pairedRecord (fun t => (f t).val) (Yc ∘ φ)
  set V := (zEnc ∘ Zc) ∘ φ
  have hpair : ∀ i t, sliceLaw P Φ f i t * max 0 (Real.log
      (originalLikelihood (sliceLaw P Φ f i) (Yc ∘ φ) V t)) =
      sliceLaw P Φ f i t * max 0 (Real.log (originalLikelihood (sliceLaw P Φ f i) E V t)) := by
    intro i t
    by_cases ht : f t = i
    · rw [originalLikelihood_pair_of_support]
      intro s hs
      have : f s ≠ i := fun h => hs (by rw [h, ht])
      simp [sliceLaw, this]
    · simp [sliceLaw, ht]
  simp_rw [hpair]
  have hlaw_nonneg : ∀ t, 0 ≤ codeLaw P Φ t := fun t => ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_nonneg : (0 : ℝ) ≤ (P Set.univ).toReal).eq_or_lt with h0 | hpos
  · -- the zero law: every atom has mass zero
    have hzero : ∀ t, codeLaw P Φ t = 0 := by
      intro t
      apply le_antisymm _ (hlaw_nonneg t)
      calc codeLaw P Φ t ≤ (P Set.univ).toReal :=
            ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
        _ = 0 := h0.symm
    rw [← h0, zero_mul]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro t _
    simp [sliceLaw, hzero]
  · have hw := weighted_original_score_eq (codeProb P Φ) f E V (sliceLaw P Φ f)
      (fun _ => (1 : ℝ)) (P Set.univ).toReal
      (fun t => div_nonneg (hlaw_nonneg t) hpos.le)
      (fun i t => by unfold sliceLaw; split_ifs <;> simp [hlaw_nonneg])
      (fun _ => zero_le_one) hpos
      (fun x y h => Fin.ext (Nat.pair_eq_pair.mp h).1)
      (fun i t => by
        unfold sliceLaw codeProb
        split_ifs
        · field_simp
        · simp)
    simpa only [one_mul] using hw

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
