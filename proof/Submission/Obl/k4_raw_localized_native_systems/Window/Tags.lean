/- Adapted from this LOT tree, o197, session x0692, Window/Tags.lean,
   branch snapshot 07a5fc04; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.Window.Witness

/-!
# Earlier-witness tags and the weighted domination

Each incidence of a full-time chart `a` is tagged by the least earlier witness
chart that is compatible with `a` and contains it.  The tag is measurable, and
the original-budget-weighted tagged pushforwards of the full-time laws are
dominated by the original weights times the normalized witness laws:
`Σ_a R_a (z_e)_* (law_a | tag = e) ≤ w_e Λ_e`.  The full-time events of one
world are disjoint, so there is no factor of the number of full-time charts.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

open Classical in
/-- The least index whose set contains `q`, or `d` when there is none. -/
def tagOf {n : ℕ} (S : Fin n → Set Point) (d : Fin n) (q : Point) : Fin n :=
  if h : (Finset.univ.filter (fun e => q ∈ S e)).Nonempty then
    (Finset.univ.filter (fun e => q ∈ S e)).min' h else d

theorem tagOf_mem {n : ℕ} (S : Fin n → Set Point) (d : Fin n) {q : Point}
    (hq : q ∈ ⋃ e, S e) : q ∈ S (tagOf S d q) := by
  classical
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hq
  have hne : (Finset.univ.filter (fun e => q ∈ S e)).Nonempty := ⟨e, by simp [he]⟩
  unfold tagOf
  rw [dif_pos hne]
  have := Finset.min'_mem _ hne
  simpa using this

theorem tagOf_eq_iff {n : ℕ} (S : Fin n → Set Point) (d : Fin n) (q : Point) (e : Fin n) :
    tagOf S d q = e ↔
      (q ∈ S e ∧ ∀ e', e' < e → q ∉ S e') ∨ ((∀ e', q ∉ S e') ∧ e = d) := by
  classical
  unfold tagOf
  by_cases hne : (Finset.univ.filter (fun e => q ∈ S e)).Nonempty
  · rw [dif_pos hne, Finset.min'_eq_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨he, hmin⟩
      exact Or.inl ⟨he, fun e' he' hq => absurd (hmin e' hq) (not_le.mpr he')⟩
    · rintro (⟨he, hmin⟩ | ⟨hnone, -⟩)
      · exact ⟨he, fun b hb => not_lt.mp fun hlt => hmin b hlt hb⟩
      · obtain ⟨e', he'⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he'
        exact absurd he' (hnone e')
  · rw [dif_neg hne]
    have hnone : ∀ e', q ∉ S e' := by
      intro e' he'
      exact hne ⟨e', by simp [he']⟩
    constructor
    · rintro rfl
      exact Or.inr ⟨hnone, rfl⟩
    · rintro (⟨he, -⟩ | ⟨-, rfl⟩)
      · exact absurd he (hnone e)
      · rfl

theorem measurable_tagOf {n : ℕ} (S : Fin n → Set Point) (hS : ∀ e, MeasurableSet (S e))
    (d : Fin n) : Measurable (tagOf S d) := by
  classical
  apply measurable_to_countable'
  intro e
  have hset : tagOf S d ⁻¹' {e} =
      (S e ∩ ⋂ e' ∈ (Finset.univ.filter (fun e' => e' < e)), (S e')ᶜ) ∪
        ((⋂ e', (S e')ᶜ) ∩ {_q | e = d}) := by
    ext q
    simp only [mem_preimage, mem_singleton_iff, tagOf_eq_iff, mem_union, mem_inter_iff,
      mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and, mem_compl_iff, mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.union ((hS e).inter ?_) ((MeasurableSet.iInter fun e' => (hS e').compl).inter ?_)
  · exact Finset.measurableSet_biInter _ fun e' _ => (hS e').compl
  · by_cases h : e = d
    · simp [h]
    · simp [h]

/-! ### Compatible events and the certificate support -/

variable {p : Data} {k : ℕ}

/-- The event of witness chart `e`, when it is compatible with full-time chart `a`. -/
def compatEvent (W : Atlas p k) {C : ℕ} (Compat : Fin C → Fin W.C → Prop) (a : Fin C)
    (e : Fin W.C) : Set Point :=
  {q | Compat a e ∧ q ∈ W.F e}

/-- The support of the full-time law `a` in the window certificate. -/
def certSupport (W : Atlas p k) {C : ℕ} (Compat : Fin C → Fin W.C → Prop)
    (FC : Fin C → Set Point) (a : Fin C) : Set Point :=
  FC a ∩ ⋃ e, compatEvent W Compat a e

/-- The witness tag of an incidence of full-time chart `a`. -/
def ctag (W : Atlas p k) {C : ℕ} (Compat : Fin C → Fin W.C → Prop) (d : Fin W.C) (a : Fin C) :
    Point → Fin W.C :=
  tagOf (compatEvent W Compat a) d

theorem measurableSet_compatEvent (W : Atlas p k) {C : ℕ} (Compat : Fin C → Fin W.C → Prop)
    (hF : ∀ e, MeasurableSet (W.F e)) (a : Fin C) (e : Fin W.C) :
    MeasurableSet (compatEvent W Compat a e) := by
  classical
  by_cases h : Compat a e
  · have : compatEvent W Compat a e = W.F e := by
      ext q; simp [compatEvent, h]
    rw [this]; exact hF e
  · have : compatEvent W Compat a e = ∅ := by
      ext q; simp [compatEvent, h]
    rw [this]; exact MeasurableSet.empty

theorem measurableSet_certSupport (W : Atlas p k) {C : ℕ} (Compat : Fin C → Fin W.C → Prop)
    (hF : ∀ e, MeasurableSet (W.F e)) {FC : Fin C → Set Point} (hFC : ∀ a, MeasurableSet (FC a))
    (a : Fin C) : MeasurableSet (certSupport W Compat FC a) :=
  (hFC a).inter (MeasurableSet.iUnion fun e => measurableSet_compatEvent W Compat hF a e)

theorem measurable_ctag (W : Atlas p k) {C : ℕ} (Compat : Fin C → Fin W.C → Prop)
    (hF : ∀ e, MeasurableSet (W.F e)) (d : Fin W.C) (a : Fin C) :
    Measurable (ctag W Compat d a) :=
  measurable_tagOf _ (measurableSet_compatEvent W Compat hF a) d

/-- A supported incidence lies in the event of its tag, which is compatible. -/
theorem ctag_spec (W : Atlas p k) {C : ℕ} (Compat : Fin C → Fin W.C → Prop) (d : Fin W.C)
    {FC : Fin C → Set Point} {a : Fin C} {q : Point} (hq : q ∈ certSupport W Compat FC a) :
    q ∈ FC a ∧ Compat a (ctag W Compat d a q) ∧ q ∈ W.F (ctag W Compat d a q) := by
  have h := tagOf_mem (compatEvent W Compat a) d hq.2
  exact ⟨hq.1, h.1, h.2⟩

/-! ### The weighted domination -/

/-- **Global weighted domination.**  Restricting the full-time laws to their
supports with tag `e`, weighting by the budgets `R_a` and pushing forward to the
normalized coordinates of `e` gives at most `w_e Λ_e`. -/
theorem tagged_domination (hp : Valid p) (W : Atlas p k) {M D : ℕ} {κ r : ℝ}
    (hW : ∀ e, WChart p k W M D κ r e) (hpos : ∀ e, 0 < wmass W e)
    {C : ℕ} (γC : Fin C → Fin (p.W k)) (FC : Fin C → Set Point)
    (law : Fin C → Measure Point) (R : Fin C → ENNReal)
    (Compat : Fin C → Fin W.C → Prop) (hcw : ∀ a e, Compat a e → W.γ e = γC a)
    (hFC : ∀ a, MeasurableSet (FC a))
    (hFCdisj : ∀ a a', a ≠ a' → γC a = γC a' → Disjoint (FC a) (FC a'))
    (hlaw : ∀ a, R a • law a ≤
      ENNReal.ofReal (p.ω k (γC a)) • (priorMass p k (γC a)).restrict (FC a))
    (d : Fin W.C) (e : Fin W.C) :
    (∑ a, R a • Measure.map (wz W e) ((law a).restrict
        {q | q ∈ certSupport W Compat FC a ∧ ctag W Compat d a q = e})) ≤
      wwt W e • wlaw W e := by
  classical
  have hF : ∀ e, MeasurableSet (W.F e) := fun e => (hW e).measF
  set γ := W.γ e
  set X : Fin C → Set Point :=
    fun a => {q | q ∈ certSupport W Compat FC a ∧ ctag W Compat d a q = e} with hXdef
  have hX : ∀ a, MeasurableSet (X a) := fun a =>
    (measurableSet_certSupport W Compat hF hFC a).inter
      (measurable_ctag W Compat hF d a (measurableSet_singleton e))
  have hXsub : ∀ a, X a ⊆ {q | Compat a e ∧ q ∈ FC a ∧ q ∈ W.F e} := by
    intro a q hq
    obtain ⟨hsupp, htag⟩ := hq
    obtain ⟨hFCq, hc, hWF⟩ := ctag_spec W Compat d hsupp
    rw [htag] at hc hWF
    exact ⟨hc, hFCq, hWF⟩
  -- the right-hand side
  have hrhs : wwt W e • wlaw W e =
      ENNReal.ofReal (p.ω k γ) • Measure.map (wz W e) ((priorMass p k γ).restrict (W.F e)) := by
    rw [wwt, wlaw, smul_smul, mul_assoc, ENNReal.mul_inv_cancel (hpos e).ne'
      (wmass_ne_top hp (hW e)), mul_one]
  rw [hrhs]
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (measurable_wz W e) hs, Measure.restrict_apply ((measurable_wz W e) hs)]
  set Y := wz W e ⁻¹' s with hYdef
  have hY : MeasurableSet Y := (measurable_wz W e) hs
  have hterm : ∀ a, R a * (Measure.map (wz W e) ((law a).restrict (X a))) s ≤
      if γC a = γ then ENNReal.ofReal (p.ω k γ) * priorMass p k γ (FC a ∩ (Y ∩ W.F e)) else 0 := by
    intro a
    rw [Measure.map_apply (measurable_wz W e) hs, Measure.restrict_apply hY]
    by_cases hc : Compat a e
    · have hγ : γC a = γ := (hcw a e hc).symm
      rw [if_pos hγ]
      have h1 := hlaw a (Y ∩ X a)
      simp only [Measure.smul_apply, smul_eq_mul] at h1
      rw [Measure.restrict_apply (hY.inter (hX a))] at h1
      calc R a * (law a) (Y ∩ X a) ≤ ENNReal.ofReal (p.ω k (γC a)) *
            priorMass p k (γC a) (Y ∩ X a ∩ FC a) := h1
        _ ≤ ENNReal.ofReal (p.ω k γ) * priorMass p k γ (FC a ∩ (Y ∩ W.F e)) := by
            rw [hγ]
            refine mul_le_mul_right (measure_mono fun q hq => ?_) _
            have hqX : q ∈ X a := hq.1.2
            have := hXsub a hqX
            exact ⟨hq.2, hq.1.1, this.2.2⟩
    · have hempty : Y ∩ X a = ∅ := by
        ext q
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro _ hq
        exact hc (hXsub a hq).1
      rw [hempty, measure_empty, mul_zero]
      split_ifs <;> exact le_rfl.trans (by simp)
  calc ∑ a, R a * (Measure.map (wz W e) ((law a).restrict (X a))) s
      ≤ ∑ a, (if γC a = γ then
          ENNReal.ofReal (p.ω k γ) * priorMass p k γ (FC a ∩ (Y ∩ W.F e)) else 0) :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = ENNReal.ofReal (p.ω k γ) *
          ∑ a ∈ Finset.univ.filter (fun a => γC a = γ), priorMass p k γ (FC a ∩ (Y ∩ W.F e)) := by
        rw [← Finset.sum_filter, Finset.mul_sum]
    _ = ENNReal.ofReal (p.ω k γ) *
          priorMass p k γ (⋃ a ∈ Finset.univ.filter (fun a => γC a = γ), FC a ∩ (Y ∩ W.F e)) := by
        congr 1
        rw [measure_biUnion_finset]
        · intro a ha a' ha' hne
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at ha ha'
          exact ((hFCdisj a a' hne (ha.trans ha'.symm)).mono inter_subset_left inter_subset_left)
        · exact fun a _ => (hFC a).inter (hY.inter (hF e))
    _ ≤ ENNReal.ofReal (p.ω k γ) * priorMass p k γ (Y ∩ W.F e) := by
        gcongr
        intro q hq
        simp only [mem_iUnion] at hq
        obtain ⟨a, -, hqa⟩ := hq
        exact hqa.2

end
end Submission.Obl.k4_raw_localized_native_systems.Window
