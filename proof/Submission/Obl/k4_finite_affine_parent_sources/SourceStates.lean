-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Mathlib

/-!
# Appended states: floors and joint numerators

A finite measure `λ` carries an end history `endL` (finitely many values) and a state code
`code` (countably many values). Suppose every end history and every velocity event `b` of a
class satisfy the numerator `λ ({endL = h} ∩ b) ≤ C w(h) β(b)`. Keep the incidences whose
(end history, code) state has mass at least `δ w(h)`. Then

* the kept part of any union of code values `code⁻¹ V` meets every velocity event `b` in mass
  at most `(C / δ) β(b) λ (code⁻¹ V)` (no count of states is used);
* the deleted mass is at most `δ Σ_h #codes(h) w(h)`, if every end history carries at most
  `#codes(h)` codes of positive mass.

This is the appended-entry floor of paper Lemma 4.8, written for an arbitrary finite measure.
Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

section States

variable {Ω H Q : Type*} [MeasurableSpace Ω] [Fintype H] [Countable Q]
    (lam : Measure Ω) (endL : Ω → H) (code : Ω → Q)

/-- The mass of one state. -/
def stateMass (h : H) (c : Q) : ENNReal := lam ({x | endL x = h} ∩ {x | code x = c})

/-- The kept incidences: those whose state carries the floor. -/
def keptSet (w : H → ENNReal) (δ : ENNReal) : Set Ω :=
  {x | δ * w (endL x) ≤ stateMass lam endL code (endL x) (code x)}

variable {lam endL code}

theorem keptSet_eq_iUnion (w : H → ENNReal) (δ : ENNReal) :
    keptSet lam endL code w δ = ⋃ (h : H) (c : Q),
      if δ * w h ≤ stateMass lam endL code h c then {x | endL x = h} ∩ {x | code x = c}
      else ∅ := by
  ext x
  simp only [keptSet, mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hx
    refine ⟨endL x, code x, ?_⟩
    rw [if_pos hx]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h, c, hx⟩
    split_ifs at hx with hc
    · obtain ⟨h1, h2⟩ := hx
      simp only [mem_ofPred_eq] at h1 h2
      rw [h1, h2]
      exact hc
    · exact hx.elim

theorem measurableSet_keptSet [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (hend : Measurable endL) (hcode : Measurable code) (w : H → ENNReal) (δ : ENNReal) :
    MeasurableSet (keptSet lam endL code w δ) := by
  rw [keptSet_eq_iUnion]
  refine MeasurableSet.iUnion fun h => MeasurableSet.iUnion fun c => ?_
  split_ifs
  · exact (hend (measurableSet_singleton h)).inter (hcode (measurableSet_singleton c))
  · exact MeasurableSet.empty

/-- **Joint numerator of the kept part.** -/
theorem kept_joint_le [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (hend : Measurable endL) (hcode : Measurable code)
    (w : H → ENNReal) {δ : ENNReal} (hδ0 : δ ≠ 0) (hδt : δ ≠ ⊤)
    {C β : ENNReal} {b : Set Ω} (hb : MeasurableSet b)
    (hnum : ∀ h, lam ({x | endL x = h} ∩ b) ≤ C * w h * β)
    (V : Set Q) :
    lam (keptSet lam endL code w δ ∩ code ⁻¹' V ∩ b) ≤
      C / δ * β * lam (code ⁻¹' V) := by
  classical
  -- decompose by states
  have hcover : keptSet lam endL code w δ ∩ code ⁻¹' V ∩ b ⊆
      ⋃ (h : H) (c : V), (keptSet lam endL code w δ ∩ ({x | endL x = h} ∩ {x | code x = c})) ∩ b := by
    intro x hx
    simp only [mem_iUnion]
    exact ⟨endL x, ⟨code x, hx.1.2⟩, ⟨hx.1.1, rfl, rfl⟩, hx.2⟩
  have hstate (h : H) (c : Q) :
      lam ((keptSet lam endL code w δ ∩ ({x | endL x = h} ∩ {x | code x = c})) ∩ b) ≤
        C / δ * β * stateMass lam endL code h c := by
    by_cases hk : δ * w h ≤ stateMass lam endL code h c
    · calc lam ((keptSet lam endL code w δ ∩ ({x | endL x = h} ∩ {x | code x = c})) ∩ b)
          ≤ lam ({x | endL x = h} ∩ b) :=
            measure_mono (fun x hx => ⟨hx.1.2.1, hx.2⟩)
        _ ≤ C * w h * β := hnum h
        _ ≤ C / δ * β * stateMass lam endL code h c := by
            calc C * w h * β = C / δ * β * (δ * w h) := by
                  rw [ENNReal.div_eq_inv_mul]
                  calc C * w h * β = (δ⁻¹ * δ) * (C * w h * β) := by
                        rw [ENNReal.inv_mul_cancel hδ0 hδt, one_mul]
                    _ = δ⁻¹ * C * β * (δ * w h) := by ring
              _ ≤ C / δ * β * stateMass lam endL code h c := by gcongr
    · have hempty : keptSet lam endL code w δ ∩ ({x | endL x = h} ∩ {x | code x = c}) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hh, hc⟩
        simp only [mem_ofPred_eq] at hh hc
        simp only [keptSet, mem_ofPred_eq, hh, hc] at hx
        exact hk hx
      rw [hempty, empty_inter, measure_empty]
      exact bot_le
  calc lam (keptSet lam endL code w δ ∩ code ⁻¹' V ∩ b)
      ≤ lam (⋃ (h : H) (c : V),
          (keptSet lam endL code w δ ∩ ({x | endL x = h} ∩ {x | code x = c})) ∩ b) :=
        measure_mono hcover
    _ ≤ ∑' (h : H), ∑' (c : V),
          lam ((keptSet lam endL code w δ ∩ ({x | endL x = h} ∩ {x | code x = c})) ∩ b) :=
        (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun h => measure_iUnion_le _)
    _ ≤ ∑' (h : H), ∑' (c : V), C / δ * β * stateMass lam endL code h c :=
        ENNReal.tsum_le_tsum fun h => ENNReal.tsum_le_tsum fun c => hstate h c
    _ = C / δ * β * ∑' (h : H), ∑' (c : V), stateMass lam endL code h c := by
        simp_rw [ENNReal.tsum_mul_left]
    _ = C / δ * β * lam (code ⁻¹' V) := by
        congr 1
        have hdisj : lam (code ⁻¹' V) = ∑' (h : H), ∑' (c : V), stateMass lam endL code h c := by
          have hset : code ⁻¹' V = ⋃ (h : H) (c : V), ({x | endL x = h} ∩ {x | code x = c}) := by
            ext x
            simp only [mem_preimage, mem_iUnion]
            constructor
            · intro hx
              exact ⟨endL x, ⟨code x, hx⟩, rfl, rfl⟩
            · rintro ⟨h, c, -, hc⟩
              simp only [mem_ofPred_eq] at hc
              rw [hc]
              exact c.2
          rw [hset, measure_iUnion]
          · congr 1
            funext h
            rw [measure_iUnion]
            · rfl
            · intro c c' hcc'
              refine Set.disjoint_left.mpr fun x hx hx' => hcc' ?_
              apply Subtype.ext
              exact hx.2.symm.trans hx'.2
            · intro c
              exact (hend (measurableSet_singleton h)).inter (hcode (measurableSet_singleton _))
          · intro h h' hhh'
            simp only [Function.onFun]
            refine Set.disjoint_left.mpr fun x hx hx' => hhh' ?_
            simp only [mem_iUnion] at hx hx'
            obtain ⟨c, hx⟩ := hx
            obtain ⟨c', hx'⟩ := hx'
            exact hx.1.symm.trans hx'.1
          · intro h
            exact MeasurableSet.iUnion fun c =>
              (hend (measurableSet_singleton h)).inter (hcode (measurableSet_singleton _))
        exact hdisj.symm

/-- **Deleted mass of the floors.** -/
theorem deleted_le (w : H → ENNReal) (δ : ENNReal) (V : H → Finset Q)
    (hV : ∀ h, lam ({x | endL x = h} ∩ {x | code x ∉ V h}) = 0) :
    lam (keptSet lam endL code w δ)ᶜ ≤ ∑ h, ((V h).card : ENNReal) * (δ * w h) := by
  classical
  have hcover : (keptSet lam endL code w δ)ᶜ ⊆ ⋃ h : H,
      ((⋃ c ∈ V h, ({x | endL x = h} ∩ {x | code x = c}) ∩ (keptSet lam endL code w δ)ᶜ) ∪
        ({x | endL x = h} ∩ {x | code x ∉ V h})) := by
    intro x hx
    simp only [mem_iUnion, mem_union]
    refine ⟨endL x, ?_⟩
    by_cases hc : code x ∈ V (endL x)
    · left
      simp only [mem_iUnion, exists_prop]
      exact ⟨code x, hc, ⟨rfl, rfl⟩, hx⟩
    · right
      exact ⟨rfl, hc⟩
  have hstate (h : H) (c : Q) :
      lam (({x | endL x = h} ∩ {x | code x = c}) ∩ (keptSet lam endL code w δ)ᶜ) ≤ δ * w h := by
    by_cases hk : δ * w h ≤ stateMass lam endL code h c
    · have hempty : ({x | endL x = h} ∩ {x | code x = c}) ∩ (keptSet lam endL code w δ)ᶜ = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨⟨hh, hc⟩, hx⟩
        simp only [mem_ofPred_eq] at hh hc
        apply hx
        simp only [keptSet, mem_ofPred_eq, hh, hc]
        exact hk
      rw [hempty, measure_empty]
      exact bot_le
    · push Not at hk
      exact (measure_mono inter_subset_left).trans hk.le
  calc lam (keptSet lam endL code w δ)ᶜ
      ≤ lam (⋃ h : H,
          ((⋃ c ∈ V h, ({x | endL x = h} ∩ {x | code x = c}) ∩ (keptSet lam endL code w δ)ᶜ) ∪
            ({x | endL x = h} ∩ {x | code x ∉ V h}))) := measure_mono hcover
    _ ≤ ∑ h : H, lam
          ((⋃ c ∈ V h, ({x | endL x = h} ∩ {x | code x = c}) ∩ (keptSet lam endL code w δ)ᶜ) ∪
            ({x | endL x = h} ∩ {x | code x ∉ V h})) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ h : H, ((V h).card : ENNReal) * (δ * w h) := by
        refine Finset.sum_le_sum fun h _ => ?_
        calc lam ((⋃ c ∈ V h, ({x | endL x = h} ∩ {x | code x = c}) ∩
              (keptSet lam endL code w δ)ᶜ) ∪ ({x | endL x = h} ∩ {x | code x ∉ V h}))
            ≤ lam (⋃ c ∈ V h, ({x | endL x = h} ∩ {x | code x = c}) ∩
                (keptSet lam endL code w δ)ᶜ) + lam ({x | endL x = h} ∩ {x | code x ∉ V h}) :=
              measure_union_le _ _
          _ ≤ ∑ c ∈ V h, lam (({x | endL x = h} ∩ {x | code x = c}) ∩
                (keptSet lam endL code w δ)ᶜ) + 0 := by
              rw [hV h]
              exact add_le_add (measure_biUnion_finset_le _ _) le_rfl
          _ ≤ ∑ _c ∈ V h, δ * w h := by
              rw [add_zero]
              exact Finset.sum_le_sum fun c _ => hstate h c
          _ = ((V h).card : ENNReal) * (δ * w h) := by
              rw [Finset.sum_const, nsmul_eq_mul]

end States

end

end Submission.Obl.k4_finite_affine_parent_sources
