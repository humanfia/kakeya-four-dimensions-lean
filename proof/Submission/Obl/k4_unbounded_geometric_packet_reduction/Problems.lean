import Submission.Obl.k4_finite_width_output_exclusion.Horizon

/-!
The exact problems and terminal atlases are the accepted definitions of o153.
The maximizing-sequence argument below is adapted from this LOT tree, o120,
session x0402, `ExtremalSequence.lean` and `Problems.lean`, commit
`b6c9f0c78a897e02a6543f9fe1234d43a2ee16c7`.  In particular it bounds only
relative profiles; no bound on the absolute exponent at depth zero is used.
-/

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- A unit problem in the prescribed maximizing neighborhood. -/
def Near (ds kr S η t : ℝ) (p : Data) : Prop :=
  Valid p ∧ p.L = 1 ∧ p.S = S ∧ p.η = η ∧
    p.d < ds + t ∧ kr - t < Horizon p

/-- The bounded optimized width conclusion, with the data packaged. -/
def BoundedWidth (ds kr S η : ℝ) : Prop :=
  ∃ a w : ℝ, 0 < a ∧ 0 ≤ w ∧ ∀ t : ℝ, 0 < t →
    ∃ p : Data, Near ds kr S η t p ∧ ¬ Narrow p (kr + a) w

theorem Near.mono {ds kr S η t t' : ℝ} {p : Data}
    (hp : Near ds kr S η t p) (htt' : t ≤ t') : Near ds kr S η t' p := by
  obtain ⟨hp, hL, hS, hη, hd, hH⟩ := hp
  exact ⟨hp, hL, hS, hη, hd.trans_le (by linarith),
    lt_of_le_of_lt (by linarith) hH⟩

theorem not_boundedWidth_iff (ds kr S η : ℝ) :
    ¬ BoundedWidth ds kr S η ↔
      ∀ a : ℝ, 0 < a → ∀ w : ℝ, 0 ≤ w →
        ∃ t : ℝ, 0 < t ∧ ∀ p : Data,
          Near ds kr S η t p → Narrow p (kr + a) w := by
  classical
  constructor
  · intro hn a ha w hw
    by_contra h
    push Not at h
    exact hn ⟨a, w, ha, hw, h⟩
  · rintro h ⟨a, w, ha, hw, hn⟩
    obtain ⟨t, ht, hall⟩ := h a ha w hw
    obtain ⟨p, hp, hnot⟩ := hn t ht
    exact hnot (hall p hp)

theorem exists_near {ds kr S η : ℝ} (hes : Extremal ds kr S η)
    {t : ℝ} (ht : 0 < t) : ∃ p : Data, Near ds kr S η t p := by
  exact hes.2.2.2.2.1 t ht

theorem exists_narrow_near {ds kr S η : ℝ} (hes : Extremal ds kr S η)
    (hnb : ¬ BoundedWidth ds kr S η)
    {a w t : ℝ} (ha : 0 < a) (hw : 0 ≤ w) (ht : 0 < t) :
    ∃ p : Data, Near ds kr S η t p ∧ Narrow p (kr + a) w := by
  obtain ⟨t', ht', hall⟩ := (not_boundedWidth_iff _ _ _ _).1 hnb a ha w hw
  obtain ⟨p, hp⟩ := exists_near hes (lt_min ht ht')
  exact ⟨p, hp.mono (min_le_left _ _), hall p (hp.mono (min_le_right _ _))⟩

/-- The horizon, cap, and relative profile can all be prepared while retaining
any prescribed terminal narrowness. -/
theorem exists_prepared_near {ds kr S η : ℝ} (hes : Extremal ds kr S η)
    (hnb : ¬ BoundedWidth ds kr S η)
    {a w t : ℝ} (ha : 0 < a) (hw : 0 ≤ w) (ht : 0 < t) :
    ∃ p : Data, Near ds kr S η t p ∧ Narrow p (kr + a) w ∧
      |Horizon p - kr| ≤ t ∧ |p.d - ds| ≤ t ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → |p.f r - p.f 0 - ds * r| ≤ t := by
  obtain ⟨aH, haH, hH⟩ := hes.2.2.2.2.2.1 t ht
  obtain ⟨aP, haP, hP⟩ := hes.2.2.2.2.2.2 t ht
  obtain ⟨p, hp, hn⟩ := exists_narrow_near hes hnb ha hw
    (lt_min ht (lt_min haH haP))
  have hpt := hp.mono (min_le_left t (min aH aP))
  have hpH := hp.mono ((min_le_right t (min aH aP)).trans (min_le_left aH aP))
  have hpP := hp.mono ((min_le_right t (min aH aP)).trans (min_le_right aH aP))
  obtain ⟨hv, hL, hS, hη, hd, hh⟩ := hp
  have hu : Horizon p ≤ kr + t := by
    simpa only [hL, mul_one] using hH p hv hS hη hpH.2.2.2.2.1
  have hprofile : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      |p.f r - p.f 0 - ds * r| ≤ t := by
    intro r hr hr1
    have hb : (kr - aP) * p.L < Horizon p := by
      simpa only [hL, mul_one] using hpP.2.2.2.2.2
    simpa only [hL, mul_one] using
      hP p hv hS hη hpP.2.2.2.2.1 hb r hr (hL ▸ hr1)
  have hdim : |p.d - ds| ≤ t := by
    have hprof := hprofile 1 (by norm_num) le_rfl
    have hcap := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hc : p.f 1 - p.f 0 ≤ p.d := by
      have hx := hcap 0 le_rfl (by simpa only [hL] using (zero_le_one : (0 : ℝ) ≤ 1))
      simpa only [hL, sub_zero, mul_one] using hx
    rw [abs_le] at hprof ⊢
    constructor <;> linarith [hpt.2.2.2.2.1]
  refine ⟨p, hpt, hn, ?_, hdim, hprofile⟩
  rw [abs_le]
  constructor <;> linarith [hpt.2.2.2.2.2]

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
