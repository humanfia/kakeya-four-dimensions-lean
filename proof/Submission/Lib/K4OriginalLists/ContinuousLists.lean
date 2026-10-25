/-
Adapted from: here:o064
Written in this workspace by session x0217, from the supplied paper,
Lemma a03:actual-lists. No external formal code.
-/

import Submission.Lib.K4OriginalLists.FiniteLists

/-!
Original-law list recovery over an arbitrary measurable base.  All densities
remain unnormalized, and only the original observed record indexes the table.
This is the measure-theoretic part of the supplied paper's Lemma `a03:actual-lists`.
-/

namespace Submission.Lib.K4OriginalLists

open Finset MeasureTheory

variable {ι X β : Type*} [Fintype ι] [Fintype β] [MeasurableSpace X]

/-- The density of a list success event, summed over its finite output labels. -/
noncomputable def listDensity (p : X → β → ℝ) (L : X → Finset β) (x : X) : ℝ :=
  ∑ a ∈ L x, p x a

/-- Measurability of a rule is expressed only through its membership events. -/
def MeasurableLists (L : X → Finset β) : Prop :=
  ∀ a, MeasurableSet {x | a ∈ L x}

omit [Fintype ι] in
theorem integrable_listDensity (ν : Measure X) (p : X → β → ℝ) (L : X → Finset β)
    (hp : ∀ a, Integrable (fun x => p x a) ν) (hL : MeasurableLists L) :
    Integrable (listDensity p L) ν := by
  classical
  have h := integrable_finsetSum (univ : Finset β)
    (fun a _ => (hp a).indicator (hL a))
  convert h using 1
  funext x
  simp only [listDensity, Set.indicator_apply, Set.mem_ofPred_eq]
  calc
    ∑ a ∈ L x, p x a = ∑ a ∈ L x, (if a ∈ L x then p x a else 0) :=
      sum_congr rfl (fun a ha => by simp [ha])
    _ = ∑ a, (if a ∈ L x then p x a else 0) :=
      sum_subset (subset_univ _) (fun a _ ha => by simp [ha])

/-- Success mass with a continuous base and a finite observed record. -/
noncomputable def continuousListMass (ν : ι → Measure X) (p : ι → X → β → ℝ)
    (L : ι → X → Finset β) : ℝ :=
  ∑ c, ∫ x, listDensity (p c) (L c) x ∂ν c

theorem continuousListMass_mono (ν : ι → Measure X) (p q : ι → X → β → ℝ)
    (hp : ∀ c a, Integrable (fun x => p c x a) (ν c))
    (hq : ∀ c a, Integrable (fun x => q c x a) (ν c))
    (hpq : ∀ c x a, p c x a ≤ q c x a) (L : ι → X → Finset β)
    (hL : ∀ c, MeasurableLists (L c)) :
    continuousListMass ν p L ≤ continuousListMass ν q L := by
  classical
  apply sum_le_sum
  intro c _
  apply integral_mono (integrable_listDensity _ _ _ (hp c) (hL c))
    (integrable_listDensity _ _ _ (hq c) (hL c))
  intro x
  exact sum_le_sum fun a _ => hpq c x a

omit [Fintype ι] in
theorem abs_integral_listDensity_sub_le (ν : Measure X) (p q : X → β → ℝ)
    (hp : ∀ a, Integrable (fun x => p x a) ν)
    (hq : ∀ a, Integrable (fun x => q x a) ν)
    (L : X → Finset β) (hL : MeasurableLists L) :
    |(∫ x, listDensity p L x ∂ν) - ∫ x, listDensity q L x ∂ν| ≤
      ∫ x, ∑ a, |p x a - q x a| ∂ν := by
  classical
  have hpL := integrable_listDensity ν p L hp hL
  have hqL := integrable_listDensity ν q L hq hL
  have hdiff : Integrable (fun x => listDensity p L x - listDensity q L x) ν := hpL.sub hqL
  have herr : Integrable (fun x => ∑ a, |p x a - q x a|) ν :=
    integrable_finsetSum _ (fun a _ => ((hp a).sub (hq a)).abs)
  rw [← integral_sub hpL hqL]
  calc
    |∫ x, listDensity p L x - listDensity q L x ∂ν| ≤
        ∫ x, |listDensity p L x - listDensity q L x| ∂ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, ∑ a, |p x a - q x a| ∂ν := by
      apply integral_mono hdiff.abs herr
      intro x
      simp only [listDensity, ← sum_sub_distrib]
      exact (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => abs_nonneg _))

theorem abs_continuousListMass_sub_le (ν : ι → Measure X) (p q : ι → X → β → ℝ)
    (hp : ∀ c a, Integrable (fun x => p c x a) (ν c))
    (hq : ∀ c a, Integrable (fun x => q c x a) (ν c))
    (L : ι → X → Finset β) (hL : ∀ c, MeasurableLists (L c)) :
    |continuousListMass ν p L - continuousListMass ν q L| ≤
      ∑ c, ∫ x, ∑ a, |p c x a - q c x a| ∂ν c := by
  classical
  simp only [continuousListMass, ← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ =>
    abs_integral_listDensity_sub_le (ν c) (p c) (q c) (hp c) (hq c) (L c) (hL c))

/-- Continuous-base original-law list recovery, with the same list size and two error charges. -/
theorem recover_original_continuous_list (allowed : Finset β) (D : ℕ)
    (ν : ι → Measure X) (p mask : ι → X → β → ℝ)
    (ρ : ι → X → ℝ) (w : ι → β → ℝ)
    (hp : ∀ c a, Integrable (fun x => p c x a) (ν c))
    (hmaskint : ∀ c a, Integrable (fun x => mask c x a) (ν c))
    (hρint : ∀ c, Integrable (ρ c) (ν c))
    (hmask : ∀ c x a, mask c x a ≤ p c x a) (hρ : ∀ c x, 0 ≤ ρ c x)
    (e m : ℝ) (herror : (∑ c, ∫ x, ∑ a, |p c x a - ρ c x * w c a| ∂ν c) ≤ e)
    (L : ι → X → Finset β) (hLmeas : ∀ c, MeasurableLists (L c))
    (hL : ∀ c x, L c x ⊆ allowed ∧ (L c x).card ≤ D)
    (hsuccess : m ≤ continuousListMass ν mask L) :
    ∃ table : ι → Finset β,
      (∀ c, table c ⊆ allowed ∧ (table c).card ≤ D) ∧
      m - 2 * e ≤ continuousListMass ν p (fun c _ => table c) := by
  classical
  choose table hsub hcard hmax using fun c => exists_maximizing_list allowed D (w c)
  have htablemeas : ∀ c, MeasurableLists (fun _ : X => table c) := by
    intro c a
    by_cases ha : a ∈ table c <;> simp [ha]
  have havgint : ∀ c a, Integrable (fun x => ρ c x * w c a) (ν c) :=
    fun c a => (hρint c).mul_const _
  have hmaxavg : continuousListMass ν (fun c x a => ρ c x * w c a) L ≤
      continuousListMass ν (fun c x a => ρ c x * w c a) (fun c _ => table c) := by
    apply sum_le_sum
    intro c _
    apply integral_mono (integrable_listDensity _ _ _ (havgint c) (hLmeas c))
      (integrable_listDensity _ _ _ (havgint c) (htablemeas c))
    intro x
    simp only [listDensity, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (hmax c (L c x) (hL c x).1 (hL c x).2) (hρ c x)
  have hdom := continuousListMass_mono ν mask p hmaskint hp hmask L hLmeas
  have hfirst := (abs_le.mp ((abs_continuousListMass_sub_le ν p
    (fun c x a => ρ c x * w c a) hp havgint L hLmeas).trans herror)).2
  have hlast := (abs_le.mp ((abs_continuousListMass_sub_le ν p
    (fun c x a => ρ c x * w c a) hp havgint (fun c _ => table c) htablemeas).trans herror)).1
  exact ⟨table, fun c => ⟨hsub c, hcard c⟩, by linarith⟩

end Submission.Lib.K4OriginalLists
