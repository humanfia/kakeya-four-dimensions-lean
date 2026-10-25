import Submission.Obl.k4_true_forest_own_depth_preparation.CommonCut
import Submission.Obl.k4_true_forest_own_depth_preparation.Numerics
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

/-! Analytically trimming full earlier witnesses, with the original mass budget. -/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set Classical
open Submission.Obl.k4_true_forest_own_depth_preparation

noncomputable section

/-- A witness keeps at least half its original mass after a common-world cutoff. -/
def activeWitness {X ι β : Type*} [MeasurableSpace X]
    (μ : β → Measure X) (γ : ι → β) (F : ι → Set X) (Good : β → Set X) (e : ι) : Prop :=
  μ (γ e) (F e) ≤ 2 * μ (γ e) (F e ∩ Good (γ e))

/-- Retain the common good event and exclude every inactive earlier witness. -/
def witnessKeep {X ι β : Type*} [MeasurableSpace X]
    (μ : β → Measure X) (γ : ι → β) (F : ι → Set X) (Good : β → Set X) (w : β) : Set X :=
  Good w ∩ commonGood γ F (fun e => if activeWitness μ γ F Good e then F e else ∅) w

theorem measurableSet_witnessKeep {X ι β : Type*} [MeasurableSpace X] [Finite ι]
    (μ : β → Measure X) (γ : ι → β) (F : ι → Set X) (Good : β → Set X)
    (hF : ∀ e, MeasurableSet (F e)) (hGood : ∀ w, MeasurableSet (Good w)) (w : β) :
    MeasurableSet (witnessKeep μ γ F Good w) := by
  classical
  apply (hGood w).inter
  apply measurableSet_commonGood γ F _ hF
  intro e
  split_ifs
  · exact hF e
  · exact MeasurableSet.empty

/-- Membership retains the full analytically trimmed witness, with its half-mass floor. -/
theorem witnessKeep_active {X ι β : Type*} [MeasurableSpace X]
    (μ : β → Measure X) (γ : ι → β) (F : ι → Set X) (Good : β → Set X)
    {e : ι} {x : X} (hx : x ∈ witnessKeep μ γ F Good (γ e)) (hF : x ∈ F e) :
    activeWitness μ γ F Good e ∧ x ∈ F e ∩ Good (γ e) := by
  classical
  have hh := hx.2 e rfl hF
  by_cases he : activeWitness μ γ F Good e
  · exact ⟨he, hF, hx.1⟩
  · simp [he] at hh

/-- Deleting witnesses whose good part is below half their original mass costs
at most twice the mass already removed from those full witnesses. -/
theorem inactive_witness_mass_le {X ι β : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : β → Measure X) (ω : β → ENNReal) (γ : ι → β)
    (F : ι → Set X) (Good : β → Set X)
    (hfin : ∀ e, μ (γ e) (F e) ≠ ⊤) :
    (∑ e, if ¬ activeWitness μ γ F Good e then ω (γ e) * μ (γ e) (F e) else 0) ≤
      2 * ∑ e, ω (γ e) * μ (γ e) (F e \ Good (γ e)) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  by_cases ha : activeWitness μ γ F Good e
  · simp only [ha, not_true_eq_false, ite_eq_right]
    exact zero_le
  · rw [ite_eq_left ha]
    have hGfin : μ (γ e) (F e ∩ Good (γ e)) ≠ ⊤ :=
      ne_top_of_le_ne_top (hfin e) (measure_mono inter_subset_left)
    have hm := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.le_two_mul_inter_of_diff_le
      (μ (γ e)) (P := F e) (X := (Good (γ e))ᶜ) hGfin
      (by simpa only [sdiff_compl] using (le_rfl :
        μ (γ e) (F e ∩ Good (γ e)) ≤ μ (γ e) (F e ∩ Good (γ e))))
      (lt_of_not_ge ha).le
    have hm' : μ (γ e) (F e) ≤ 2 * μ (γ e) (F e \ Good (γ e)) := by
      simpa only [sdiff_eq] using hm
    calc _ ≤ ω (γ e) * (2 * μ (γ e) (F e \ Good (γ e))) := mul_le_mul' le_rfl hm'
      _ = _ := by ring

/-- A common-world analytical deletion and the removal of light earlier witnesses
have total original weighted cost at most five times the original exceptional mass. -/
theorem witnessKeep_loss_le {X ι β : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype β] [DecidableEq β]
    (μ : β → Measure X) (ω : β → ENNReal) (γ : ι → β)
    (F : ι → Set X) (Good : β → Set X)
    (hF : ∀ e, MeasurableSet (F e)) (hGood : ∀ w, MeasurableSet (Good w))
    (hfin : ∀ e, μ (γ e) (F e) ≠ ⊤)
    (hmult : ∀ w x, (∑ e ∈ Finset.univ.filter (fun e => γ e = w),
      (F e).indicator (1 : X → ENNReal) x) ≤ 2) :
    (∑ w, ω w * μ w (witnessKeep μ γ F Good w)ᶜ) ≤
      5 * ∑ w, ω w * μ w (Good w)ᶜ := by
  classical
  let H := fun e => if activeWitness μ γ F Good e then F e else ∅
  have hcommon := commonGood_loss_le μ ω γ F H
  have hsplit : (∑ e, ω (γ e) * μ (γ e) (F e \ H e)) =
      ∑ e, if ¬ activeWitness μ γ F Good e then ω (γ e) * μ (γ e) (F e) else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    by_cases ha : activeWitness μ γ F Good e <;> simp [H, ha]
  rw [hsplit] at hcommon
  have hinactive := inactive_witness_mass_le μ ω γ F Good hfin
  have htrim := weighted_common_cut_loss μ ω γ F Good hF hGood hmult
  have htotal := hcommon.trans (hinactive.trans (mul_le_mul' le_rfl htrim))
  calc
    _ ≤ ∑ w, (ω w * μ w (Good w)ᶜ + ω w * μ w (commonGood γ F H w)ᶜ) := by
      apply Finset.sum_le_sum
      intro w hw
      dsimp only [witnessKeep]
      rw [compl_inter, ← mul_add]
      exact mul_le_mul' le_rfl (measure_union_le _ _)
    _ = (∑ w, ω w * μ w (Good w)ᶜ) + ∑ w, ω w * μ w (commonGood γ F H w)ᶜ :=
      Finset.sum_add_distrib
    _ ≤ (∑ w, ω w * μ w (Good w)ᶜ) +
        2 * (2 * ∑ w, ω w * μ w (Good w)ᶜ) := add_le_add le_rfl htotal
    _ = _ := by ring

end
end Submission.Obl.k4_raw_localized_native_systems.Window
