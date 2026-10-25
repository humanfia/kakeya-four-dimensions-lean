-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.Covering.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric

/-- A lower bound on the number of closed balls in every finite cover. -/
def CoverLower {X : Type*} [PseudoMetricSpace X] (S : Set X) (r N : ℝ) : Prop :=
  ∀ (m : ℕ) (c : Fin m → X), S ⊆ ⋃ j, closedBall (c j) r → N ≤ (m : ℝ)

/-- The interval covering condition in the statement of the slab lemma. -/
def IntervalAD (d α C : ℝ) (S : Set ℝ) : Prop :=
  ∀ r R a : ℝ, d ≤ r → r ≤ R → ∃ (m : ℕ) (c : Fin m → ℝ),
    S ∩ Icc a (a + R) ⊆ ⋃ j, closedBall (c j) r ∧
      (m : ℝ) ≤ C * (R / r) ^ α

lemma CoverLower.mono {X : Type*} [PseudoMetricSpace X] {S T : Set X} {r N : ℝ}
    (h : CoverLower S r N) (hST : S ⊆ T) : CoverLower T r N :=
  fun m c hc => h m c (hST.trans hc)

lemma CoverLower.le_one_of_subset_closedBall {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {r N : ℝ} (h : CoverLower S r N) {x : X}
    (hS : S ⊆ closedBall x r) : N ≤ 1 := by
  have ht := h 1 (fun _ => x) (fun y hy => mem_iUnion.mpr ⟨0, hS hy⟩)
  simpa using ht

lemma IntervalAD.mono {d α C : ℝ} {S T : Set ℝ}
    (h : IntervalAD d α C S) (hTS : T ⊆ S) : IntervalAD d α C T := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R a hdr hrR
  exact ⟨m, c, (inter_subset_inter_left _ hTS).trans hc, hm⟩

/-- On an interval, an AD upper bound conflicts with a larger covering lower bound. -/
lemma IntervalAD.not_coverLower {d α C r L a β : ℝ} {S : Set ℝ}
    (h : IntervalAD d α C S) (hdr : d ≤ r) (hrL : r ≤ L)
    (hgap : C * (L / r) ^ α < (L / r) ^ β) :
    ¬ CoverLower (Icc a (a + L) ∩ S) r ((L / r) ^ β) := by
  intro hlower
  obtain ⟨m, c, hc, hm⟩ := h r L a hdr hrL
  have hlo := hlower m c (by simpa only [inter_comm] using hc)
  exact (not_lt_of_ge (hlo.trans hm)) hgap

/-- The exponent gap rules out the expanding alternative of the projection dichotomy. -/
lemma IntervalAD.no_expansion {d α C r L a β M : ℝ} {S : Set ℝ}
    (h : IntervalAD d α C S) (hdr : d ≤ r) (hr : 0 < r)
    (hM : 1 ≤ M) (hML : M * r ≤ L) (hαβ : α ≤ β)
    (hC : C < M ^ (β - α)) :
    ¬ CoverLower (Icc a (a + L) ∩ S) r ((L / r) ^ β) := by
  have hMx : M ≤ L / r := (le_div_iff₀ hr).2 hML
  have hx : 0 < L / r := lt_of_lt_of_le zero_lt_one (hM.trans hMx)
  apply h.not_coverLower hdr (by nlinarith)
  calc
    C * (L / r) ^ α < M ^ (β - α) * (L / r) ^ α :=
      mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hx _)
    _ ≤ (L / r) ^ (β - α) * (L / r) ^ α :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by linarith) hMx (sub_nonneg.mpr hαβ))
        (Real.rpow_nonneg hx.le _)
    _ = (L / r) ^ β := by rw [← Real.rpow_add hx]; congr 1; ring

end WangZahlLot.Obl.wz_slab_local_linearity
