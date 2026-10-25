/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/HalfMassPruning.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/HalfMassPruning.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Subatlas
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory
open scoped Classical ENNReal

noncomputable section

/-- Keeping the entries which retain half their own mass costs at most twice
the aggregate loss, in addition to entries already declared ineligible. -/
theorem weighted_keep_half_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w before after lost : ι → ENNReal) (eligible : Finset ι)
    (hsplit : ∀ i, before i = after i + lost i)
    (hfinite : ∀ i, after i ≠ ⊤) :
    (∑ i, w i * before i) ≤
      (∑ i ∈ eligible.filter (fun i => before i ≤ 2 * after i), w i * after i) +
        2 * (∑ i, w i * lost i) + (∑ i ∈ Finset.univ \ eligible, w i * before i) := by
  classical
  have hterm (i : ι) : w i * before i ≤
      (if i ∈ eligible then if before i ≤ 2 * after i then w i * after i else 0 else 0) +
        2 * (w i * lost i) + (if i ∈ eligible then 0 else w i * before i) := by
    by_cases he : i ∈ eligible
    · simp only [he, ite_true, add_zero]
      by_cases hh : before i ≤ 2 * after i
      · simp only [hh, ite_true]
        rw [hsplit i, mul_add]
        exact add_le_add le_rfl (by rw [two_mul]; exact le_add_self)
      · simp only [hh, ite_false, zero_add]
        have h : after i + after i ≤ after i + lost i := by
          rw [← two_mul, ← hsplit i]
          exact (lt_of_not_ge hh).le
        have had : after i ≤ lost i := (ENNReal.add_le_add_iff_left (hfinite i)).mp h
        calc
          _ = w i * (after i + lost i) := by rw [hsplit i]
          _ ≤ w i * (lost i + lost i) := mul_le_mul' le_rfl (add_le_add had le_rfl)
          _ = _ := by ring
    · simp only [he, ite_false, zero_add]
      exact le_add_self
  have hkept : (∑ i, if i ∈ eligible then
      if before i ≤ 2 * after i then w i * after i else 0 else 0) =
      ∑ i ∈ eligible.filter (fun i => before i ≤ 2 * after i), w i * after i := by
    rw [Finset.sum_filter]
    exact Finset.sum_ite_mem_eq eligible _
  have hdeleted : (∑ i, if i ∈ eligible then 0 else w i * before i) =
      ∑ i ∈ Finset.univ \ eligible, w i * before i := by
    calc
      _ = ∑ i, if i ∈ Finset.univ \ eligible then w i * before i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases he : i ∈ eligible <;> simp [he]
      _ = _ := Finset.sum_ite_mem_eq _ _
  calc
    _ ≤ ∑ i, ((if i ∈ eligible then if before i ≤ 2 * after i then w i * after i else 0 else 0) +
        2 * (w i * lost i) + (if i ∈ eligible then 0 else w i * before i)) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hkept, hdeleted]

def Atlas.halfMassLabels {p : Data} {k : ℕ} (a : Atlas p k)
    (F : Fin a.C → Set Incidence) (eligible : Finset (Fin a.C)) : Finset (Fin a.C) :=
  eligible.filter (fun b => ((p.ν k (a.γ b)).prod volume) (a.F b) ≤
    2 * ((p.ν k (a.γ b)).prod volume) (F b))

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
