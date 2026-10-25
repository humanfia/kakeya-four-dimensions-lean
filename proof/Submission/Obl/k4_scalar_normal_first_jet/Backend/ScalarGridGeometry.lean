/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGridGeometry.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGridGeometry.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-! Explicit scalar grid-index errors used in local collision cells. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem mesh_index_close {p C x y : ℝ} (hp : 0 < p) (hxy : |x - y| ≤ C * p) :
    |(⌊x / p⌋ : ℝ) - (⌊y / p⌋ : ℝ)| ≤ C + 1 := by
  have hdiv : |x / p - y / p| ≤ C := by
    rw [← sub_div, abs_div, abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr hxy
  have hxlo := Int.floor_le (x / p)
  have hxhi := Int.lt_floor_add_one (x / p)
  have hylo := Int.floor_le (y / p)
  have hyhi := Int.lt_floor_add_one (y / p)
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hdiv
  rw [abs_le]
  constructor <;> linarith

theorem mesh_lower_endpoint {p x : ℝ} (hp : 0 < p) {k : ℤ} (hk : ⌊x / p⌋ = k) :
    x ∈ Set.Icc (p * k) (p * k + p) ∧ |x - p * k| < p := by
  have hlo := Int.sub_floor_div_mul_nonneg x hp
  have hhi := Int.sub_floor_div_mul_lt x hp
  rw [hk] at hlo hhi
  constructor
  · constructor <;> nlinarith
  · rw [abs_of_nonneg (by nlinarith : 0 ≤ x - p * k)]
    nlinarith

theorem mesh_lower_endpoint_index {p : ℝ} (hp : 0 < p) (k : ℤ) :
    ⌊(p * k) / p⌋ = k := by
  rw [mul_div_cancel_left₀ (k : ℝ) hp.ne']
  exact Int.floor_intCast k

theorem same_mesh_cell_close {p x y : ℝ} (hp : 0 < p)
    (heq : ⌊x / p⌋ = ⌊y / p⌋) : |x - y| ≤ p := by
  have hx := (mesh_lower_endpoint hp (k := ⌊x / p⌋) rfl).1
  have hy := (mesh_lower_endpoint hp heq.symm).1
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The sign is selected on the finite tuple set. The active time sets
attached to its first indices need not be restricted at this step. -/
theorem exists_signed_half {ι : Type*} (T : Finset ι) (t : ι → ℝ) :
    ∃ (e : ℝ) (T' : Finset ι), |e| = 1 ∧ T' ⊆ T ∧
      (T.card : ℝ) / 2 ≤ (T'.card : ℝ) ∧ ∀ q ∈ T', 0 ≤ e * t q := by
  classical
  let Tp := T.filter (fun q => 0 ≤ t q)
  let Tm := T.filter (fun q => ¬0 ≤ t q)
  have hcard : Tp.card + Tm.card = T.card := Finset.card_filter_add_card_filter_not _
  by_cases hlarge : (T.card : ℝ) / 2 ≤ (Tp.card : ℝ)
  · refine ⟨1, Tp, by norm_num, Finset.filter_subset _ _, hlarge, ?_⟩
    intro q hq
    simpa only [one_mul] using (Finset.mem_filter.mp hq).2
  · refine ⟨-1, Tm, by norm_num, Finset.filter_subset _ _, ?_, ?_⟩
    · have hcardR : (Tp.card : ℝ) + (Tm.card : ℝ) = (T.card : ℝ) := by exact_mod_cast hcard
      linarith
    · intro q hq
      have hqneg := lt_of_not_ge (Finset.mem_filter.mp hq).2
      linarith

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
