import Submission.WZ.Obl.wz_slab_local_linearity.Covering

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set Metric
open WangZahlLot.Obl.wz_slab_local_linearity

/-- A finite scalar-bin list gives an indexed closed-ball cover with the
same cardinality, in the exact format used by `IntervalAD`. -/
theorem scalar_cover_of_bin_list {S : Set ℝ} {r : ℝ} (hr : 0 < r)
    (L : Finset ℤ) (hL : ∀ x ∈ S, ⌊x / r⌋ ∈ L) :
    ∃ (m : ℕ) (c : Fin m → ℝ), S ⊆ ⋃ j, closedBall (c j) r ∧ m = L.card := by
  classical
  let e := Fintype.equivFin L
  refine ⟨Fintype.card L, fun j => ((e.symm j).val : ℝ) * r, ?_, by simp⟩
  intro x hx
  let j : L := ⟨⌊x / r⌋, hL x hx⟩
  apply mem_iUnion.mpr
  refine ⟨e j, ?_⟩
  simp only [Equiv.symm_apply_apply, mem_closedBall, Real.dist_eq]
  change |x - (⌊x / r⌋ : ℝ) * r| ≤ r
  have hlo := (le_div_iff₀ hr).mp (Int.floor_le (x / r))
  have hhi := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (x / r))
  apply abs_le.mpr
  constructor <;> linarith

theorem intervalAD_of_bin_lists {ζ d K : ℝ} (hζ : 0 < ζ) (S : Set ℝ)
    (hlist : ∀ r R a : ℝ, ζ ≤ r → r ≤ R →
      ∃ L : Finset ℤ, (L.card : ℝ) ≤ K * (R / r) ^ d ∧
        ∀ x ∈ S ∩ Icc a (a + R), ⌊x / r⌋ ∈ L) :
    IntervalAD ζ d K S := by
  intro r R a hr hR
  obtain ⟨L, hcard, hmem⟩ := hlist r R a hr hR
  obtain ⟨m, c, hcover, hm⟩ := scalar_cover_of_bin_list (hζ.trans_le hr) L hmem
  exact ⟨m, c, hcover, by simpa only [hm] using hcard⟩

end Submission.Obl.k4_scalar_grid_polynomial_qualification
