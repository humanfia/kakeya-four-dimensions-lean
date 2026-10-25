-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.SourceGrid, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/SourceGrid.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

noncomputable section

namespace SourceGrid

/-- The grid may start arbitrarily shallow while retaining a specified
rational old depth. All choices precede the supplied original path. -/
theorem exists_grid_with_shallow_ancestor
    {κ₁ ρ gain u0 shallow tolerance : ℝ}
    (hκ : 0 < κ₁) (hρ : 0 < ρ) (hg : 0 < gain) (hg1 : gain  ≤  1/8)
    (hu : 0 < u0) (hu1 : u0  ≤  4*gain) (hshallow : 0 < shallow)
    (htolerance : 0 < tolerance) (Q : ℕ) (hQ : 2  ≤  Q) :
    ∃ (m : ℕ) (s : ℕ→ℝ) (δ₀ : ℝ),
      grid κ₁ ρ m s gain δ₀ u0 ∧ s 0  ≤  shallow ∧ δ₀  ≤  tolerance ∧ Q∣m ∧
      ∃ i, i < m ∧ s i = 1/(Q:ℝ) := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (lt_min hshallow (div_pos hg hκ))
  let m := 4*Q*(n+1)
  let s : ℕ→ℝ := fun i => ((i:ℝ)+1)/(m:ℝ)
  let δ₀ := min tolerance (min (gain/100) (min (u0/100) (ρ*gain/100)))
  have hQpos : 0 < Q := by omega
  have hnle : n+1  ≤  m := by
    simpa only [m,one_mul] using Nat.mul_le_mul_right (n+1)
      (show 1 ≤ 4*Q by omega)
  have hm : 0 < m := (Nat.succ_pos n).trans_le hnle
  have hm4 : 4  ≤  m := by
    have hh : 1 ≤ Q*(n+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    change 4 ≤ 4*Q*(n+1)
    nlinarith
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have hfirst : 1/(m:ℝ) ≤ min shallow (gain/κ₁) :=
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hnle)).trans hn.le
  have hδ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδtol : δ₀ ≤ tolerance := min_le_left _ _
  have hδg : δ₀ ≤ gain/100 := (min_le_right _ _).trans (min_le_left _ _)
  have hδu : δ₀ ≤ u0/100 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδρ : δ₀ ≤ ρ*gain/100 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have heven : Even m := ⟨2*Q*(n+1),by dsimp [m]; ring⟩
  have hlast : s (m-1)=1 := by
    have hc : ((m-1:ℕ):ℝ)+1=(m:ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_iff.mpr hm)
    dsimp [s]
    rw [hc,div_self hmR.ne']
  refine ⟨m,s,δ₀,?_,?_,hδtol,?_,?_⟩
  · unfold grid
    refine ⟨⟨hm,by dsimp [s]; positivity,?_,hlast⟩,hg,hg1,hδ,?_,heven,
      by omega,fun _ => rfl,?_,hδg,hδu,hδρ,hu,hu1⟩
    · intro i hi
      dsimp [s]
      exact (div_lt_div_iff_of_pos_right hmR).mpr (by push_cast; linarith)
    · nlinarith [mul_pos hρ hg]
    · exact hfirst.trans (min_le_right _ _)
  · simpa only [s,Nat.cast_zero,zero_add] using hfirst.trans (min_le_left _ _)
  · exact ⟨4*(n+1),by dsimp [m]; ring⟩
  · let j := 4*(n+1)
    have hj : 0 < j := by dsimp [j]; positivity
    have hmj : m=Q*j := by dsimp [m,j]; ring
    have hjm : j < m := by
      rw [hmj]
      exact (show j<2*j by omega).trans_le (Nat.mul_le_mul_right j hQ)
    refine ⟨j-1,by omega,?_⟩
    have hc : ((j-1:ℕ):ℝ)+1=(j:ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_iff.mpr hj)
    dsimp [s]
    rw [hc,hmj]
    push_cast
    field_simp

end SourceGrid

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
