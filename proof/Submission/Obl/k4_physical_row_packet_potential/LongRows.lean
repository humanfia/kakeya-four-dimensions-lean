-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/LongRows.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
import Submission.Obl.k4_physical_row_packet_potential.PotentialFits

namespace Submission.Obl.k4_physical_row_packet_potential

open Set MeasureTheory MvPolynomial

noncomputable section

namespace PotentialFits

/-- Qualification on a positive-duration set of original block times
extends to the full old block. The accepted Remez lemma is applied before
integrating the field to an own-intercept potential. -/
theorem whole_block_row_of_long_times (Tfield : Row) (D : ℕ)
    (hdegree : ∀ i, (Tfield i).totalDegree ≤ D)
    (T j : ℕ) (c u : P2) (P : Po) (hP : P.totalDegree ≤ 2) (l : Ln)
    (R : Set ℝ) {η err : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (herr : 0 ≤ err)
    (hR : R ⊆ Icc (0 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume R)
    (hfit : ∀ s ∈ R,
      |ParentSignal.rate P l (start T j + clock T * s) - ∑ i : Fin 3,
        direction l i * eval (fun i => packetBase T j c u (l, start T j + clock T * s) i)
          (Tfield i)| ≤ err) :
    ∀ t ∈ Icc (start T j) (start T j + clock T),
      |ParentSignal.rate P l t - ∑ i : Fin 3,
        direction l i * eval (fun i => packetBase T j c u (l, t) i) (Tfield i)| ≤
        (8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err := by
  let base : Fin 3 → ℝ := fun i => packetBase T j c u (l, start T j) i
  let b : ℝ := Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
    2 * start T j * Submission.Lib.K4ProjectedGroups.sc2 P l.2
  let d : ℝ := clock T * Submission.Lib.K4ProjectedGroups.sc2 P l.2
  have hrate (s : ℝ) : ParentSignal.rate P l (start T j + clock T * s) = b + 2 * s * d := by
    rw [ParentSignal.rate_eq_coefficients hP]
    dsimp [b, d]
    ring
  have hfit' : ∀ s ∈ R,
      |b + 2 * s * d - ∑ i : Fin 3,
        direction l i * eval (base + s • direction l) (Tfield i)| ≤ err := by
    intro s hs
    have h := hfit s hs
    rw [hrate, packetBase_normalized] at h
    exact h
  have hfull := Submission.Lib.K4PolynomialNorming.quadratic_line_field_fit_on_whole_block
    Tfield D hdegree base (direction l) b d R η err hη hη1 herr hR hmass hfit'
  intro t ht
  let s : ℝ := (t - start T j) / clock T
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) (clock_pos T).le
    · apply (div_le_one (clock_pos T)).mpr
      linarith [ht.2]
  have htime : start T j + clock T * s = t := by
    dsimp [s]
    field_simp [ne_of_gt (clock_pos T)]
    <;> ring
  have h := hfull s hs
  rw [← hrate, ← packetBase_normalized T j c u l s, htime] at h
  exact h

end PotentialFits

end

end Submission.Obl.k4_physical_row_packet_potential
