-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PrismPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismCount

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- A prism meeting a thin slab in the unit ball lies in a common rectangular
container. The bound is independent of the two longer prism side lengths. -/
theorem prism_enclosure_of_meeting_slab {a b c w t : ℝ} {z : V}
    (e : V ≃ₗᵢ[ℝ] V) (hb : b ≤ 1) (hc : c ≤ 1)
    (hmeet : (P a b c z e ∩ (ball 0 1 ∩ {p | |e p 0 - t| ≤ w})).Nonempty) :
    P a b c z e ⊆ P (2 * (w + a)) 4 4 (e.symm (EuclideanSpace.single 0 t)) e := by
  obtain ⟨q, hqP, hqball, hqslab⟩ := hmeet
  intro p hp
  change |e q 0 - t| ≤ w at hqslab
  have hqnorm : ‖q‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hqball
  have hcoord (i : Fin 3) : |e q i| ≤ 1 := (abs_rotated_coord_le e q i).trans hqnorm.le
  have he (i : Fin 3) : e (p - z) i - e (q - z) i + e q i = e p i := by
    simp only [map_sub]
    change (e p i - e z i) - (e q i - e z i) + e q i = e p i
    ring
  have h0 : |e p 0 - t| ≤ w + a := by
    rw [← he 0]
    calc
      |e (p - z) 0 - e (q - z) 0 + e q 0 - t| =
          |(e (p - z) 0 - e (q - z) 0) + (e q 0 - t)| := by ring_nf
      _ ≤ |e (p - z) 0 - e (q - z) 0| + |e q 0 - t| := abs_add_le _ _
      _ ≤ (|e (p - z) 0| + |e (q - z) 0|) + |e q 0 - t| := by
        exact add_le_add (abs_sub _ _) le_rfl
      _ ≤ w + a := by
        have hp0 : |e (p - z) 0| ≤ a / 2 := hp.1
        have hq0 : |e (q - z) 0| ≤ a / 2 := hqP.1
        linarith only [hp0, hq0, hqslab]
  have hshort (i : Fin 3) (s : ℝ) (hs : s ≤ 1)
      (hp' : |e (p - z) i| ≤ s / 2) (hq' : |e (q - z) i| ≤ s / 2) :
      |e p i| ≤ 2 := by
    rw [← he i]
    have hsum := abs_add_le (e (p - z) i - e (q - z) i) (e q i)
    have hdiff := abs_sub (e (p - z) i) (e (q - z) i)
    linarith [hcoord i]
  have h1 := hshort 1 b hb hp.2.1 hqP.2.1
  have h2 := hshort 2 c hc hp.2.2 hqP.2.2
  change |e (p - e.symm (EuclideanSpace.single 0 t)) 0| ≤ 2 * (w + a) / 2 ∧
    |e (p - e.symm (EuclideanSpace.single 0 t)) 1| ≤ 4 / 2 ∧
    |e (p - e.symm (EuclideanSpace.single 0 t)) 2| ≤ 4 / 2
  norm_num [map_sub]
  exact ⟨h0, h1, h2⟩

/-- Disjoint prisms meeting one width-w slab in the unit ball have total
volume at most 32(w+a). This gives the average grain-density denominator. -/
theorem prism_packing_in_slab {a b c w t : ℝ} {L : ℕ}
    (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hw : 0 ≤ w)
    (hb : b ≤ 1) (hc : c ≤ 1) (e : V ≃ₗᵢ[ℝ] V) (z : Fin L → V)
    (hdisj : Pairwise (fun i j => Disjoint (P a b c (z i) e) (P a b c (z j) e)))
    (hmeet : ∀ j, (P a b c (z j) e ∩ (ball 0 1 ∩ {p | |e p 0 - t| ≤ w})).Nonempty) :
    o ((L : ℝ) * (a * b * c)) ≤ o (32 * (w + a)) := by
  let W := P (2 * (w + a)) 4 4 (e.symm (EuclideanSpace.single 0 t)) e
  have hsub (j : Fin L) : P a b c (z j) e ⊆ W :=
    prism_enclosure_of_meeting_slab e hb hc (hmeet j)
  have hcount := prism_count_of_disjoint ha hb0 hc0 z (fun _ => e) Finset.univ
    (fun i _ j _ hij => hdisj hij) W
  have hset : {j | j ∈ (Finset.univ : Finset (Fin L)) ∧ P a b c (z j) e ⊆ W} = univ := by
    ext j
    simp only [Finset.mem_univ, true_and, mem_setOf_eq, mem_univ, iff_true]
    exact hsub j
  rw [hset] at hcount
  have hq : q (univ : Set (Fin L)) = (L : ℝ) := by simp [q]
  rw [hq] at hcount
  have hvol : μ W = o (32 * (w + a)) := by
    have hvol0 : μ W = o ((2 * (w + a)) * 4 * 4) :=
      Factor.box_volume (by positivity) (by norm_num) (by norm_num)
        (e.symm (EuclideanSpace.single 0 t)) e
    rw [hvol0]
    congr 1
    ring
  exact hcount.trans_eq hvol

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
