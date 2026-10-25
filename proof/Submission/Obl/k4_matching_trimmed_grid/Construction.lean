import Submission.Obl.k4_matching_trimmed_grid.Refinement

noncomputable section

namespace Submission.Obl.k4_matching_trimmed_grid

open Set
open scoped BigOperators

def Admissible (J : ℕ) (β : ℕ → ℝ) (q : ℕ) (A : Finset ℕ)
    (m z : ℕ → ℕ) (γ : ℝ) : Prop :=
  A ⊆ Finset.range q ∧ ∀ k ∈ A,
    k + 6 * (J + 1) ≤ q ∧ 1 ≤ m k ∧ m k ≤ J ∧ β (m k) < 2 ∧
    z (m k) ≤ k ∧ γ ≤ (z (m k) : ℝ) / q ∧
    ∀ x ∈ Icc ((z (m k) : ℝ) / q) (((k + 6 * (J + 1) : ℕ) : ℝ) / q),
      radius J β x = line β (m k) x ∧
      (∀ j, 1 ≤ j → j ≤ J → j ≠ m k → line β j x < radius J β x) ∧
      (∀ j, j ≤ J → γ ≤ ((J : ℝ) + 1 - j) * radius J β x - accuracy J β j x) ∧
      (∀ i, 1 ≤ i → m k + i ≤ J →
        γ ≤ accuracy J β (m k + i) x + (i : ℝ) * radius J β x - β (m k))

lemma refine_admissible {J n t d : ℕ} {β : ℕ → ℝ} {S : Finset ℕ} {m z : ℕ → ℕ}
    (hJ : 1 ≤ J) (hn : 1 ≤ n) (ht : 1 ≤ t) (hCt : 6 * (J + 1) ≤ t)
    (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0)
    (hS : S ⊆ Finset.range n) (hpos : ∀ s ∈ S, 1 ≤ s)
    (hactive : ∀ s ∈ S, ∀ x ∈ Icc (((s : ℝ) - 1) / n) (((s : ℝ) + 1) / n),
      Active J β (m s) x)
    (href : ∀ s ∈ S, z (m s) ∈ S ∧ m (z (m s)) = m s ∧ z (m s) ≤ s) :
    Admissible J β (n * t) (fineCells S t (6 * (J + 1)))
      (fun k => m (k / t)) (fun j => z j * t) (margin n J) := by
  classical
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htp : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hn0 := ne_of_gt hnp
  have ht0 := ne_of_gt htp
  refine ⟨fineCells_subset hS ht, ?_⟩
  intro k hk
  obtain ⟨s, hs, hks⟩ := Finset.mem_biUnion.mp hk
  have hdiv := fineBlock_div ht hks
  dsimp only
  rw [hdiv]
  let a := z (m s)
  have haS : a ∈ S := (href s hs).1
  have hams : m a = m s := (href s hs).2.1
  have has : a ≤ s := (href s hs).2.2
  have ha1 : 1 ≤ a := hpos a haS
  have ha1r : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hs1r : (1 : ℝ) ≤ s := by exact_mod_cast hpos s hs
  have hsn : s + 1 ≤ n := by have := Finset.mem_range.mp (hS hs); omega
  have hend : k + 6 * (J + 1) ≤ (s + 1) * t := fineBlock_end hCt hks
  have hq : k + 6 * (J + 1) ≤ n * t := hend.trans (Nat.mul_le_mul_right t hsn)
  have hsk : s * t ≤ k := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hks
    omega
  have haz : a * t ≤ k := (Nat.mul_le_mul_right t has).trans hsk
  have hzratio : ((a * t : ℕ) : ℝ) / ((n * t : ℕ) : ℝ) = (a : ℝ) / n := by
    push_cast
    field_simp
  have hay0 : 0 ≤ ((a : ℝ) - 1) / n := div_nonneg (by linarith) hnp.le
  have hleft : Active J β (m s) (((a : ℝ) - 1) / n) := by
    have h := hactive a haS (((a : ℝ) - 1) / n)
      ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hnp.le⟩
    simpa only [hams] using h
  have hright : Active J β (m s) (((s : ℝ) + 1) / n) :=
    hactive s hs _ ⟨div_le_div_of_nonneg_right (by linarith) hnp.le, le_rfl⟩
  have hcenter : Active J β (m s) ((s : ℝ) / n) := hactive s hs _
    ⟨div_le_div_of_nonneg_right (by linarith) hnp.le,
      div_le_div_of_nonneg_right (by linarith) hnp.le⟩
  have hcenter0 : 0 < (s : ℝ) / n := div_pos (by linarith) hnp
  have hcenter1 : (s : ℝ) / n ≤ 1 := by
    apply (div_le_one hnp).2
    exact_mod_cast (by omega : s ≤ n)
  have hbeta := beta_lt_two_of_active hd hdJ hz hcenter0 hcenter1 hcenter
  refine ⟨hq, hcenter.1, hcenter.2.1, hbeta, haz, ?_, ?_⟩
  · rw [hzratio]
    exact (margin_le_step hn hJ).trans (div_le_div_of_nonneg_right ha1r hnp.le)
  · intro x hx
    change x ∈ Icc (((a * t : ℕ) : ℝ) / ((n * t : ℕ) : ℝ))
      (((k + 6 * (J + 1) : ℕ) : ℝ) / ((n * t : ℕ) : ℝ)) at hx
    rw [hzratio] at hx
    have hendr : (((k + 6 * (J + 1) : ℕ) : ℝ) / ((n * t : ℕ) : ℝ)) ≤
        ((s : ℝ) + 1) / n := by
      calc
        _ ≤ (((s + 1) * t : ℕ) : ℝ) / ((n * t : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hend) (by positivity)
        _ = _ := by push_cast; field_simp
    have hxright : x ≤ ((s : ℝ) + 1) / n := hx.2.trans hendr
    have hxleft : ((a : ℝ) - 1) / n ≤ x :=
      (div_le_div_of_nonneg_right (by linarith) hnp.le).trans hx.1
    have hax := hleft.between hright ⟨hxleft, hxright⟩
    have hxstep : 1 / (n : ℝ) ≤ x - ((a : ℝ) - 1) / n := by
      have he : (a : ℝ) / n - ((a : ℝ) - 1) / n = 1 / (n : ℝ) := by ring
      linarith [hx.1]
    have hxpos : 1 / (n : ℝ) ≤ x :=
      (div_le_div_of_nonneg_right ha1r hnp.le).trans hx.1
    refine ⟨hax.radius_eq, ?_, ?_, ?_⟩
    · intro j hj hjJ hjm
      rw [hax.radius_eq]
      exact hax.2.2 j hj hjJ hjm
    · intro j hj
      exact remainder_gap hn hJ hd hdJ hz hxpos hj
    · intro i hi hiJ
      exact higher_gap hn hJ hd hdJ hz hay0 hxstep hleft hax hi

lemma exists_trimmed_grid {J : ℕ} {β : ℕ → ℝ} (hJ : 1 ≤ J)
    (hβ : ∀ j, 1 ≤ j → j ≤ J → 0 ≤ β j)
    (hz : ∃ d, 1 ≤ d ∧ d ≤ J ∧ β d = 0) :
    ∀ δ : ℝ, 0 < δ → ∃ γ : ℝ, 0 < γ ∧ ∀ Q : ℕ,
      ∃ q : ℕ, Q ≤ q ∧ 1 ≤ q ∧ ∃ (A : Finset ℕ) (m z : ℕ → ℕ),
        Admissible J β q A m z γ ∧
        1 + radius J β 1 - δ ≤ ∑ k ∈ A, (1 + 1 / (m k : ℝ)) / q := by
  classical
  intro δ hδ
  let B : ℕ := 1 + 6 * (crossings J β).card
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) (4 * (B : ℝ) / δ))
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
    exact_mod_cast this.le
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnloss : 2 * (B : ℝ) / n ≤ δ / 2 := by
    have hlt : 4 * (B : ℝ) / δ < n := (le_max_right _ _).trans_lt hn
    have hlt' := (div_lt_iff₀ hδ).1 hlt
    apply (div_le_iff₀ hnp).2
    nlinarith
  let S := goodCells n (crossings J β)
  have hS : S ⊆ Finset.range n := goodCells_subset _ _
  have hpos : ∀ s ∈ S, 1 ≤ s := fun _ hs => goodCells_pos hs
  have hex : ∀ s : ℕ, ∃ m : ℕ, s ∈ S →
      ∀ x ∈ Icc (((s : ℝ) - 1) / n) (((s : ℝ) + 1) / n), Active J β m x := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨m, hm⟩ := goodCells_active hJ hn1 hs
      exact ⟨m, fun _ => hm⟩
    · exact ⟨1, fun h => (hs h).elim⟩
  choose m hm using hex
  obtain ⟨z, href⟩ := reference_indices S m
  have hzero := radius_zero hJ hβ hz
  have hcoverage := coarse_coverage hJ hn1 hzero m hm
  have hcoarse : 1 + radius J β 1 - δ / 2 ≤
      ∑ s ∈ S, (1 + 1 / (m s : ℝ)) / n := by
    change 1 + radius J β 1 - 2 * (B : ℝ) / n ≤ _ at hcoverage
    linarith
  refine ⟨margin n J, margin_pos hn1 hJ, ?_⟩
  intro Q
  let C : ℕ := 6 * (J + 1)
  obtain ⟨t, ht⟩ := exists_nat_gt (max (max (Q : ℝ) ((C : ℝ) + 1)) (4 * (C : ℝ) / δ))
  have hCt : C ≤ t := by
    have : (C : ℝ) + 1 < t := (le_trans (le_max_right _ _) (le_max_left _ _)).trans_lt ht
    exact_mod_cast (by linarith : (C : ℝ) ≤ t)
  have ht1 : 1 ≤ t := by
    have hC1 : 1 ≤ C := by dsimp [C]; omega
    exact hC1.trans hCt
  have htp : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hQt : Q ≤ t := by
    have : (Q : ℝ) < t := (le_trans (le_max_left _ _) (le_max_left _ _)).trans_lt ht
    exact_mod_cast this.le
  have htloss : 2 * (C : ℝ) / t ≤ δ / 2 := by
    have hlt : 4 * (C : ℝ) / δ < t := (le_max_right _ _).trans_lt ht
    have hlt' := (div_lt_iff₀ hδ).1 hlt
    apply (div_le_iff₀ htp).2
    nlinarith
  have htq : t ≤ n * t := by nlinarith
  refine ⟨n * t, hQt.trans htq, by nlinarith, fineCells S t C,
    (fun k => m (k / t)), (fun j => z j * t), ?_, ?_⟩
  · obtain ⟨d, hd, hdJ, hdz⟩ := hz
    exact refine_admissible hJ hn1 ht1 hCt hd hdJ hdz hS hpos hm href
  · have hmpos : ∀ s ∈ S, 1 ≤ m s := by
      intro s hs
      exact (hm s hs ((s : ℝ) / n)
        ⟨div_le_div_of_nonneg_right (by linarith) hnp.le,
          div_le_div_of_nonneg_right (by linarith) hnp.le⟩).1
    have hfin := refinement_coverage hn1 ht1 hCt hS hmpos
    dsimp only at hfin ⊢
    linarith

end Submission.Obl.k4_matching_trimmed_grid
