-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.IntervalPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric MeasureTheory

/-- A finite metric set has a separated subfamily whose closed balls cover it. -/
lemma finite_separated_cover {X : Type*} [PseudoMetricSpace X] (S : Finset X) (r : ℝ)
    (hr : 0 ≤ r) : ∃ T : Finset X, T ⊆ S ∧
      (∀ a ∈ T, ∀ b ∈ T, a ≠ b → r < dist a b) ∧
      ∀ a ∈ S, ∃ b ∈ T, dist a b ≤ r := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨T, hTS, hsep, hcover⟩ := ih
    by_cases hnear : ∃ b ∈ T, dist a b ≤ r
    · refine ⟨T, hTS.trans (Finset.subset_insert _ _), hsep, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxS
      · subst x
        exact hnear
      · exact hcover x hxS
    · have hfar : ∀ b ∈ T, r < dist a b := by
        intro b hb
        exact lt_of_not_ge (fun hab => hnear ⟨b, hb, hab⟩)
      refine ⟨insert a T, Finset.insert_subset_insert _ hTS, ?_, ?_⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hxa | hxT
        · subst x
          rcases Finset.mem_insert.mp hy with hya | hyT
          · exact (hxy hya.symm).elim
          · exact hfar y hyT
        · rcases Finset.mem_insert.mp hy with hya | hyT
          · subst y
            simpa only [dist_comm] using hfar x hxT
          · exact hsep x hxT y hyT hxy
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxa | hxS
        · subst x
          exact ⟨a, Finset.mem_insert_self _ _, by simpa only [dist_self] using hr⟩
        · obtain ⟨b, hb, hxb⟩ := hcover x hxS
          exact ⟨b, Finset.mem_insert_of_mem hb, hxb⟩

/-- Uniform intervals inside a measured set turn its volume bound into a covering
bound for their base points. The set itself need not be measurable. -/
theorem cover_of_intervals_in_set {r ℓ c B : ℝ} (S : Finset ℝ) {D : Set ℝ}
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hB : 0 ≤ B)
    (hsub : ∀ a ∈ S, Ioo (a + c) (a + c + ℓ) ⊆ D)
    (hvol : volume D ≤ ENNReal.ofReal B) :
    ∃ (m : ℕ) (cc : Fin m → ℝ), (S : Set ℝ) ⊆ ⋃ j, closedBall (cc j) r ∧
      (m : ℝ) ≤ B / ℓ := by
  classical
  obtain ⟨T, hTS, hsep, hcover⟩ := finite_separated_cover S r (hℓ.le.trans hℓr)
  have hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      Disjoint (Ioo (a + c) (a + c + ℓ)) (Ioo (b + c) (b + c + ℓ)) := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hs := hsep a ha b hb hab
    change r < |a - b| at hs
    have : |a - b| < ℓ := abs_lt.mpr ⟨by linarith [hy.1, hx.2], by linarith [hx.1, hy.2]⟩
    linarith
  have hmass : ENNReal.ofReal ((T.card : ℝ) * ℓ) ≤ volume D := by
    have hu : (⋃ a ∈ T, Ioo (a + c) (a + c + ℓ)) ⊆ D := by
      intro x hx
      obtain ⟨a, haT, hxa⟩ := mem_iUnion₂.mp hx
      exact hsub a (hTS haT) hxa
    calc
      ENNReal.ofReal ((T.card : ℝ) * ℓ) = volume (⋃ a ∈ T, Ioo (a + c) (a + c + ℓ)) := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_Ioo)]
        simp only [Real.volume_Ioo, add_sub_cancel_left, Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ volume D := measure_mono hu
  have hcard : (T.card : ℝ) ≤ B / ℓ := by
    rw [le_div_iff₀ hℓ]
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp (hmass.trans hvol)
  refine ⟨T.card, fun j => ((Finset.equivFin T).symm j : ℝ), ?_, hcard⟩
  intro a ha
  obtain ⟨b, hb, hab⟩ := hcover a ha
  refine mem_iUnion.mpr ⟨Finset.equivFin T ⟨b, hb⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply, mem_closedBall] using hab

end WangZahlLot.Obl.wz_slab_local_linearity
