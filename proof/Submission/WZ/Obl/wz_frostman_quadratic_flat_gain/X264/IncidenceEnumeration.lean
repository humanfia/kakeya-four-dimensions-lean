-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.IncidenceEnumeration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file IncidenceEnumeration.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set

/-- Enumerate tube-prism incidences, repeating a tube once for each prism that
contains it. This preserves both the physical union and incidence-weighted sums. -/
lemma incidence_enumeration {n p : ℕ} (hn : 0 < n) (F : Fin p → Finset (Fin n))
    (hcover : ∀ i, ∃ j, i ∈ F j) :
    ∃ N : ℕ, 0 < N ∧ ∃ g : Fin N → Fin n, Function.Surjective g ∧
      N = ∑ j, (F j).card ∧
      (∀ w : Fin n → ENNReal, ∑ a, w (g a) = ∑ j, ∑ i ∈ F j, w i) ∧
      ∀ Y : Fin n → Set Space, (⋃ a, Y (g a)) = ⋃ i, Y i := by
  classical
  let I := (j : Fin p) × {i : Fin n // i ∈ F j}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let g := fun a => (e a).2.val
  have hN : 0 < Fintype.card I := by
    obtain ⟨j, hj⟩ := hcover ⟨0, hn⟩
    exact Fintype.card_pos_iff.mpr ⟨⟨j, ⟨⟨0, hn⟩, hj⟩⟩⟩
  have hg : Function.Surjective g := by
    intro i
    obtain ⟨j, hj⟩ := hcover i
    refine ⟨e.symm ⟨j, ⟨i, hj⟩⟩, ?_⟩
    exact congrArg (fun z : I => z.2.val) (e.apply_symm_apply ⟨j, ⟨i, hj⟩⟩)
  refine ⟨Fintype.card I, hN, g, hg, ?_, ?_, ?_⟩
  · simp [I, Fintype.card_sigma]
  · intro w
    calc
      _ = ∑ z : I, w z.2.val := e.sum_comp (fun z : I => w z.2.val)
      _ = _ := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.sum_attach (F j) w
  · intro Y
    apply Set.Subset.antisymm
    · exact Set.iUnion_mono' fun a => ⟨g a, Set.Subset.rfl⟩
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      obtain ⟨a, rfl⟩ := hg i
      exact Set.mem_iUnion.mpr ⟨a, hi⟩

/-- A pointwise lower density remains a lower density after arbitrary incidence
multiplicity is introduced. -/
lemma uniform_incidence_mass {n p : ℕ} (F : Fin p → Finset (Fin n))
    (Y : Fin n → Set Space) {L : ℝ} (hL : 0 ≤ L)
    (hden : ∀ i, ENNReal.ofReal L ≤ volume (Y i)) :
    ENNReal.ofReal (L * (∑ j, ((F j).card : ℝ))) ≤ ∑ j, ∑ i ∈ F j, volume (Y i) := by
  classical
  have he : ENNReal.ofReal (L * (∑ j, ((F j).card : ℝ))) =
      ∑ j, ∑ _i ∈ F j, ENNReal.ofReal L := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul hL, ENNReal.ofReal_natCast, mul_comm]
  rw [he]
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hden i

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
