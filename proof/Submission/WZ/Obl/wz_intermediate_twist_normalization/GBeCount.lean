-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.GBeCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.GBeAux

/-!
# Counts of translated families

For a family in the thin cylinder with the enlarged convex count `Kt |W + 2e(W - W)|`, a bounded
convex set `P` and a horizontal translation `s`:

* the number of translated tubes inside `P` is at most `Kt |P + 2e(P - P)|`
  (`count_translate_le`);
* summed over the grid of translations, it is at most `m · 2 |P| / h²` (`grid_sum_le`).
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube)

/-- The enlargement commutes with translations. -/
theorem enlarge_translate (W : Set Space) (t : ℝ) (s : Space) :
    (fun p => p + s) ⁻¹' W + t • ((fun p => p + s) ⁻¹' W - (fun p => p + s) ⁻¹' W) =
      (fun p => p + s) ⁻¹' (W + t • (W - W)) := by
  ext p
  simp only [mem_preimage, Set.mem_add, Set.mem_smul_set, Set.mem_sub]
  constructor
  · rintro ⟨a, ha, _, ⟨d, ⟨w1, hw1, w2, hw2, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a + s, ha, _, ⟨w1 + s - (w2 + s), ⟨w1 + s, hw1, w2 + s, hw2, rfl⟩, rfl⟩, by abel⟩
  · rintro ⟨a, ha, _, ⟨d, ⟨w1, hw1, w2, hw2, rfl⟩, rfl⟩, hp⟩
    refine ⟨a - s, by simpa using ha, _, ⟨(w1 - s) - (w2 - s), ⟨w1 - s, by simpa using hw1,
      w2 - s, by simpa using hw2, rfl⟩, rfl⟩, ?_⟩
    rw [← sub_eq_iff_eq_add.mpr hp.symm]
    simp only [sub_sub_sub_cancel_right]
    abel

theorem tube_translate_subset_iff (ρ : ℝ) (x v s : Space) (P : Set Space) :
    tube ρ (x + s) v ⊆ P ↔ tube ρ x v ⊆ (fun p => p + s) ⁻¹' P := by
  rw [tube_translate]
  constructor
  · intro h p hp
    apply h
    show p + s - s ∈ tube ρ x v
    rwa [add_sub_cancel_right]
  · intro h q hq
    have := h hq
    simp only [mem_preimage, sub_add_cancel] at this
    exact this

open Classical in
/-- **Counts of a translate.** -/
theorem count_translate_le {ρ e Kt : ℝ} (hKt : 0 ≤ Kt) {m : ℕ} {x v : Fin m → Space}
    (hcount : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | tube ρ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal Kt * volume (W + (2 * e) • (W - W)))
    {P : Set Space} (hP : Convex ℝ P) (hPfin : volume (P + (2 * e) • (P - P)) ≠ ⊤) (s : Space) :
    ((Finset.univ.filter (fun i => tube ρ (x i + s) (v i) ⊆ P)).card : ℝ) ≤
      Kt * (volume (P + (2 * e) • (P - P))).toReal := by
  classical
  have hW : Convex ℝ ((fun p => p + s) ⁻¹' P) := by
    simpa [add_comm] using hP.translate_preimage_right s
  have h := hcount _ hW
  rw [enlarge_translate, measure_preimage_add_right] at h
  have hset : {i | tube ρ (x i) (v i) ⊆ (fun p => p + s) ⁻¹' P} =
      ↑(Finset.univ.filter (fun i => tube ρ (x i + s) (v i) ⊆ P)) := by
    ext i; simp [tube_translate_subset_iff]
  rw [hset, Set.ncard_coe_finset] at h
  rw [← ENNReal.ofReal_toReal hPfin, ← ENNReal.ofReal_mul hKt] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

open Classical in
/-- **The grid sum.** -/
theorem grid_sum_le {ρ h : ℝ} (hh : 0 < h) (hhρ : h ≤ ρ / 2) {m : ℕ} {x v : Fin m → Space}
    (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|) (M : ℕ) {P : Set Space} (hPfin : volume P ≠ ⊤) :
    ∑ ab : Fin (2 * M + 1) × Fin (2 * M + 1),
      ((Finset.univ.filter (fun i => tube ρ (x i + sgrid h M ab.1 ab.2) (v i) ⊆ P)).card : ℝ) ≤
      m * (2 * (volume P).toReal / h ^ 2) := by
  classical
  have hswap : ∑ ab : Fin (2 * M + 1) × Fin (2 * M + 1),
      ((Finset.univ.filter (fun i => tube ρ (x i + sgrid h M ab.1 ab.2) (v i) ⊆ P)).card : ℝ) =
      ∑ i : Fin m, ((Finset.univ.filter (fun ab : Fin (2 * M + 1) × Fin (2 * M + 1) =>
        tube ρ (x i + sgrid h M ab.1 ab.2) (v i) ⊆ P)).card : ℝ) := by
    simp only [Finset.card_filter]
    push_cast
    exact Finset.sum_comm
  rw [hswap]
  calc ∑ i : Fin m, ((Finset.univ.filter (fun ab : Fin (2 * M + 1) × Fin (2 * M + 1) =>
        tube ρ (x i + sgrid h M ab.1 ab.2) (v i) ⊆ P)).card : ℝ)
      ≤ ∑ _i : Fin m, 2 * (volume P).toReal / h ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hg := grid_count hh hhρ (x := x i) (hv2 i) M P
        rw [← ENNReal.ofReal_toReal hPfin] at hg
        have hg' := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hg
        rw [le_div_iff₀ (by positivity)]
        linarith
    _ = m * (2 * (volume P).toReal / h ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end WangZahlLot.Obl.wz_intermediate_twist_normalization
