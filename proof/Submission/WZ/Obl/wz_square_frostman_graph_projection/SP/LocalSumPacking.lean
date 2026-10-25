-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.LocalSumPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealCoarseSubset
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.LocalSumCover

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- A local portion of a separated set and a coarse net in a summand
produce disjoint translated packets in a global sumset cover. -/
theorem local_sum_packing_count {δ r L x : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (A R : Finset ℝ) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hR : CoverLower (8 * r) (↑R : Set ℝ) L)
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers (3 * δ) (↑(A + R) : Set ℝ) cc) :
    ((A.filter (fun a => dist a x ≤ r)).card : ℝ) * L ≤ 18 * (m : ℝ) := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  let U := A.filter (fun a => dist a x ≤ r)
  obtain ⟨V, hVU, hVsep, hVc⟩ := real_coarse_separated_subset U hδ (by positivity : 0 < 8 * δ)
    (fun a ha b hb hne => hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hne)
  have hUV : (U.card : ℝ) ≤ 18 * (V.card : ℝ) := by
    convert hVc using 1 <;> field_simp <;> ring
  obtain ⟨n, z, hzR, hzsep, hzcover⟩ := exists_separated_cover R.finite_toSet.totallyBounded (by positivity : 0 < 8 * r)
  have hLn : L ≤ (n : ℝ) := hR n z hzcover
  let f (p : V × Fin n) := (p.1 : ℝ) + z p.2
  have hfsep (p q : V × Fin n) (hne : p ≠ q) : 2 * (3 * δ) < dist (f p) (f q) := by
    by_cases hsecond : p.2 = q.2
    · have hfirst : (p.1 : ℝ) ≠ (q.1 : ℝ) := by
        intro hh
        exact hne (Prod.ext (Subtype.ext hh) hsecond)
      have hh := hVsep p.1 p.1.property q.1 q.1.property hfirst
      simpa only [f, hsecond, dist_add_right] using (by linarith : 2 * (3 * δ) < dist (p.1 : ℝ) q.1)
    · have hz := hzsep p.2 q.2 hsecond
      have hp := (Finset.mem_filter.mp (hVU p.1.property)).2
      have hq := (Finset.mem_filter.mp (hVU q.1.property)).2
      have hdist : dist (p.1 : ℝ) q.1 ≤ 2 * r := by
        have hh := dist_triangle (p.1 : ℝ) x (q.1 : ℝ)
        rw [dist_comm x (q.1 : ℝ)] at hh
        linarith
      have hh := dist_triangle ((p.1 : ℝ) + z p.2) ((q.1 : ℝ) + z q.2) ((p.1 : ℝ) + z q.2)
      rw [dist_add_left, dist_add_right, dist_comm (q.1 : ℝ) (p.1 : ℝ)] at hh
      dsimp [f]
      linarith
  have hfcov : Covers (3 * δ) (Set.range f) cc := by
    rintro y ⟨p, rfl⟩
    exact hcov (Finset.add_mem_add (Finset.mem_filter.mp (hVU p.1.property)).1 (hzR p.2))
  have hprod := separated_indexed_card_le_cover f hfsep cc hfcov
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Nat.cast_mul] at hprod
  calc
    (U.card : ℝ) * L ≤ (U.card : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hLn (Nat.cast_nonneg _)
    _ ≤ (18 * (V.card : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right hUV (Nat.cast_nonneg _)
    _ ≤ 18 * (m : ℝ) := by nlinarith

/-- Entropy of a summand bounds the local density of the other summand. -/
theorem local_sum_packing_power {δ r s x : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (A R : Finset ℝ) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hR : CoverLower (8 * r) (↑R : Set ℝ) ((8 * r) ^ (-s)))
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers (3 * δ) (↑(A + R) : Set ℝ) cc) :
    ((A.filter (fun a => dist a x ≤ r)).card : ℝ) ≤ 18 * (m : ℝ) * (8 * r) ^ s := by
  have hh := local_sum_packing_count (x := x) hδ hδr A R hsep hR cc hcov
  have hr : 0 < 8 * r := by have := hδ.trans_le hδr; positivity
  have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hr.le s)
  have hid : (8 * r) ^ (-s) * (8 * r) ^ s = 1 := by rw [← Real.rpow_add hr]; simp
  simpa only [mul_assoc, hid, mul_one] using hm

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
