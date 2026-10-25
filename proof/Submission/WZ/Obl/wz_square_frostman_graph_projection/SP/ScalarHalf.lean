-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarHalf.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarSelfSum

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- Small additive doubling controls the scalar one half, with a fixed loss. -/
theorem SmallScalarProjection.one_half {δ K : ℝ} {A : Finset ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hA : A.Nonempty)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hbase : SmallScalarProjection δ A K 1) :
    SmallScalarProjection δ A (9 * (6 * K) ^ 3) (1 / 2) := by
  classical
  obtain ⟨m, cc, hc, hm⟩ := hbase
  rw [realScalarImage_one] at hc
  obtain ⟨n, centers, hcov, hn⟩ :=
    mixed_plunnecke_nine hδ hK A A hA hsep cc hc hm 3 0 (by norm_num)
  have hbound : RealCoverBound δ ((3 : ℕ) • A) (9 * (6 * K) ^ 3 * (A.card : ℝ)) := by
    refine ⟨n, centers, ?_, ?_⟩
    · simpa only [zero_nsmul, sub_zero] using hcov
    · simpa only [Nat.add_zero] using hn
  have hscaled := hbound.scale_contract hδ.le (by norm_num : |(1 / 2 : ℝ)| ≤ 1)
  apply hscaled.mono _ le_rfl
  intro x hx
  obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  refine Finset.mem_image.mpr ⟨a + a + b, ?_, by ring⟩
  have hmem := Finset.add_mem_add (Finset.add_mem_add ha ha) hb
  simpa only [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, one_nsmul,
    zero_nsmul, zero_add] using hmem

/-- Halving a good scalar keeps it good when the unscaled sum is small. -/
theorem SmallScalarProjection.half {δ K L t : ℝ} {A : Finset ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hL : 0 ≤ L) (hA : A.Nonempty)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hbase : SmallScalarProjection δ A K 1)
    (ht : SmallScalarProjection δ A L t) :
    SmallScalarProjection δ A (288 * (9 * (6 * K) ^ 3) * L) (t / 2) := by
  have hh := (hbase.one_half hδ hK hA hsep).mul hδ
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (by positivity) hL hA hsep ht
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
