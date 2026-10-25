-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarCountPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarFamilyCover

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- An entropy bound for a separated family of good scalars. Its exponent
loss only depends on a positive lower bound for coordinate nonconcentration. -/
theorem small_scalar_card_power (A R : Finset ℝ) {δ d α β σ C : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 0 < d) (hβ : 0 < β)
    (hσ : β ≤ σ) (hdβ : 4 * d / β ≤ 1)
    (hconst : 12 ≤ δ ^ (-d)) (hC : 0 ≤ C) (hCb : C ≤ δ ^ (-d))
    (hA : A.Nonempty) (hAF : RealFiniteFrostman δ C σ A)
    (hAsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hAc : (A.card : ℝ) ≤ δ ^ (-α - d))
    (hRsep : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → δ ≤ dist a b)
    (hgood : ∀ t ∈ R, SmallScalarProjection δ A (δ ^ (-d)) t) :
    (R.card : ℝ) ≤ δ ^ (-α - (3 + 4 / β) * d) := by
  let q := δ ^ (4 * d / β)
  have hq : 0 < q := Real.rpow_pos_of_pos hδ _
  have hδq : δ ≤ q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hdβ
  have hq1 : q ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hpow : q ^ σ ≤ δ ^ (4 * d) := by
    have hexp : 4 * d ≤ (4 * d / β) * σ := by
      have hh := mul_le_mul_of_nonneg_left hσ (by positivity : 0 ≤ 4 * d / β)
      have hid : (4 * d / β) * β = 4 * d := by field_simp
      rwa [hid] at hh
    dsimp [q]
    rw [← Real.rpow_mul hδ.le]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
  have hbudget : 12 * δ ^ (-d) * C * q ^ σ ≤ 1 := by
    calc
      _ ≤ δ ^ (-d) * δ ^ (-d) * δ ^ (-d) * δ ^ (4 * d) := by gcongr
      _ = δ ^ d := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hd.le
  have hs (t : ℝ) (ht : t ∈ R) : ∃ (m : ℕ) (cc : Fin m → ℝ),
      Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(A ×ˢ A) : Set (ℝ × ℝ))) cc ∧
        (m : ℝ) ≤ δ ^ (-d) * (A.card : ℝ) := by
    obtain ⟨m, cc, hc, hm⟩ := hgood t ht
    refine ⟨m, cc, ?_, hm⟩
    rintro x ⟨p, hp, rfl⟩
    exact hc (Finset.add_mem_add (Finset.mem_product.mp hp).1
      (Finset.mem_image.mpr ⟨p.2, (Finset.mem_product.mp hp).2, rfl⟩))
  have hcount := small_projection_scalar_count A R hδ hδq hq1 hC
    (Real.rpow_pos_of_pos hδ _) hA hAF hAsep hRsep hbudget hs
  calc
    (R.card : ℝ) ≤ 12 * δ ^ (-d) * (A.card : ℝ) / q :=
      (le_div_iff₀ hq).mpr (by nlinarith)
    _ ≤ δ ^ (-d) * δ ^ (-d) * δ ^ (-α - d) / q := by gcongr
    _ = _ := by
      dsimp [q]
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
      congr 1
      ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
