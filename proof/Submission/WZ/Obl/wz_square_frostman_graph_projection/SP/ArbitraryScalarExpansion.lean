-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ArbitraryScalarExpansion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarClosureIteration
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealFrostmanTruncation
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealFrostmanExponent

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
open scoped Pointwise

/-- A nonconcentrated scalar family expands a separated coordinate set of
entropy below one. No comparison between their cardinalities is required. -/
theorem arbitrary_scalar_expansion (ε b β : ℝ)
    (hε : 0 < ε) (hb : 0 < b) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ τ α C : ℝ, 0 < δ → δ ≤ δ₀ → b ≤ σ → β ≤ τ →
        0 ≤ α → α ≤ 1 - ε → 1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A S : Finset ℝ, A.Nonempty → S.Nonempty →
          (∀ s ∈ S, s ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C σ A → RealFiniteFrostman δ C τ S →
          (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') →
          (A.card : ℝ) ≤ δ ^ (-α - η) →
          ∃ t ∈ S, CoverLower δ
            ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(A ×ˢ A) : Set (ℝ × ℝ)))
            (δ ^ (-η) * (A.card : ℝ)) := by
  classical
  let β' := min β 1
  have hβ' : 0 < β' := lt_min hβ (by norm_num)
  have hβ'1 : β' ≤ 1 := min_le_right _ _
  have hβ'β : β' ≤ β := min_le_left _ _
  obtain ⟨ζ, r₀, hζ, hr₀, hr₀1, hno⟩ := no_small_scalar_family ε b β' hε hb hβ' hβ'1
  let k := min ζ 1
  have hk : 0 < k := lt_min hζ (by norm_num)
  have hkζ : k ≤ ζ := min_le_left _ _
  have hk1 : k ≤ 1 := min_le_right _ _
  let η := k * β' / 100
  have hη : 0 < η := by dsimp [η]; positivity
  have hηk : 100 * η ≤ k := by dsimp [η]; nlinarith
  have hηζ : η ≤ ζ := by linarith
  have hηβ : 2 * η ≤ k / 4 * β' := by dsimp [η]; nlinarith
  obtain ⟨d, hd, hd1, hcut⟩ := exists_power_bound 144 hη
  refine ⟨η, min r₀ d, hη, lt_min hr₀ hd, (min_le_left _ _).trans hr₀1, ?_⟩
  intro δ σ τ α C hδ hδs hσ hτ hα0 hα hC hCb A S hA hS hSb hAF hSF hAsep hAc
  have hδr : δ ≤ r₀ := hδs.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδr.trans hr₀1
  have hconst : 144 ≤ δ ^ (-η) := hcut δ hδ (hδs.trans (min_le_right _ _))
  have hSF' : RealFiniteFrostman δ C β' S := hSF.lower_exponent hδ hC hβ'.le (hβ'β.trans hτ)
  have hδc : δ ≤ δ ^ (k / 4) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : k / 4 ≤ 1)
  have htrim : C * (δ ^ (k / 4)) ^ β' ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hδ.le η)
    have hid : δ ^ (-η) * δ ^ η = 1 := by rw [← Real.rpow_add hδ]; simp
    rw [hid] at hh
    calc
      C * (δ ^ (k / 4)) ^ β' ≤ δ ^ (-η) * (δ ^ (k / 4)) ^ β' := by gcongr
      _ = δ ^ (k / 4 * β' - η) := by
        rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ ≤ 1 / 2 := by nlinarith [Real.rpow_pos_of_pos hδ η]
  obtain ⟨B, hBS, hB, hBlow, hBcard, hBF⟩ := hSF'.trim_zero hδ (by linarith) hδc hS
    (fun s hs => (hSb s hs).1) htrim
  have hCbζ : C ≤ δ ^ (-ζ) := hCb.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have h2Cbζ : 2 * C ≤ δ ^ (-ζ) := by
    calc
      2 * C ≤ δ ^ (-η) * δ ^ (-η) := by gcongr; linarith
      _ = δ ^ (-(2 * η)) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hAFζ : RealFiniteFrostman δ (δ ^ (-ζ)) σ A := hAF.weaken hδ hCbζ
  have hBFζ : RealFiniteFrostman δ (δ ^ (-ζ)) β' B := hBF.weaken hδ h2Cbζ
  have hAcζ : (A.card : ℝ) ≤ δ ^ (-α - ζ) := hAc.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  by_contra hfail
  have hsmall (s : ℝ) (hs : s ∈ S) : SmallScalarProjection δ A (δ ^ (-η)) s := by
    have hh : ¬ CoverLower δ
        ((fun p : ℝ × ℝ => p.1 + s * p.2) '' (↑(A ×ˢ A) : Set (ℝ × ℝ)))
        (δ ^ (-η) * (A.card : ℝ)) := fun h => hfail ⟨s, hs, h⟩
    unfold CoverLower at hh
    push_neg at hh
    obtain ⟨m, cc, hc, hm⟩ := hh
    refine ⟨m, cc, ?_, hm.le⟩
    intro x hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact hc ⟨(a, v), Finset.mem_product.mpr ⟨ha, hv⟩, rfl⟩
  obtain ⟨u, hu⟩ := hB
  have hu0 : 0 < u := (Real.rpow_pos_of_pos hδ _).trans_le (hBlow u hu)
  have hbase := (hsmall u (hBS hu)).self_sum hδ hu0 (hSb u (hBS hu)).2
    (Real.rpow_nonneg hδ.le _) hA hAsep
  have hbaseζ : SmallScalarProjection δ A (δ ^ (-ζ)) 1 := by
    apply hbase.weaken
    calc
      144 * (δ ^ (-η)) ^ 2 / u ≤ δ ^ (-η) * (δ ^ (-η)) ^ 2 / δ ^ (k / 4) := by gcongr <;> linarith [hBlow u hu]
      _ = δ ^ (-(3 * η + k / 4)) := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
        congr 1
        norm_num
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  exact hno δ σ α hδ hδr hσ hα0 hα A B hA ⟨u, hu⟩ hAFζ hBFζ hAsep hAcζ
    (fun s hs => ⟨(Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : k / 4 ≤ ζ)).trans
      (hBlow s hs), (hSb s (hBS hs)).2⟩)
    hbaseζ (fun s hs => (hsmall s (hBS hs)).weaken
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
