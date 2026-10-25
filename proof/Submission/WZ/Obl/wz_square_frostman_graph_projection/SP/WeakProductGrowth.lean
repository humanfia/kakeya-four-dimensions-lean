-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.WeakProductGrowth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.WeakUnitProductGrowth
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PinnedCoarseSubset
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RelativeNormalizationNumerics
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealNormalization

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

set_option maxHeartbeats 400000 in
/-- Relative two-product growth under any fixed positive nonconcentration
exponent and an independent entropy upper exponent below one. -/
theorem weak_product_growth (ε β : ℝ) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ τ α C : ℝ, 0 < δ → δ ≤ δ₀ → β ≤ τ →
        0 ≤ α → α ≤ 1 - ε → 1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A : Finset ℝ, A.Nonempty → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C τ A →
          (∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) →
          (A.card : ℝ) ≤ δ ^ (-α - η) →
          CoverLower δ (↑(A * A + A * A) : Set ℝ) (δ ^ (-η) * (A.card : ℝ)) := by
  classical
  obtain ⟨ηU, rU, hηU, hrU, hrU1, hunit⟩ := weak_unit_product_growth ε β hε hβ
  let g := min ηU 1
  have hg : 0 < g := lt_min hηU (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgη : g ≤ ηU := min_le_left _ _
  let κ := g / 100000
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκg : κ ≤ g / 10000 := by dsimp [κ]; linarith
  have hκ1 : κ ≤ 1 / 10000 := by dsimp [κ]; linarith
  let b := min β 1
  let η := κ * b
  have hb : 0 < b := lt_min hβ (by norm_num)
  have hb1 : b ≤ 1 := min_le_right _ _
  have hbβ : b ≤ β := min_le_left _ _
  have hη : 0 < η := mul_pos hκ hb
  have hηκ : η ≤ κ := by dsimp [η]; nlinarith
  obtain ⟨dC, hdC, hdC1, hcut⟩ := exists_monomial_bound 128 (a := κ) (b := 0) hκ
  obtain ⟨dR, hdR, hdR1, hscale⟩ := exists_monomial_bound (1 / rU)
    (a := 1 - 200 * κ) (b := 0) (by linarith)
  refine ⟨η, min dC dR, hη, lt_min hdC hdR, (min_le_left _ _).trans hdC1, ?_⟩
  intro δ τ α C hδ hδs hτ hα0 hα hC hCb A hAne hAb hAF hsep hAc m cc hcov
  have hδ1 : δ ≤ 1 := (hδs.trans (min_le_left _ _)).trans hdC1
  have hsmall : 128 * δ ^ κ ≤ 1 := by
    simpa only [Real.rpow_zero] using hcut δ hδ (hδs.trans (min_le_left _ _))
  have hδlt : δ < 1 := by
    by_contra hh
    have heq : δ = 1 := le_antisymm hδ1 (le_of_not_gt hh)
    simp only [heq, Real.one_rpow] at hsmall
    norm_num at hsmall
  have hCbκ : C ≤ δ ^ (-κ) := hCb.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hAcκ : (A.card : ℝ) ≤ δ ^ (-α - κ) := hAc.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hδq : δ ≤ δ ^ (100 * κ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : 100 * κ ≤ 1)
  have hpairbudget : C * (δ ^ (100 * κ)) ^ τ < 1 := by
    have hκτ := mul_le_mul_of_nonneg_left (hbβ.trans hτ) hκ.le
    calc
      C * (δ ^ (100 * κ)) ^ τ ≤ δ ^ (-η) * (δ ^ (100 * κ)) ^ τ := by gcongr
      _ = δ ^ (100 * κ * τ - η) := by rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by dsimp [η] at *; nlinarith)
      _ < 1 := Real.rpow_lt_one hδ.le hδlt hη
  obtain ⟨c, hc, d, hd, hcd⟩ := hAF.exists_separated_pair hAne hδq hpairbudget
  let t := A.max' hAne
  have htA : t ∈ A := Finset.max'_mem A hAne
  have hmax (a : ℝ) (ha : a ∈ A) : a ≤ t := Finset.le_max' A a ha
  have hsize : δ ^ (100 * κ) ≤ t := hcd.trans (abs_le.mpr
    ⟨by linarith [(hAb c hc).1, hmax d hd], by linarith [(hAb d hd).1, hmax c hc]⟩)
  have ht : 0 < t := (Real.rpow_pos_of_pos hδ _).trans_le hsize
  have ht1 : t ≤ 1 := (hAb t htA).2
  obtain ⟨B, hBA, htB, hBsep, hBcount⟩ := real_pinned_coarse_subset A hδ
    (div_pos hδ ht) htA hsep
  have hBN : t * (A.card : ℝ) ≤ 4 * (B.card : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hBcount ht.le
    have hid : t * (2 * (δ / t) / δ + 2) = 2 + 2 * t := by field_simp <;> ring
    rw [← mul_assoc, hid] at hh
    have hh' := mul_le_mul_of_nonneg_right ht1 (Nat.cast_nonneg B.card : (0 : ℝ) ≤ B.card)
    nlinarith
  let d₀ := δ ^ (101 * κ)
  have hd₀ : 0 < d₀ := Real.rpow_pos_of_pos hδ _
  have hretain : d₀ * (A.card : ℝ) ≤ (B.card : ℝ) := by
    have hq : 4 * d₀ ≤ t := by
      calc
        4 * d₀ = (4 * δ ^ κ) * δ ^ (100 * κ) := by
          rw [mul_assoc, ← Real.rpow_add hδ]; dsimp [d₀]; congr 1; ring
        _ ≤ 1 * δ ^ (100 * κ) := mul_le_mul_of_nonneg_right (by nlinarith [Real.rpow_pos_of_pos hδ κ])
          (Real.rpow_nonneg hδ.le _)
        _ ≤ t := by simpa only [one_mul] using hsize
    have hh := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
    nlinarith
  have hd₀1 : d₀ ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hBF := hAF.subset hδ (by linarith) hd₀ hBA hretain
  let S := B.image (fun a => a / t)
  have hinj : Function.Injective (fun a : ℝ => a / t) := fun _ _ hab => (div_left_inj' ht.ne').mp hab
  have hScard : S.card = B.card := Finset.card_image_of_injective _ hinj
  have hS1 : (1 : ℝ) ∈ S := Finset.mem_image.mpr ⟨t, htB, div_self ht.ne'⟩
  have hSb (b : ℝ) (hb : b ∈ S) : b ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨div_nonneg (hAb a (hBA ha)).1 ht.le, (div_le_one ht).mpr (hmax a (hBA ha))⟩
  let ρ := δ / t ^ 2
  have hρ : 0 < ρ := div_pos hδ (by positivity)
  have hρbound : ρ ≤ δ ^ (1 - 200 * κ) := product_normalized_mesh_upper hδ ht hsize
  have hρU : ρ ≤ rU := by
    apply hρbound.trans
    have hh := hscale δ hδ (hδs.trans (min_le_right _ _))
    rw [Real.rpow_zero] at hh
    have hh' : δ ^ (1 - 200 * κ) / rU ≤ 1 := by convert hh using 1 <;> ring
    have hh'' := (div_le_iff₀ hrU).mp hh'
    simpa only [one_mul] using hh''
  have hρ1 : ρ ≤ 1 := hρU.trans hrU1
  have hscale' : δ ≤ t * ρ := by
    have hid : t * ρ = δ / t := by dsimp [ρ]; field_simp
    rw [hid]
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hSF : RealFiniteFrostman ρ (C / d₀) τ S :=
    hBF.div_image hδ ht ht1 (by positivity) (by linarith) hscale'
  have hSsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ρ ≤ dist a b := by
    intro a ha b hb hne
    change a ∈ B.image (fun a => a / t) at ha
    change b ∈ B.image (fun a => a / t) at hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    have hh := hBsep u hu v hv (fun huv => hne (huv ▸ rfl))
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos ht]
    have hdiv := div_le_div_of_nonneg_right hh ht.le
    convert hdiv using 1 <;> dsimp [ρ] <;> field_simp <;> ring
  have hnum := relative_normalized_bounds hδ hδ1 hρ hρbound hκ hg hg1 hκg hα0 (by linarith : α ≤ 1)
  have hCρ : C / d₀ ≤ ρ ^ (-ηU) := by
    calc
      C / d₀ ≤ δ ^ (-κ) / δ ^ (101 * κ) := div_le_div_of_nonneg_right hCbκ hd₀.le
      _ = δ ^ (-(102 * κ)) := by rw [← Real.rpow_sub hδ]; congr 1; ring
      _ ≤ ρ ^ (-g) := hnum.1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have hSupper : (S.card : ℝ) ≤ ρ ^ (-α - ηU) := by
    calc
      (S.card : ℝ) = (B.card : ℝ) := by rw [hScard]
      _ ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hBA
      _ ≤ δ ^ (-α - κ) := hAcκ
      _ ≤ ρ ^ (-α - g) := hnum.2.1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have hCS : 1 ≤ C / d₀ := (le_div_iff₀ hd₀).mpr (by linarith)
  have hcoverB := Covers.div_product_sum ht (hcov.mono_set (Finset.add_subset_add
    (Finset.mul_subset_mul hBA hBA) (Finset.mul_subset_mul hBA hBA)))
  have hcount := hunit ρ τ α (C / d₀) hρ hρU hτ hα hCS hCρ S hS1 hSb hSF hSsep hSupper m _ hcoverB
  calc
    δ ^ (-η) * (A.card : ℝ) ≤ δ ^ (-κ) * (A.card : ℝ) := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (Nat.cast_nonneg _)
    _ ≤ (ρ ^ (-g) * d₀) * (A.card : ℝ) :=
      mul_le_mul_of_nonneg_right hnum.2.2 (Nat.cast_nonneg _)
    _ ≤ ρ ^ (-g) * (S.card : ℝ) := by rw [hScard, mul_assoc]; gcongr
    _ ≤ ρ ^ (-ηU) * (S.card : ℝ) := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)) (Nat.cast_nonneg _)
    _ ≤ _ := hcount

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
