-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.WeakRectangularScalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit 7d51ba0; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RectangularNumerics
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ArbitraryScalarExpansion
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.WeakScalarCutoff

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- Rectangular expansion with independent positive coordinate dimension and
cardinality dimension, and arbitrary positively nonconcentrated slopes. -/
theorem weak_coordinate_rectangular_expansion (ε bA β : ℝ) (hε : 0 < ε) (hbA : 0 < bA) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ τ α C : ℝ, 0 < δ → δ ≤ δ₀ → bA ≤ σ → β ≤ τ → 0 ≤ α → α ≤ 1 - ε →
        1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A B S : Finset ℝ, A.Nonempty → B.Nonempty → S.Nonempty →
          (∀ s ∈ S, s ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C σ A → RealFiniteFrostman δ C σ B → RealFiniteFrostman δ C τ S →
          (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') →
          (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') →
          (A.card : ℝ) ≤ δ ^ (-α - η) → (B.card : ℝ) ≤ δ ^ (-α - η) →
          δ ^ (η - α) ≤ (A.card : ℝ) → δ ^ (η - α) ≤ (B.card : ℝ) →
          ∃ t ∈ S, CoverLower δ
            ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(A ×ˢ B) : Set (ℝ × ℝ)))
            (δ ^ (-η) * (A.card : ℝ)) := by
  classical
  obtain ⟨θ, rP, hθ, hrP, hrP1, hproject⟩ := arbitrary_scalar_expansion ε bA β hε hbA hβ
  let κ := min (θ / 1000) (1 / 10000)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκθ : 1000 * κ ≤ θ := by have := min_le_left (θ / 1000) (1 / 10000); dsimp [κ]; linarith
  have hκ1 : κ ≤ 1 / 10000 := min_le_right _ _
  let b := min β 1
  let η := κ * b / 100
  have hb : 0 < b := lt_min hβ (by norm_num)
  have hb1 : b ≤ 1 := min_le_right _ _
  have hbβ : b ≤ β := min_le_left _ _
  have hη : 0 < η := by dsimp [η]; positivity
  have hηκ : η ≤ κ := by dsimp [η]; nlinarith
  obtain ⟨dC, hdC, hdC1, hconstants⟩ := exists_power_bound 52488 hη
  refine ⟨η, min rP (min dC (1 / 2)), hη, lt_min hrP (lt_min hdC (by norm_num)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (by norm_num)), ?_⟩
  intro δ σ τ α C hδ hδs hσ hτ hα hαmax hC hCbη A B S hAne hBne hSne hS hAF hBF hSF hAsep hBsep hAcη hBcη hAlo hBlo
  have hδP : δ ≤ rP := hδs.trans (min_le_left _ _)
  have hδC : δ ≤ dC := hδs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδhalf : δ ≤ 1 / 2 := hδs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by linarith
  have hδlt : δ < 1 := by linarith
  have hconstη : 52488 ≤ δ ^ (-η) := hconstants δ hδ hδC
  have herror : δ ^ (-η) ≤ δ ^ (-κ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hconst : 52488 ≤ δ ^ (-κ) := hconstη.trans herror
  have hCb : C ≤ δ ^ (-κ) := hCbη.trans herror
  have hAc : (A.card : ℝ) ≤ δ ^ (-α - κ) := hAcη.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hBc : (B.card : ℝ) ≤ δ ^ (-α - κ) := hBcη.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hcut := weak_scalar_cutoff_budget hδ hδ1 hκ hκ1
    (show 2 * η ≤ 100 * κ * τ by
      have hh := mul_le_mul_of_nonneg_left (hbβ.trans hτ) hκ.le
      dsimp [η]; nlinarith)
    hCbη ((by norm_num : (2 : ℝ) ≤ 52488).trans hconstη)
  obtain ⟨c, hc, d, hd, hcd⟩ := hSF.exists_separated_pair hSne hcut.1
    (hcut.2.2.trans_lt (by norm_num))
  let a := S.max' hSne
  have haS : a ∈ S := Finset.max'_mem S hSne
  have hmax (s : ℝ) (hs : s ∈ S) : s ≤ a := Finset.le_max' S s hs
  have halow : δ ^ (100 * κ) ≤ a := hcd.trans (abs_le.mpr
    ⟨by linarith [(hS c hc).1, hmax d hd], by linarith [(hS d hd).1, hmax c hc]⟩)
  have ha : 0 < a := (Real.rpow_pos_of_pos hδ _).trans_le halow
  have ha1 : a ≤ 1 := (hS a haS).2
  let T := S.image (fun s => s / a)
  have hTne : T.Nonempty := hSne.image _
  have hTunit (t : ℝ) (ht : t ∈ T) : t ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨div_nonneg (hS s hs).1 ha.le, (div_le_one ha).mpr (hmax s hs)⟩
  have hTF : RealFiniteFrostman δ C τ T := hSF.div_image_same_scale hδ ha ha1
  have hCθ : C ≤ δ ^ (-θ) := hCb.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hBcθ : (B.card : ℝ) ≤ δ ^ (-α - θ) := hBc.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  obtain ⟨v, hv, hvcount⟩ := hproject δ σ τ α C hδ hδP hσ hτ hα hαmax hC hCθ
    B T hBne hTne hTunit hBF hTF hBsep hBcθ
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
  by_contra hgood
  have hsmall (s : ℝ) (hs : s ∈ S) :
      RealCoverBound δ (A + realScalarImage s B) (δ ^ (-κ) * (A.card : ℝ)) := by
    have hnot : ¬ CoverLower δ
        ((fun p : ℝ × ℝ => p.1 + s * p.2) '' (↑(A ×ˢ B) : Set (ℝ × ℝ)))
        (δ ^ (-η) * (A.card : ℝ)) := fun h => hgood ⟨s, hs, h⟩
    unfold CoverLower at hnot
    push_neg at hnot
    obtain ⟨m, cc, hc, hm⟩ := hnot
    exact ⟨m, cc, by rwa [rectangular_projection_image] at hc,
      hm.le.trans (mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg _))⟩
  obtain ⟨m, cc, hc, hm⟩ := rectangular_scalar_transfer A B hδ ha ha1 (by positivity)
    hAne hAsep (hsmall a haS) (hsmall t ht)
  have hratio : (A.card : ℝ) ≤ δ ^ (-2 * κ) * (B.card : ℝ) :=
    rectangular_card_ratio hδ hAc
      ((Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show η - α ≤ κ - α by linarith)).trans hBlo)
  have hupper : (m : ℝ) ≤ δ ^ (-105 * κ) * (B.card : ℝ) := hm.trans
    (rectangular_scalar_power_budget hδ halow (Nat.cast_nonneg _) (Nat.cast_nonneg _) hratio
      ((by norm_num : (108 : ℝ) ≤ 52488).trans hconst))
  rw [rectangular_projection_image] at hvcount
  have hlower := hvcount m cc hc
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hBne
  have hstrict : δ ^ (-105 * κ) * (B.card : ℝ) < δ ^ (-θ) * (B.card : ℝ) :=
    mul_lt_mul_of_pos_right (Real.rpow_lt_rpow_of_exponent_gt hδ hδlt (by linarith)) hBp
  exact (not_le_of_gt hstrict) (hlower.trans hupper)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
