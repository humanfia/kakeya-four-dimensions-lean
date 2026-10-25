-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.UniformWeakCoordinates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit 7d51ba0; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.SmallProjectionRectangle
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PopularRectangles
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.OverlappingRectangles
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.UniformProjectionNumerics
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.WeakRectangularScalar

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 600000 in
/-- Dense-relation expansion with independent positive coordinate dimension
and cardinality dimension. Slopes have any fixed positive dimension, with no
cardinality or separation condition. -/
theorem uniform_weak_coordinate_expansion (ε bA β : ℝ) (hε : 0 < ε) (hbA : 0 < bA) (hβ : 0 < β) :
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
          ∃ t ∈ S, ∀ R : A → B → Prop,
            δ ^ η * (A.card : ℝ) * (B.card : ℝ) ≤
              ((Finset.univ.filter (fun p : A × B => R p.1 p.2)).card : ℝ) →
            CoverLower δ
              ((fun q : A × B => (q.1 : ℝ) + t * (q.2 : ℝ)) ''
                (↑(Finset.univ.filter (fun q : A × B => R q.1 q.2)) : Set (A × B)))
              (δ ^ (-η) * (A.card : ℝ)) := by
  classical
  obtain ⟨θ, rP, hθ, hrP, hrP1, hproject⟩ := weak_coordinate_rectangular_expansion ε bA β hε hbA hβ
  let κ := min (θ / 10000) (1 / 10000)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκθ : 10000 * κ ≤ θ := by have := min_le_left (θ / 10000) (1 / 10000); dsimp [κ]; linarith
  have hκ1 : κ ≤ 1 / 10000 := min_le_right _ _
  let b := min β 1
  let η := κ * b / 100
  have hb : 0 < b := lt_min hβ (by norm_num)
  have hb1 : b ≤ 1 := min_le_right _ _
  have hbβ : b ≤ β := min_le_left _ _
  have hη : 0 < η := by dsimp [η]; positivity
  have hηκ : η ≤ κ := by dsimp [η]; nlinarith
  obtain ⟨dC, hdC, hdC1, hconstants⟩ := exists_power_bound 603979776 hη
  refine ⟨η, min rP (min dC (1 / 2)), hη, lt_min hrP (lt_min hdC (by norm_num)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (by norm_num)), ?_⟩
  intro δ σ τ α C hδ hδs hσ hτ hα hαmax hC hCbη A B S hA hB hS hSunit hAF hBF hSF hAsep hBsep hAcη hBcη hAlo hBlo
  have hδP : δ ≤ rP := hδs.trans (min_le_left _ _)
  have hδC : δ ≤ dC := hδs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδhalf : δ ≤ 1 / 2 := hδs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by linarith
  have hδlt : δ < 1 := by linarith
  have hconstη : 603979776 ≤ δ ^ (-η) := hconstants δ hδ hδC
  have herror : δ ^ (-η) ≤ δ ^ (-κ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hconst : 603979776 ≤ δ ^ (-κ) := hconstη.trans herror
  have hCb : C ≤ δ ^ (-κ) := hCbη.trans herror
  have hAc : (A.card : ℝ) ≤ δ ^ (-α - κ) := hAcη.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hBc : (B.card : ℝ) ≤ δ ^ (-α - κ) := hBcη.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hcut := weak_scalar_cutoff_budget hδ hδ1 hκ hκ1
    (show 2 * η ≤ 100 * κ * τ by
      have hh := mul_le_mul_of_nonneg_left (hbβ.trans hτ) hκ.le
      dsimp [η]; nlinarith)
    hCbη ((by norm_num : (2 : ℝ) ≤ 603979776).trans hconstη)
  obtain ⟨T, hTS, hT, hTlow, hST, hTF⟩ := hSF.trim_zero hδ (by linarith) hcut.1 hS
    (fun s hs => (hSunit s hs).1) hcut.2.2
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  by_contra hgood
  have hbad (t : T) : ∃ R : A → B → Prop,
      δ ^ κ * (A.card : ℝ) * (B.card : ℝ) ≤
        ((Finset.univ.filter (fun p : A × B => R p.1 p.2)).card : ℝ) ∧
      ∃ (m : ℕ) (cc : Fin m → ℝ),
        Covers δ ((fun q : A × B => (q.1 : ℝ) + (t : ℝ) * (q.2 : ℝ)) ''
          (↑(Finset.univ.filter (fun q : A × B => R q.1 q.2)) : Set (A × B))) cc ∧
        (m : ℝ) < δ ^ (-κ) * (A.card : ℝ) := by
    have hn : ¬ ∀ R : A → B → Prop,
        δ ^ η * (A.card : ℝ) * (B.card : ℝ) ≤
          ((Finset.univ.filter (fun p : A × B => R p.1 p.2)).card : ℝ) →
        CoverLower δ ((fun q : A × B => (q.1 : ℝ) + (t : ℝ) * (q.2 : ℝ)) ''
          (↑(Finset.univ.filter (fun q : A × B => R q.1 q.2)) : Set (A × B)))
          (δ ^ (-η) * (A.card : ℝ)) := fun h => hgood ⟨t, hTS t.2, h⟩
    push_neg at hn
    obtain ⟨R, hR, hn⟩ := hn
    unfold CoverLower at hn
    push_neg at hn
    obtain ⟨m, cc, hcov, hm⟩ := hn
    refine ⟨R, ?_, m, cc, hcov, hm.trans_le ?_⟩
    · exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηκ)
          (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans hR
    · exact mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg _)
  choose R hR m cc hcover hm using hbad
  have hratio : (A.card : ℝ) ≤ δ ^ (-2 * κ) * (B.card : ℝ) :=
    rectangular_card_ratio hδ hAc
      ((Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show η - α ≤ κ - α by linarith)).trans hBlo)
  have hrect (t : T) := small_projection_rectangle_of_ratio A B (R t) hδ hδ1 hκ hA hB
    hAsep hBsep hratio (hR t) (hTlow t t.2) (hSunit t (hTS t.2)).2 hconst (cc t) (hcover t) (hm t).le
  choose X Y hXA hYB hX hY hXsize hYsize hproj using hrect
  let e := (δ ^ κ) ^ 2 / 16
  let g := e ^ 4 / 2
  have hd : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ _
  have hd1 : δ ^ κ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hκ.le
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by dsimp [e]; nlinarith [mul_self_le_mul_self hd.le hd1]
  have hg : 0 < g := by dsimp [g]; positivity
  have hge : g ≤ e := by
    have he3 : e ^ 3 ≤ 1 := pow_le_one₀ he.le he1
    have hh := mul_le_mul_of_nonneg_left he3 he.le
    dsimp [g]
    nlinarith
  have hg1 : g ≤ 1 := hge.trans he1
  have hsz := uniform_rectangle_size_budget hδ
    ((by norm_num : (131072 : ℝ) ≤ 603979776).trans hconst)
  have heb : δ ^ (3 * κ) ≤ e := hsz.1
  have hgb : δ ^ (9 * κ) ≤ g := hsz.2
  obtain ⟨a, U, hU, hUsize, hoverlap⟩ := popular_rectangles A B X Y he hA hB hXA hYB hXsize hYsize
  simp only [Fintype.card_coe] at hUsize
  let S' := U.image (fun t : T => (t : ℝ))
  have hS'card : S'.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hS'T : S' ⊆ T := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact u.2
  have hS' : S'.Nonempty := hU.image _
  have hS'size : g * (T.card : ℝ) ≤ (S'.card : ℝ) := by rw [hS'card]; exact hUsize
  let D := 2 * C / g
  have hD : 1 ≤ D := (le_div_iff₀ hg).mpr (by nlinarith)
  have hCD : C / e ≤ D := by
    calc
      C / e ≤ C / g := div_le_div_of_nonneg_left (by linarith) hg hge
      _ ≤ 2 * C / g := by gcongr; linarith
  have hDb : D ≤ δ ^ (-11 * κ) := uniform_frostman_power_budget hδ (by linarith) hCb hgb
    ((by norm_num : (2 : ℝ) ≤ 603979776).trans hconst)
  have hDθ : D ≤ δ ^ (-θ) := hDb.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hXF : RealFiniteFrostman δ D σ (X a) :=
    (hAF.subset hδ (by linarith) he (hXA a) (hXsize a)).weaken hδ hCD
  have hYF : RealFiniteFrostman δ D σ (Y a) :=
    (hBF.subset hδ (by linarith) he (hYB a) (hYsize a)).weaken hδ hCD
  have hS'F : RealFiniteFrostman δ D τ S' := hTF.subset hδ (by linarith) hg hS'T hS'size
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  have hBcard : δ ^ (2 * κ) * (A.card : ℝ) ≤ (B.card : ℝ) := by
    calc
      _ ≤ δ ^ (2 * κ) * (δ ^ (-2 * κ) * (B.card : ℝ)) := by gcongr
      _ = _ := by rw [← mul_assoc, ← Real.rpow_add hδ]; simp
  have hXa3 : δ ^ (3 * κ) * (A.card : ℝ) ≤ ((X a).card : ℝ) :=
    (mul_le_mul_of_nonneg_right heb hAp.le).trans (hXsize a)
  have hXa5 : δ ^ (5 * κ) * (A.card : ℝ) ≤ ((X a).card : ℝ) :=
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) hAp.le).trans hXa3
  have hYa5 : δ ^ (5 * κ) * (A.card : ℝ) ≤ ((Y a).card : ℝ) := by
    calc
      _ = δ ^ (3 * κ) * (δ ^ (2 * κ) * (A.card : ℝ)) := by rw [← mul_assoc, ← Real.rpow_add hδ]; congr 2; ring
      _ ≤ e * (B.card : ℝ) := mul_le_mul heb hBcard (by positivity) he.le
      _ ≤ _ := hYsize a
  have hta : 0 < (a : ℝ) := (Real.rpow_pos_of_pos hδ _).trans_le (hTlow a a.2)
  have hta1 : (a : ℝ) ≤ 1 := (hSunit a (hTS a.2)).2
  obtain ⟨hAA, hBB⟩ := rectangular_projection_self_sums (X a) (Y a) hδ hta hta1 (hX a) (hY a)
    (fun x hx y hy hne => hAsep x (hXA a hx) y (hXA a hy) hne)
    (fun x hx y hy hne => hBsep x (hYB a hx) y (hYB a hy) hne) (hproj a)
  have h144 : (144 : ℝ) ≤ δ ^ (-κ) := (by norm_num : (144 : ℝ) ≤ 603979776).trans hconst
  have hAA' : RealCoverBound δ (X a + X a) (δ ^ (-334 * κ) * (A.card : ℝ)) :=
    hAA.mono (fun _ h => h) (uniform_self_sum_power_budget hδ hAp (hTlow a a.2) hYa5 h144)
  have hBB' : RealCoverBound δ (Y a + Y a) (δ ^ (-334 * κ) * (A.card : ℝ)) :=
    hBB.mono (fun _ h => h) ((show 108 * (δ ^ (-114 * κ) * (A.card : ℝ)) ^ 2 /
      ((a : ℝ) * ((X a).card : ℝ)) ≤ 144 * (δ ^ (-114 * κ) * (A.card : ℝ)) ^ 2 /
      ((a : ℝ) * ((X a).card : ℝ)) by gcongr; norm_num).trans
      (uniform_self_sum_power_budget hδ hAp (hTlow a a.2) hXa5 h144))
  have hsmall (t : ℝ) (ht : t ∈ S') : RealCoverBound δ (X a + realScalarImage t (Y a))
      (δ ^ (-906 * κ) * ((X a).card : ℝ)) := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hXu, hYu⟩ := hoverlap u hu
    have hXu' : δ ^ (9 * κ) * (A.card : ℝ) ≤ ((X a ∩ X u).card : ℝ) :=
      (mul_le_mul_of_nonneg_right hgb hAp.le).trans hXu
    have hYu' : δ ^ (11 * κ) * (A.card : ℝ) ≤ ((Y a ∩ Y u).card : ℝ) := by
      calc
        _ = δ ^ (9 * κ) * (δ ^ (2 * κ) * (A.card : ℝ)) := by rw [← mul_assoc, ← Real.rpow_add hδ]; congr 2; ring
        _ ≤ g * (B.card : ℝ) := mul_le_mul hgb hBcard (by positivity) hg.le
        _ ≤ _ := hYu
    have hUne : (X a ∩ X u).Nonempty := by
      apply Finset.card_pos.mp
      have hh : (0 : ℝ) < (X a ∩ X u).card := (mul_pos (Real.rpow_pos_of_pos hδ _) hAp).trans_le hXu'
      exact_mod_cast hh
    have hVne : (Y a ∩ Y u).Nonempty := by
      apply Finset.card_pos.mp
      have hh : (0 : ℝ) < (Y a ∩ Y u).card := (mul_pos (Real.rpow_pos_of_pos hδ _) hAp).trans_le hYu'
      exact_mod_cast hh
    have htu : 0 < (u : ℝ) := (Real.rpow_pos_of_pos hδ _).trans_le (hTlow u u.2)
    have hh := overlapping_rectangle_projection (X a) (Y a) (X u) (Y u) hδ htu
      (hSunit u (hTS u.2)).2 hUne hVne
      (fun x hx y hy hne => hAsep x (hXA a hx) y (hXA a hy) hne)
      (fun x hx y hy hne => hBsep x (hYB a hx) y (hYB a hy) hne) hAA' hBB' (hproj u)
    apply hh.mono (fun _ h => h)
    apply (uniform_overlap_power_budget hδ hAp (hTlow u u.2) hXu' hYu'
      ((by norm_num : (5184 : ℝ) ≤ 603979776).trans hconst)).trans
    calc
      δ ^ (-903 * κ) * (A.card : ℝ) = δ ^ (-906 * κ) * (δ ^ (3 * κ) * (A.card : ℝ)) := by
        rw [← mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hXa3 (Real.rpow_nonneg hδ.le _)
  have hXc : ((X a).card : ℝ) ≤ δ ^ (-α - θ) :=
    (show ((X a).card : ℝ) ≤ (A.card : ℝ) by exact_mod_cast Finset.card_le_card (hXA a)).trans
      (hAc.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))
  have hYc : ((Y a).card : ℝ) ≤ δ ^ (-α - θ) :=
    (show ((Y a).card : ℝ) ≤ (B.card : ℝ) by exact_mod_cast Finset.card_le_card (hYB a)).trans
      (hBc.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))
  have hXlo : δ ^ (θ - α) ≤ ((X a).card : ℝ) := by
    calc
      _ ≤ δ ^ (3 * κ + η - α) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ (3 * κ) * δ ^ (η - α) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (3 * κ) * (A.card : ℝ) := mul_le_mul_of_nonneg_left hAlo (by positivity)
      _ ≤ _ := hXa3
  have hYlo : δ ^ (θ - α) ≤ ((Y a).card : ℝ) := by
    calc
      _ ≤ δ ^ (3 * κ + η - α) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ (3 * κ) * δ ^ (η - α) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (3 * κ) * (B.card : ℝ) := mul_le_mul_of_nonneg_left hBlo (by positivity)
      _ ≤ e * (B.card : ℝ) := mul_le_mul_of_nonneg_right heb (by positivity)
      _ ≤ _ := hYsize a
  obtain ⟨t, ht, htlarge⟩ := hproject δ σ τ α D hδ hδP hσ hτ hα hαmax hD hDθ (X a) (Y a) S' (hX a) (hY a) hS'
    (fun s hs => hSunit s (hTS (hS'T hs))) hXF hYF hS'F
    (fun x hx y hy hne => hAsep x (hXA a hx) y (hXA a hy) hne)
    (fun x hx y hy hne => hBsep x (hYB a hx) y (hYB a hy) hne)
    hXc hYc hXlo hYlo
  obtain ⟨n, centers, hcov, hn⟩ := hsmall t ht
  rw [rectangular_projection_image] at htlarge
  have hlower := htlarge n centers hcov
  have hXp : (0 : ℝ) < (X a).card := by exact_mod_cast Finset.card_pos.mpr (hX a)
  have hstrict : δ ^ (-906 * κ) * ((X a).card : ℝ) < δ ^ (-θ) * ((X a).card : ℝ) :=
    mul_lt_mul_of_pos_right (Real.rpow_lt_rpow_of_exponent_gt hδ hδlt (by linarith)) hXp
  exact (not_le_of_gt hstrict) (hlower.trans hn)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
