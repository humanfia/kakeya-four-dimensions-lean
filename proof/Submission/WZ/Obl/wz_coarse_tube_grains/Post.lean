-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.Post.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.Prism
import Submission.WZ.Obl.wz_coarse_tube_grains.Geom

/-!
# From a prism family to the frozen grains

A `CellPrismFamily` (x0310, o019) for a refinement of the shading inside a thin carrier is
turned into the exact grains of the frozen statement: the shading is cut to the points where
it keeps a `δ^κ` share of the original multiplicity (which gives broadness relative to `ρ`),
the boxes are widened from `ρc/2` to `ρc` (`Geom.crossing_widen`), and they stay inside
`T ρ y w`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains

open Set Metric MeasureTheory
open scoped Classical

local notation "V" => LeanEval.Analysis.WangZahlKakeya.Space

theorem P_eq_box (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    RIS.Interfaces.P a b c z e = Geom.box a b c z e := rfl

theorem measurable_card {m : ℕ} {W : Fin m → Set V} (hW : ∀ i, MeasurableSet (W i)) :
    Measurable fun p => ((Finset.univ.filter fun i => p ∈ W i).card : ℝ) := by
  have h : (fun p => ((Finset.univ.filter fun i => p ∈ W i).card : ℝ)) =
      fun p => ∑ i, (W i).indicator (fun _ => (1 : ℝ)) p := by
    funext p
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p ∈ W i <;> simp [hp]
  rw [h]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hW i)

theorem ncard_eq_card {m : ℕ} (W : Fin m → Set V) (p : V) :
    (({i | p ∈ W i} : Set (Fin m)).ncard : ℝ) =
      ((Finset.univ.filter fun i => p ∈ W i).card : ℝ) := by
  have : ({i | p ∈ W i} : Set (Fin m)) = ↑(Finset.univ.filter fun i => p ∈ W i) := by
    ext i; simp
  rw [this, Set.ncard_coe_finset]

theorem mult_lower {m : ℕ} {W : Fin m → Set V} (hW : ∀ i, MeasurableSet (W i)) {k : ℕ}
    {A : Set V} (hA : MeasurableSet A)
    (hlev : ∀ p ∈ A, 2 ^ k ≤ (Finset.univ.filter fun i => p ∈ W i).card) :
    (2 ^ k : ENNReal) * volume A ≤ ∑ i, volume (W i ∩ A) := by
  rw [sum_volume_eq_lintegral (fun i => (hW i).inter hA), ← lintegral_indicator_const hA]
  apply lintegral_mono
  intro p
  dsimp only
  by_cases hp : p ∈ A
  · simp only [Set.indicator_of_mem hp]
    have hsub : (Finset.univ.filter fun i => p ∈ W i) ⊆
        (Finset.univ.filter fun i => p ∈ W i ∩ A) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hi, hp⟩
    calc (2 ^ k : ENNReal) ≤ ((Finset.univ.filter fun i => p ∈ W i).card : ENNReal) := by
          exact_mod_cast hlev p hp
      _ ≤ _ := by
          have h : ((Finset.univ.filter fun i => p ∈ W i).card : ENNReal) ≤
              ((Finset.univ.filter fun i => p ∈ W i ∩ A).card : ENNReal) := by
            exact_mod_cast Finset.card_le_card hsub
          convert h
  · simp only [Set.indicator_of_notMem hp]
    simp

theorem mult_upper {m : ℕ} {W : Fin m → Set V} (hW : ∀ i, MeasurableSet (W i)) {k : ℕ}
    (hlev : ∀ p ∈ ⋃ i, W i, (Finset.univ.filter fun i => p ∈ W i).card < 2 ^ (k + 1)) :
    ∑ i, volume (W i) ≤ (2 ^ (k + 1) : ENNReal) * volume (⋃ i, W i) := by
  have hU : MeasurableSet (⋃ i, W i) := MeasurableSet.iUnion hW
  rw [sum_volume_eq_lintegral hW, ← lintegral_indicator_const hU]
  apply lintegral_mono
  intro p
  dsimp only
  by_cases hp : p ∈ ⋃ i, W i
  · simp only [Set.indicator_of_mem hp]
    exact_mod_cast (hlev p hp).le
  · simp only [Set.indicator_of_notMem hp]
    have : (Finset.univ.filter fun i => p ∈ W i) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hp (Set.mem_iUnion.mpr ⟨i, h⟩)
    simp [this]

/-- The points where `W` keeps less than a `θ` share of the multiplicity of `Z` carry at
most a `θ` share of the mass of `Z`. -/
theorem bad_mass {m : ℕ} {Z W : Fin m → Set V} (hZ : ∀ i, MeasurableSet (Z i))
    (hW : ∀ i, MeasurableSet (W i)) {θ : ℝ} (hθ : 0 < θ) :
    ∑ i, volume (W i ∩ {p | θ * ((Finset.univ.filter fun i => p ∈ Z i).card : ℝ) <
        ((Finset.univ.filter fun i => p ∈ W i).card : ℝ)}ᶜ) ≤
      ENNReal.ofReal θ * ∑ i, volume (Z i) := by
  set B : Set V := {p | θ * ((Finset.univ.filter fun i => p ∈ Z i).card : ℝ) <
        ((Finset.univ.filter fun i => p ∈ W i).card : ℝ)}ᶜ with hB
  have hBm : MeasurableSet B :=
    (measurableSet_lt (measurable_const.mul (measurable_card hZ)) (measurable_card hW)).compl
  rw [sum_volume_eq_lintegral (fun i => (hW i).inter hBm), sum_volume_eq_lintegral hZ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro p
  dsimp only
  have key : ((Finset.univ.filter fun i => p ∈ W i ∩ B).card : ENNReal) ≤
      ENNReal.ofReal θ * ((Finset.univ.filter fun i => p ∈ Z i).card : ENNReal) := by
    by_cases hp : p ∈ B
    · have hle : ((Finset.univ.filter fun i => p ∈ W i).card : ℝ) ≤
          θ * ((Finset.univ.filter fun i => p ∈ Z i).card : ℝ) := by
        simp only [hB, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hp
        exact hp
      have hcard : (Finset.univ.filter fun i => p ∈ W i ∩ B) =
          (Finset.univ.filter fun i => p ∈ W i) := by
        ext i; simp [hp]
      rw [hcard, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul hθ.le]
      exact ENNReal.ofReal_le_ofReal hle
    · have hcard : (Finset.univ.filter fun i => p ∈ W i ∩ B) = ∅ := by
        ext i; simp [hp]
      rw [hcard, Finset.card_empty, Nat.cast_zero]
      exact zero_le
  convert key

theorem tb_isOpen (d : ℝ) (p u : V) : IsOpen (Tb d p u) := Metric.isOpen_thickening

theorem tb_convex (d : ℝ) (p u : V) : Convex ℝ (Tb d p u) :=
  (convex_segment p (p + u)).thickening d

theorem small_box_eq (δ ρ c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    RIS.Interfaces.P (16 * δ) (128 * (ρ / 256) * c) c z e =
      Geom.box (16 * δ) (ρ * c / 2) c z e := by
  rw [P_eq_box, show 128 * (ρ / 256) * c = ρ * c / 2 by ring]

/-- A box of half the middle width inside the thin carrier, widened, stays inside the
coarse tube. -/
theorem big_box_subset {δ ρ c : ℝ} (hρ : 0 < ρ) (hc4 : c ≤ 1 / 4) (hc : 0 ≤ c)
    {z y w y' w' : V} {e : V ≃ₗᵢ[ℝ] V}
    (hsmall : Geom.box (16 * δ) (ρ * c / 2) c z e ⊆ Tb (2 * (ρ / 256)) y' w')
    (hseg : segment ℝ y' (y' + w') ⊆ Tb (ρ / 2) y w) :
    Geom.box (16 * δ) (ρ * c) c z e ⊆ Tb ρ y w := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := Geom.halve_mid hp
  have hq' := hsmall (by simpa only [show ρ * c / 2 = ρ * c / 2 from rfl] using hq)
  obtain ⟨a, ha, hqa⟩ := mem_thickening_iff.mp hq'
  obtain ⟨b, hb, hab⟩ := mem_thickening_iff.mp (hseg ha)
  refine mem_thickening_iff.mpr ⟨b, hb, ?_⟩
  have h1 := dist_triangle4 p q a b
  have h2 : ρ * c / 4 ≤ ρ / 16 := by nlinarith
  linarith

set_option maxHeartbeats 1600000 in
/-- The frozen grains from a prism family in a thin carrier. -/
theorem grains_of_family {δ ρ c r ζ η κ ε Λ β : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ)
    (hc : 0 < c) (hc4 : c ≤ 1 / 4) (hκ : 0 < κ) (hΛ : 0 < Λ)
    (hηκ : η + κ ≤ ε) (hret : Λ * (δ ^ ε + δ ^ κ) ≤ 1) (hden1 : 4 * Λ * δ ^ κ ≤ 1)
    (hden2 : 4 * δ ^ ε ≤ δ ^ ζ)
    {m N : ℕ} {x v : Fin m → V} {Z Y' : Fin m → Set V} {C : Fin N → Set V} {q : Fin N → V}
    {y w y' w' : V}
    (hZm : ∀ i, MeasurableSet (Z i)) (hY'Z : ∀ i, Y' i ⊆ Z i)
    (hZT : ∀ i, Z i ⊆ Tb δ (x i) (v i))
    (hseg : segment ℝ y' (y' + w') ⊆ Tb (ρ / 2) y w) (hww : ‖w' - w‖ < 2 * ρ)
    (F : RIS.Interfaces.CellPrismFamily δ r (ρ / 256) c ζ x v Y' C q y' w')
    (hmass : ∑ i, volume (Z i) ≤ ENNReal.ofReal Λ * ∑ i, volume (F.shading i))
    (hbroad : ∀ (p u : V) (s : ℝ), ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        (({i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s} : Set (Fin m)).ncard : ℝ) ≤
          δ ^ (-η) * (s / ρ) ^ β * (({i | p ∈ Z i} : Set (Fin m)).ncard : ℝ)) :
    ∃ (Z' : Fin m → Set V) (mm : ℝ) (L : ℕ) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V)
      (G : Fin L → Set V),
      (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i) ∧
      ENNReal.ofReal (δ ^ ε) * ∑ i, volume (Z i) ≤ ∑ i, volume (Z' i) ∧
      (∀ (p u : V) (s : ℝ), ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        (({i | p ∈ Z' i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s} : Set (Fin m)).ncard : ℝ) ≤
          δ ^ (-ε) * (s / ρ) ^ β * (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ)) ∧
      (∀ p, (∃ i, p ∈ Z' i) →
        (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ) ∈ Set.Icc mm (2 * mm)) ∧
      (∀ j, MeasurableSet (G j) ∧ G j ⊆ Geom.box (16 * δ) (ρ * c) c (z j) (e j) ∧
        Geom.box (16 * δ) (ρ * c) c (z j) (e j) ⊆ Tb ρ y w ∧
        e j w 0 ^ 2 + e j w 1 ^ 2 ≤ (10 * ρ) ^ 2) ∧
      (∀ j j', j ≠ j' → Disjoint (G j) (G j')) ∧
      {p | ∃ j, p ∈ G j} = {p | ∃ i, p ∈ Z' i} ∧
      ENNReal.ofReal (δ ^ ε * L * (16 * δ) * (ρ * c) * c) ≤ ∑ j, volume (G j) ∧
      ∀ i j, (Z' i ∩ G j).Nonempty →
        Z' i ∩ Geom.box (16 * δ) (ρ * c) c (z j) (e j) ⊆ G j ∧
        (∀ p ∈ Tb δ (x i) (v i) ∩ frontier (Geom.box (16 * δ) (ρ * c) c (z j) (e j)),
          |e j (p - z j) 2| = c / 2) ∧
        ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
          ∃ p ∈ Tb δ (x i) (v i) ∩ Geom.box (16 * δ) (ρ * c) c (z j) (e j),
            e j (p - z j) 2 = t := by
  set W := F.shading with hW_def
  have hWm : ∀ i, MeasurableSet (W i) := fun i => (F.refines i).1
  have hWZ : ∀ i, W i ⊆ Z i := fun i => (F.refines i).2.trans (hY'Z i)
  have hWT : ∀ i, W i ⊆ Tb δ (x i) (v i) := fun i => (hWZ i).trans (hZT i)
  set θ : ℝ := δ ^ κ with hθ_def
  have hθ : 0 < θ := Real.rpow_pos_of_pos hδ κ
  set Good : Set V := {p | θ * ((Finset.univ.filter fun i => p ∈ Z i).card : ℝ) <
      ((Finset.univ.filter fun i => p ∈ W i).card : ℝ)} with hGood_def
  have hGoodm : MeasurableSet Good :=
    measurableSet_lt (measurable_const.mul (measurable_card hZm)) (measurable_card hWm)
  set Z' : Fin m → Set V := fun i => W i ∩ Good with hZ'_def
  have hZ'm : ∀ i, MeasurableSet (Z' i) := fun i => (hWm i).inter hGoodm
  -- finiteness
  have hZfin : ∀ i, volume (Z i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (RIS.tube_volume_ne_top δ (x i) (v i)) (measure_mono (hZT i))
  have hWfin : ∀ i, volume (W i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hZfin i) (measure_mono (hWZ i))
  -- the membership pattern on good points
  have hpat : ∀ p ∈ Good, ∀ i, p ∈ Z' i ↔ p ∈ W i := by
    intro p hp i
    simp only [hZ'_def, Set.mem_inter_iff]
    tauto
  -- mass
  have hbad := bad_mass hZm hWm hθ
  rw [← hGood_def] at hbad
  have hsplit : ∑ i, volume (W i) = ∑ i, volume (Z' i) + ∑ i, volume (W i ∩ Goodᶜ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hZ'_def]
    exact (measure_inter_add_diff (W i) hGoodm).symm
  have hZsum_fin : ∑ i, volume (Z i) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hZfin i
  have hWsum_fin : ∑ i, volume (W i) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hWfin i
  have hZ'sum_fin : ∑ i, volume (Z' i) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ =>
      ne_top_of_le_ne_top (hWfin i) (measure_mono Set.inter_subset_left)
  have hBsum_fin : ∑ i, volume (W i ∩ Goodᶜ) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ =>
      ne_top_of_le_ne_top (hWfin i) (measure_mono Set.inter_subset_left)
  -- real versions
  set A := (∑ i, volume (Z i)).toReal with hA_def
  set Bw := (∑ i, volume (W i)).toReal with hBw_def
  set Gz := (∑ i, volume (Z' i)).toReal with hGz_def
  set Bd := (∑ i, volume (W i ∩ Goodᶜ)).toReal with hBd_def
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hGz0 : 0 ≤ Gz := ENNReal.toReal_nonneg
  have hBd0 : 0 ≤ Bd := ENNReal.toReal_nonneg
  have hBw_eq : Bw = Gz + Bd := by
    rw [hBw_def, hsplit, ENNReal.toReal_add hZ'sum_fin hBsum_fin]
  have hBd_le : Bd ≤ θ * A := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZsum_fin) hbad
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] at this
  have hA_le : A ≤ Λ * Bw := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWsum_fin) hmass
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛ.le] at this
  have hret' : δ ^ ε * A ≤ Gz := by
    have h1 : A ≤ Λ * Gz + Λ * θ * A := by
      calc A ≤ Λ * Bw := hA_le
        _ = Λ * Gz + Λ * Bd := by rw [hBw_eq]; ring
        _ ≤ Λ * Gz + Λ * (θ * A) := by gcongr
        _ = Λ * Gz + Λ * θ * A := by ring
    have h2 : Λ * δ ^ ε * A ≤ Λ * Gz := by
      have : Λ * δ ^ ε + Λ * θ ≤ 1 := by rw [hθ_def]; linarith [hret]
      nlinarith
    have := le_of_mul_le_mul_left (by linarith [h2] : Λ * (δ ^ ε * A) ≤ Λ * Gz) hΛ
    exact this
  -- the multiplicity window
  have hlevel := F.uniform
  rw [← hW_def] at hlevel
  -- grains
  set L := F.count
  set z := F.centers
  set e := F.frames
  set G : Fin L → Set V := fun l => F.pieces l ∩ Good with hG_def
  have hpieces : ∀ l, F.pieces l ⊆ Geom.box (16 * δ) (ρ * c / 2) c (z l) (e l) := by
    intro l
    have := (F.piece_data l).2.1
    rwa [small_box_eq] at this
  have hsmallT : ∀ l, Geom.box (16 * δ) (ρ * c / 2) c (z l) (e l) ⊆ Tb (2 * (ρ / 256)) y' w' := by
    intro l
    have := (F.piece_data l).2.2.2.1
    rw [small_box_eq] at this
    exact this
  have hpieces_m : ∀ l, MeasurableSet (F.pieces l) := fun l => (F.piece_data l).1
  have hunion : (⋃ l, F.pieces l) = ⋃ i, W i := F.union_eq
  refine ⟨Z', 2 ^ F.level, L, z, e, G, fun i => ⟨hZ'm i, Set.inter_subset_left.trans (hWZ i)⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- mass retention
    rw [← ENNReal.ofReal_toReal hZsum_fin, ← ENNReal.ofReal_toReal hZ'sum_fin,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hret'
  · -- broadness
    have hfrac : ∀ p, (∃ i, p ∈ Z' i) →
        X48.q m {i | p ∈ Z i} ≤ θ⁻¹ * X48.q m {i | p ∈ Z' i} := by
      intro p ⟨i, hi⟩
      have hpG : p ∈ Good := hi.2
      have hset : ({i | p ∈ Z' i} : Set (Fin m)) = {i | p ∈ W i} := by
        ext j; exact hpat p hpG j
      show (({i | p ∈ Z i} : Set (Fin m)).ncard : ℝ) ≤
        θ⁻¹ * (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ)
      rw [hset, ncard_eq_card, ncard_eq_card]
      have h := hpG
      simp only [hGood_def, Set.mem_setOf_eq] at h
      rw [le_inv_mul_iff₀ hθ]
      exact h.le
    have hb := X48.broad_of_pointwise_fraction (δ := δ) (l := δ ^ (-η)) (K := θ⁻¹) hδ.le hρ
      (Real.rpow_nonneg hδ.le _) (fun i => Set.inter_subset_left.trans (hWZ i)) hfrac hbroad
    intro p u s hu hs hsρ
    refine (hb p u s hu hs hsρ).trans ?_
    have hK : θ⁻¹ * δ ^ (-η) ≤ δ ^ (-ε) := by
      rw [hθ_def, ← Real.rpow_neg hδ.le, ← Real.rpow_add hδ]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have h0 : 0 ≤ (s / ρ) ^ β * (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ) :=
      mul_nonneg (Real.rpow_nonneg (div_nonneg (hδ.le.trans hs) hρ.le) _) (Nat.cast_nonneg _)
    calc θ⁻¹ * δ ^ (-η) * (s / ρ) ^ β * (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ)
        = (θ⁻¹ * δ ^ (-η)) * ((s / ρ) ^ β * (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ)) := by
          ring
      _ ≤ δ ^ (-ε) * ((s / ρ) ^ β * (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ)) := by gcongr
      _ = δ ^ (-ε) * (s / ρ) ^ β * (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ) := by ring
  · -- multiplicity
    intro p ⟨i, hi⟩
    have hpG : p ∈ Good := hi.2
    have hpW : p ∈ ⋃ i, W i := Set.mem_iUnion.mpr ⟨i, hi.1⟩
    have hset : ({i | p ∈ Z' i} : Set (Fin m)) = {i | p ∈ W i} := by
      ext j; exact hpat p hpG j
    rw [hset, ncard_eq_card]
    obtain ⟨h1, h2⟩ := hlevel p hpW
    constructor
    · exact_mod_cast h1
    · have : ((Finset.univ.filter fun i => p ∈ W i).card : ℝ) < 2 ^ (F.level + 1) := by
        exact_mod_cast h2
      rw [pow_succ] at this
      linarith
  · -- the boxes
    intro l
    refine ⟨(hpieces_m l).inter hGoodm, Set.inter_subset_left.trans ((hpieces l).trans
      (Geom.box_mono_mid (by nlinarith) _ _)), big_box_subset hρ hc4 hc.le (hsmallT l) hseg, ?_⟩
    have hal := F.aligned l
    have hd : ‖w - w'‖ ≤ 2 * ρ := by rw [norm_sub_rev]; exact hww.le
    have h := Geom.axis_sq_le (e := e l) (A := 10 * (ρ / 256)) hal hd (by positivity)
    nlinarith
  · -- disjointness
    intro j j' hjj'
    exact (F.disjoint hjj').mono Set.inter_subset_left Set.inter_subset_left
  · -- union
    ext p
    simp only [Set.mem_setOf_eq, hG_def, Set.mem_inter_iff, hZ'_def]
    constructor
    · rintro ⟨l, hl, hg⟩
      have : p ∈ ⋃ l, F.pieces l := Set.mem_iUnion.mpr ⟨l, hl⟩
      rw [hunion] at this
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
      exact ⟨i, hi, hg⟩
    · rintro ⟨i, hi, hg⟩
      have : p ∈ ⋃ i, W i := Set.mem_iUnion.mpr ⟨i, hi⟩
      rw [← hunion] at this
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp this
      exact ⟨l, hl, hg⟩
  · -- density
    have hUW : MeasurableSet (⋃ i, W i) := MeasurableSet.iUnion hWm
    have hsumP : ∑ l, volume (F.pieces l) = volume (⋃ i, W i) := by
      rw [← hunion, measure_iUnion (fun j k hjk => F.disjoint hjk) hpieces_m, tsum_fintype]
    have hsumG : ∑ l, volume (G l) = volume ((⋃ i, W i) ∩ Good) := by
      rw [hG_def, ← hunion, Set.iUnion_inter, measure_iUnion
        (fun j k hjk => (F.disjoint hjk).mono Set.inter_subset_left Set.inter_subset_left)
        (fun l => (hpieces_m l).inter hGoodm), tsum_fintype]
    have hlow := mult_lower hWm (k := F.level) (hUW.inter hGoodm.compl)
      (fun p hp => (hlevel p hp.1).1)
    have hup := mult_upper hWm (k := F.level) (fun p hp => (hlevel p hp).2)
    have hbadsub : ∑ i, volume (W i ∩ ((⋃ i, W i) ∩ Goodᶜ)) ≤ ∑ i, volume (W i ∩ Goodᶜ) :=
      Finset.sum_le_sum fun i _ => measure_mono (Set.inter_subset_inter_right _
        Set.inter_subset_right)
    have hUfin : volume (⋃ i, W i) ≠ ⊤ :=
      ne_top_of_le_ne_top hWsum_fin (measure_iUnion_fintype_le _ _)
    set X := (volume (⋃ i, W i)).toReal with hX_def
    set Xg := (volume ((⋃ i, W i) ∩ Good)).toReal with hXg_def
    set Xb := (volume ((⋃ i, W i) ∩ Goodᶜ)).toReal with hXb_def
    have hgfin : volume ((⋃ i, W i) ∩ Good) ≠ ⊤ :=
      ne_top_of_le_ne_top hUfin (measure_mono Set.inter_subset_left)
    have hbfin : volume ((⋃ i, W i) ∩ Goodᶜ) ≠ ⊤ :=
      ne_top_of_le_ne_top hUfin (measure_mono Set.inter_subset_left)
    have hXsplit : X = Xg + Xb := by
      have h := measure_inter_add_diff (μ := volume) (⋃ i, W i) hGoodm
      rw [Set.diff_eq] at h
      rw [hX_def, ← h, ENNReal.toReal_add hgfin hbfin]
    have h2k : (0 : ℝ) < 2 ^ F.level := by positivity
    have hXb : 2 ^ F.level * Xb ≤ θ * A := by
      have := (hlow.trans hbadsub).trans hbad
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZsum_fin) this
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] at this
      simpa using this
    have hBwX : Bw ≤ 2 ^ (F.level + 1) * X := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hUfin) hup
      rw [ENNReal.toReal_mul] at this
      simpa using this
    have hXb' : Xb ≤ X / 2 := by
      have h1 : 2 ^ F.level * Xb ≤ θ * (Λ * (2 ^ (F.level + 1) * X)) :=
        hXb.trans (by
          have := mul_le_mul_of_nonneg_left (hA_le.trans (mul_le_mul_of_nonneg_left hBwX hΛ.le))
            hθ.le
          linarith)
      have h2 : θ * (Λ * (2 ^ (F.level + 1) * X)) = 2 ^ F.level * (2 * Λ * θ * X) := by
        rw [pow_succ]; ring
      rw [h2] at h1
      have h3 := le_of_mul_le_mul_left h1 h2k
      have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
      have : 2 * Λ * θ ≤ 1 / 2 := by rw [hθ_def]; linarith [hden1]
      nlinarith
    have hXg : X / 2 ≤ Xg := by linarith
    have hdens : ENNReal.ofReal (δ ^ ζ * F.count * (16 * δ * (128 * (ρ / 256) * c) * c)) ≤
        ∑ l, volume (F.pieces l) := F.density
    rw [hsumP] at hdens
    rw [hsumG, ← ENNReal.ofReal_toReal hgfin]
    apply ENNReal.ofReal_le_ofReal
    have hd := ENNReal.toReal_mono hUfin hdens
    rw [ENNReal.toReal_ofReal (by positivity)] at hd
    have hgoal : δ ^ ε * (L : ℝ) * (16 * δ) * (ρ * c) * c ≤
        δ ^ ζ * F.count * (16 * δ * (128 * (ρ / 256) * c) * c) / 2 := by
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      have hpos : 0 ≤ (L : ℝ) * (16 * δ) * (ρ * c) * c := by positivity
      have : δ ^ ζ * F.count * (16 * δ * (128 * (ρ / 256) * c) * c) / 2 =
          (δ ^ ζ / 4) * ((L : ℝ) * (16 * δ) * (ρ * c) * c) := by ring
      rw [this]
      calc δ ^ ε * (L : ℝ) * (16 * δ) * (ρ * c) * c
          = δ ^ ε * ((L : ℝ) * (16 * δ) * (ρ * c) * c) := by ring
        _ ≤ (δ ^ ζ / 4) * ((L : ℝ) * (16 * δ) * (ρ * c) * c) := by gcongr; linarith
    linarith
  · -- crossing
    intro i l ⟨p, hpZ', hpG⟩
    have hpW : p ∈ W i := hpZ'.1
    have hpP : p ∈ F.pieces l := hpG.1
    obtain ⟨hsub, hfr, hend⟩ := F.crossing i l ⟨p, hpW, hpP⟩
    rw [small_box_eq] at hsub hfr hend
    have hne : (Tb δ (x i) (v i) ∩ Geom.box (16 * δ) (ρ * c / 2) c (z l) (e l)).Nonempty :=
      ⟨p, hWT i hpW, hpieces l hpP⟩
    obtain ⟨hfr', hin⟩ := Geom.crossing_widen (tb_isOpen δ (x i) (v i)) (tb_convex δ (x i) (v i))
      hc (by nlinarith : ρ * c / 2 ≤ ρ * c) hne hfr
    refine ⟨?_, hfr', ?_⟩
    · intro p' ⟨hp'Z, hp'B⟩
      have hp'W : p' ∈ W i := hp'Z.1
      have hp'small := hin ⟨hWT i hp'W, hp'B⟩
      exact ⟨hsub ⟨hp'W, hp'small⟩, hp'Z.2⟩
    · intro t ht
      obtain ⟨p', ⟨hp'T, hp'B⟩, hp't⟩ := hend t ht
      exact ⟨p', ⟨hp'T, Geom.box_mono_mid (by nlinarith) _ _ hp'B⟩, hp't⟩

end WangZahlLot.Obl.wz_coarse_tube_grains
