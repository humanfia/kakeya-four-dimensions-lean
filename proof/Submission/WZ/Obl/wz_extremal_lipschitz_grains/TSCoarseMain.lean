-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TSCoarseMain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSCoarse
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSCount
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

/-!
# Coarse families: assembly

The covers of one separated level, contracted about the origin and re-extended,
are thinned by `select_frozen` into an exact separated family at eight times the
level scale. The fine family's balance and local convex counts at every coarser
level transfer to the coarse tubes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical
open WangZahlLot.Obl.wz_separated_cover_refinement
  (Tube Dilate CoverAt SeparatedAt enumerate enumerate_mem power_net exists_net_size)

/-- Arithmetic of the convex count transfer from fine to coarse tubes. -/
theorem frost_transfer {c A0 ρ'' R lam P Qc Bm G : ℝ} {W W' : Set Space}
    (hc : 1 ≤ c) (hA0 : 0 < A0) (hρ'' : 0 < ρ'') (hR0 : 0 ≤ R) (hR : R ≤ 2 * ρ'')
    (hlam : 1 / 2 ≤ lam) (hlam1 : lam ≤ 1) (hP : 0 ≤ P) (hG : 0 < G)
    (hQ : ENNReal.ofReal (Qc * ρ'' ^ 2) ≤ ENNReal.ofReal (c * Bm) * volume W')
    (hW' : volume W' = ENNReal.ofReal (lam⁻¹ ^ 3) * volume W)
    (hPQ : P * (A0 / c) ≤ Qc) (hB : Bm ≤ G * (c * A0)) (hBm : 0 ≤ Bm) :
    ENNReal.ofReal (P * R ^ 2) ≤ ENNReal.ofReal (32 * c ^ 3 * G) * volume W := by
  have hc0 : 0 < c := by linarith
  have hlam0 : 0 < lam := by linarith
  rcases eq_or_ne (volume W) ⊤ with hW | hW
  · rw [hW, ENNReal.mul_top (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
    exact le_top
  set V := (volume W).toReal
  have hV : volume W = ENNReal.ofReal V := (ENNReal.ofReal_toReal hW).symm
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  rw [hW', hV, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)] at hQ
  have hQr : Qc * ρ'' ^ 2 ≤ c * Bm * (lam⁻¹ ^ 3 * V) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hQ
  rw [hV, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hlinv : lam⁻¹ ^ 3 ≤ 8 := by
    have : lam⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hlam0 (by norm_num)]; linarith
    calc lam⁻¹ ^ 3 ≤ 2 ^ 3 := by
          exact pow_le_pow_left₀ (inv_nonneg.mpr hlam0.le) this 3
      _ = 8 := by norm_num
  have hlinv0 : 0 ≤ lam⁻¹ ^ 3 := by positivity
  have hR2 : R ^ 2 ≤ 4 * ρ'' ^ 2 := by nlinarith
  have hPQ' : P ≤ Qc * (c / A0) := by
    rw [div_eq_mul_inv] at hPQ ⊢
    have h := mul_le_mul_of_nonneg_right hPQ (show 0 ≤ c * A0⁻¹ by positivity)
    calc P = P * (A0 * c⁻¹) * (c * A0⁻¹) := by field_simp
      _ ≤ Qc * (c * A0⁻¹) := h
  calc P * R ^ 2 ≤ P * (4 * ρ'' ^ 2) := mul_le_mul_of_nonneg_left hR2 hP
    _ ≤ Qc * (c / A0) * (4 * ρ'' ^ 2) := mul_le_mul_of_nonneg_right hPQ' (by positivity)
    _ = 4 * (c / A0) * (Qc * ρ'' ^ 2) := by ring
    _ ≤ 4 * (c / A0) * (c * Bm * (lam⁻¹ ^ 3 * V)) :=
        mul_le_mul_of_nonneg_left hQr (by positivity)
    _ ≤ 4 * (c / A0) * (c * (G * (c * A0)) * (lam⁻¹ ^ 3 * V)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hB hc0.le
    _ = 4 * c ^ 3 * G * lam⁻¹ ^ 3 * V := by field_simp
    _ ≤ 4 * c ^ 3 * G * 8 * V := by
        apply mul_le_mul_of_nonneg_right _ hV0
        exact mul_le_mul_of_nonneg_left hlinv (by positivity)
    _ = 32 * c ^ 3 * G * V := by ring

theorem CoverAt.mono_const {δ K K' ρ : ℝ} {n : ℕ} {x v : Fin n → Space} {k : ℕ}
    {z w : Fin k → Space} (h : CoverAt δ K ρ x v z w) (hKK : K ≤ K') :
    CoverAt δ K' ρ x v z w := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · intro j j'
    exact (h5 j j').trans (mul_le_mul_of_nonneg_right hKK (Nat.cast_nonneg _))
  · intro j W hW
    exact (h6 j W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hKK (Nat.cast_nonneg _))) le_rfl)

/-- An exact separated cover gives one level of `Separated`. -/
theorem separated_level_of_cover {η δ ρ : ℝ} {n : ℕ} {x v : Fin n → Space} {k : ℕ}
    (hk : 0 < k) {z w : Fin k → Space}
    (hC : CoverAt δ (δ ^ (-η)) ρ x v z w) (hS : SeparatedAt δ ρ x v z w) :
    ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space,
      (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (tube ρ (z j) (w j) ∩ tube ρ (z j') (w j')) ≤
        (1 / 2 : ℝ≥0∞) * volume (tube ρ (z j) (w j))) ∧
      (∀ i, ∃! j, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)) ∧
      (∀ j, ∃ i, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)) ∧
      (∀ j j', ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ) ≤
        δ ^ (-η) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j') (w j')}.ncard : ℝ)) ∧
      (∀ j, ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧
          tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) *
          ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ)) * volume W) ∧
      (∀ i j j', tube δ (x i) (v i) ⊆ dilatedTube ρ (z j) (w j) →
        tube δ (x i) (v i) ⊆ dilatedTube ρ (z j') (w j') → j = j') :=
  ⟨k, hk, z, w, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1, hC.2.2.2.2.2, hS⟩

/-- The level-`ρ` covers of a separated family, normalized and thinned, form an
exact separated family at scale `8ρ`, keeping a fixed fraction of any weight. -/
theorem coarse_family {η δ ρ η' t Mw : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hη : 0 < η)
    {n : ℕ} {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) (hS : Separated η δ n x v)
    {k : ℕ} {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1)
    (hsepρ : ∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube ρ (z j) (w j)))
    (huniq : ∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j))
    (hfull : ∀ j, ∃ i, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j))
    (hbalρ : ∀ j j', ({i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)}.ncard : ℝ) ≤
      δ ^ (-η) * ({i | Tube δ (x i) (v i) ⊆ Tube ρ (z j') (w j')}.ncard : ℝ))
    (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1 / 10 ^ 12)
    (hP1a : 8 * δ ^ (-(2 * η)) ≤ (8 * ρ) ^ (-η'))
    (hP1b : (8 * ρ) ^ η' ≤ δ ^ (2 * η) / (4 * 10 ^ 9))
    (hP2 : 32 * (δ ^ (-η)) ^ 3 / t ≤ (8 * ρ) ^ (-η'))
    (ht : 0 < t) (ω : Fin k → ℝ) (hω0 : ∀ j, 0 ≤ ω j) (hωM : ∀ j, ω j ≤ Mw) (hMw : 0 < Mw) :
    ∃ Q : Finset (Fin k),
      (∀ j ∈ Q, ∀ j' ∈ Q, j ≠ j' →
        volume (ntube (8 * ρ) (16 * ρ) (z j) (w j) ∩ ntube (8 * ρ) (16 * ρ) (z j') (w j')) ≤
          (1 / 2 : ℝ≥0∞) * volume (ntube (8 * ρ) (16 * ρ) (z j) (w j))) ∧
      (Q.Nonempty → Separated η' (8 * ρ) Q.card
        (fun a => (1 - 2 * (16 * ρ)) • z (enumerate Q a) - (16 * ρ) • w (enumerate Q a))
        (fun a => w (enumerate Q a))) ∧
      (∑ j, ω j) / ((bigBound + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) -
        Mw * t * (((⌈η⁻¹⌉₊ + 3 : ℕ) : ℝ) * k) ≤ ∑ j ∈ Q, ω j := by
  classical
  set e : ℝ := 16 * ρ with he_def
  set lam : ℝ := 1 - 2 * e with hlam_def
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hδ1' : δ < 1 := by linarith
  have he0 : 0 ≤ e := by positivity
  have hlam : 1 / 2 ≤ lam := by
    simp only [hlam_def, he_def]
    have : ρ ≤ 1 / 10 ^ 12 := hρ
    norm_num at this ⊢
    linarith
  -- fine-to-coarse assignment
  choose fc hfc using fun i => (huniq i).exists
  have hfcu : ∀ i j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) → j = fc i :=
    fun i j h => (huniq i).unique h (hfc i)
  choose rep hrep using hfull
  have hfcrep : ∀ j, fc (rep j) = j := fun j => (hfcu (rep j) j (hrep j)).symm
  -- axes of coarse covers stay near the unit ball
  have hzax : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, ‖z j + t • w j‖ ≤ 2 := by
    intro j t ht
    have h := cover_axis_norm_le hδ hδ1' (by linarith) (hv (rep j)) (hw j) (hball (rep j))
      (hrep j) t ht
    linarith
  -- the net of scales
  set N : ℕ := ⌈η⁻¹⌉₊ with hN_def
  have hN : 0 < N := Nat.ceil_pos.mpr (inv_pos.mpr hη)
  have hgap : (N : ℝ)⁻¹ ≤ η := by
    rw [inv_le_comm₀ (by exact_mod_cast hN) hη]
    exact Nat.le_ceil _
  obtain ⟨s, hs, hnet⟩ := power_net hδ hδ1'.le hN hgap
  -- the fine levels at the net scales (enlarged to at least `32ρ`)
  have hlev := fun l : Fin (N + 1) =>
    hS (max (s l) (32 * ρ)) (le_max_of_le_left (hs l).1)
      (max_le (hs l).2 (by linarith))
  choose ρ'' hρ''lo hρ''1 hρ''hi k'' hk'' z'' w'' hw'' hsep'' huniq'' hfull'' hbal''
    hfrost'' hdil'' using hlev
  have hρρ'' : ∀ l, 32 * ρ ≤ ρ'' l := fun l => (le_max_right _ _).trans (hρ''lo l)
  choose lc hlc using fun l i => (huniq'' l i).exists
  have hlcu : ∀ l i m, Tube δ (x i) (v i) ⊆ Tube (ρ'' l) (z'' l m) (w'' l m) → m = lc l i :=
    fun l i m h => (huniq'' l i).unique h (hlc l i)
  -- tree property: fine tubes of one coarse tube share their cover at every level
  have htree : ∀ l i, lc l i = lc l (rep (fc i)) := by
    intro l i
    have hd := subset_dilate_of_same_coarse hδ hδρ (by linarith [hρρ'' l]) (hv (rep (fc i)))
      (hw (fc i)) (hrep (fc i)) (hfc i) (hlc l (rep (fc i)))
    exact hdil'' l i _ _ ((hlc l i).trans (tube_subset_dilate _ _ _)) hd
  -- the balance constant of the fine family
  set c : ℝ := δ ^ (-η) with hc_def
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1'.le (by linarith)
  have hc0 : 0 < c := by linarith
  -- fibres of `fc` are the coarse containment sets
  have hfcset : ∀ j, {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} =
      (Finset.univ.filter (fun i => fc i = j) : Set (Fin n)) := by
    intro j
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact (hfcu i j h).symm
    · intro h; rw [← h]; exact hfc i
  have hA : ∀ j j', ((Finset.univ.filter (fun i => fc i = j)).card : ℝ) ≤
      c * (Finset.univ.filter (fun i => fc i = j')).card := by
    intro j j'
    have h := hbalρ j j'
    rwa [hfcset j, hfcset j', Set.ncard_coe_finset, Set.ncard_coe_finset] at h
  have hlcset : ∀ l m, {i | tube δ (x i) (v i) ⊆ tube (ρ'' l) (z'' l m) (w'' l m)} =
      (Finset.univ.filter (fun i => lc l (rep (fc i)) = m) : Set (Fin n)) := by
    intro l m
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    rw [← htree l i]
    constructor
    · intro h; exact (hlcu l i m h).symm
    · intro h; rw [← h]; exact hlc l i
  -- regular levels and the top level as cover systems
  set c0 : ℝ := 1 / 10 ^ 9 with hc0_def
  let Λr := {l : Fin (N + 1) // ρ'' l ≤ c0}
  let u0 : Space := EuclideanSpace.single 0 1
  have hu0 : ‖u0‖ = 1 := by simp [u0]
  let Lr : Λr → CoverSys k := fun l =>
    { k := k'' l.1, ρ := ρ'' l.1 + 27 * ρ,
      z := fun m => (1 - 2 * e) • z'' l.1 m - e • w'' l.1 m,
      w := fun m => w'' l.1 m,
      f := fun j => lc l.1 (rep j),
      conf := coverConflict (8 * ρ) e (ρ'' l.1 + 27 * ρ) z w (z'' l.1) (w'' l.1) }
  let Ltop : CoverSys k :=
    { k := 1, ρ := 1, z := fun _ => -(1 / 2 : ℝ) • u0, w := fun _ => u0,
      f := fun _ => 0, conf := fun _ _ => False }
  let L : Λr ⊕ Unit → CoverSys k := Sum.elim Lr (fun _ => Ltop)
  let xE : Fin k → Space := fun j => (1 - 2 * e) • z j - e • w j
  have hsmall2e : 2 * e < 1 := by
    simp only [he_def]; have : ρ ≤ 1 / 10 ^ 12 := hρ; norm_num at this ⊢; linarith
  -- coarse tubes lie in the unit ball
  have hTball : ∀ j, Tube (8 * ρ) (xE j) (w j) ⊆ ball 0 1 := by
    intro j
    apply ntube_subset_ball he0 hsmall2e (hw j) (R := 1 + 3 * ρ)
    · intro t ht
      exact cover_axis_norm_le hδ hδ1' (by linarith) (hv (rep j)) (hw j) (hball (rep j))
        (hrep j) t ht
    · simp only [he_def]
      nlinarith
  have hball_top : ball (0 : Space) 1 ⊆ Tube 1 (-(1 / 2 : ℝ) • u0) u0 := by
    intro p hp
    apply mem_Tube_of_param (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    have : p - (-(1 / 2 : ℝ) • u0 + (1 / 2 : ℝ) • u0) = p := by module
    rw [this]
    simpa using hp
  -- axes of the level covers stay near the unit ball
  have hz'' : ∀ (l : Λr) m, ∀ t ∈ Icc (0 : ℝ) 1, ‖z'' l.1 m + t • w'' l.1 m‖ ≤ 2 := by
    intro l m t ht
    obtain ⟨i, hi⟩ := hfull'' l.1 m
    have hl : ρ'' l.1 ≤ 1 / 10 ^ 9 := l.2
    have h := cover_axis_norm_le hδ hδ1' (by linarith) (hv i) (hw'' l.1 m) (hball i) hi t ht
    linarith
  -- the hypotheses of the selection
  have hf : ∀ l j, Tube (8 * ρ) (xE j) (w j) ⊆
      Tube (L l).ρ ((L l).z ((L l).f j)) ((L l).w ((L l).f j)) := by
    rintro (l | u) j
    · change ntube (8 * ρ) e (z j) (w j) ⊆
        ntube (ρ'' l.1 + 27 * ρ) e (z'' l.1 (lc l.1 (rep j))) (w'' l.1 (lc l.1 (rep j)))
      apply ntube_subset_ntube he0 hsmall2e
        (coarse_axis_close hδ (hv (rep j)) (hw j) (hrep j) (hlc l.1 (rep j))) (hw j)
      simp only [he_def]; linarith
    · exact (hTball j).trans hball_top
  have hcEdeg : ∀ j, (Finset.univ.filter (elemConflict (8 * ρ) e z w j)).card <
      bigBound + 1 := by
    intro j
    have := elemConflict_card_le hρ0 (by linarith) he0 (by linarith) (by simp only [he_def]; linarith)
      z w hw hzax hsepρ j
    omega
  have hcC : ∀ l {m m'}, (L l).conf m m' → (L l).conf m' m := by
    rintro (l | u) m m' h
    · exact coverConflict_symm h
    · exact h
  have hcCdeg : ∀ l m, (Finset.univ.filter ((L l).conf m)).card < bigBound + 1 := by
    rintro (l | u) m
    · have hl : ρ'' l.1 ≤ 1 / 10 ^ 9 := l.2
      have := coverConflict_card_le hρ0 (by linarith [hρρ'' l.1]) (by norm_num at hl ⊢; linarith)
        he0 (by simp only [he_def]; linarith) z w (z'' l.1) (w'' l.1) hw (hw'' l.1)
        (hz'' l) (hsep'' l.1) m
      change (Finset.univ.filter (coverConflict (8 * ρ) e (ρ'' l.1 + 27 * ρ) z w
        (z'' l.1) (w'' l.1) m)).card < bigBound + 1
      omega
    · have hempty : Finset.univ.filter ((L (Sum.inr u)).conf m) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun _ _ h => h)
      rw [hempty]
      simp
  have hunit : ∀ l m, ‖(L l).w m‖ = 1 := by
    rintro (l | u) m
    · exact hw'' l.1 m
    · exact hu0
  have hC : ∀ l m m', (∃ i, (L l).f i = m) → (∃ i, (L l).f i = m') → m ≠ m' →
      ¬(L l).conf m m' →
      volume (Tube (L l).ρ ((L l).z m) ((L l).w m) ∩ Tube (L l).ρ ((L l).z m') ((L l).w m')) ≤
        (1 / 2 : ℝ≥0∞) * volume (Tube (L l).ρ ((L l).z m) ((L l).w m)) := by
    rintro (l | u) m m' - - hne hnc
    · by_contra hlt
      push Not at hlt
      exact hnc ⟨hne, Or.inl hlt⟩
    · have h1 : (m : ℕ) < 1 := m.isLt
      have h2 : (m' : ℕ) < 1 := m'.isLt
      exact absurd (Fin.ext (by omega)) hne
  have hsep : ∀ l j m m', (∃ i, (L l).f i = m) → (∃ i, (L l).f i = m') →
      Tube (8 * ρ) (xE j) (w j) ⊆ Dilate (L l).ρ ((L l).z m) ((L l).w m) →
      Tube (8 * ρ) (xE j) (w j) ⊆ Dilate (L l).ρ ((L l).z m') ((L l).w m') →
        m = m' ∨ (L l).conf m m' := by
    rintro (l | u) j m m' - - h1 h2
    · by_cases hmm : m = m'
      · exact Or.inl hmm
      · exact Or.inr ⟨hmm, Or.inr (Or.inr ⟨j, h1, h2⟩)⟩
    · have h1 : (m : ℕ) < 1 := m.isLt
      have h2 : (m' : ℕ) < 1 := m'.isLt
      exact Or.inl (Fin.ext (by omega))
  -- balance of coarse fibres
  have hK : (1 : ℝ) ≤ 32 * c ^ 3 := by
    have : 1 ≤ c ^ 3 := one_le_pow₀ hc1
    linarith
  have hbal : ∀ l j1 j2, ((Finset.univ.filter (fun a => (L l).f a = (L l).f j1)).card : ℝ) ≤
      32 * c ^ 3 * (Finset.univ.filter (fun a => (L l).f a = (L l).f j2)).card := by
    rintro (l | u) j1 j2
    · have hB : ∀ m m', ((Finset.univ.filter (fun i => lc l.1 (rep (fc i)) = m)).card : ℝ) ≤
          c * (Finset.univ.filter (fun i => lc l.1 (rep (fc i)) = m')).card := by
        intro m m'
        have h := hbal'' l.1 m m'
        rwa [hlcset l.1 m, hlcset l.1 m', Set.ncard_coe_finset, Set.ncard_coe_finset] at h
      have h := coarse_fibre_balance fc (fun j => lc l.1 (rep j)) hc0 hA hB
        (fun j => ⟨rep j, hfcrep j⟩) j1 j2
      calc _ ≤ c ^ 3 * ((Finset.univ.filter
            (fun a => lc l.1 (rep a) = lc l.1 (rep j2))).card : ℝ) := h
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          have : 0 ≤ c ^ 3 := by positivity
          linarith
    · change ((Finset.univ.filter (fun a : Fin k => (0 : Fin 1) = 0)).card : ℝ) ≤
        32 * c ^ 3 * (Finset.univ.filter (fun a : Fin k => (0 : Fin 1) = 0)).card
      have h0 : (0 : ℝ) ≤ ((Finset.univ.filter (fun a : Fin k => (0 : Fin 1) = 0)).card : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
  -- convex counts of coarse fibres
  have hlam0 : 0 < lam := by linarith
  have hsmulvol : ∀ W : Set Space, volume (lam⁻¹ • W) = ENNReal.ofReal (lam⁻¹ ^ 3) * volume W := by
    intro W
    rw [Measure.addHaar_smul, finrank_euclideanSpace_fin,
      abs_of_pos (pow_pos (inv_pos.mpr hlam0) 3)]
  have hcontract : ∀ (W : Set Space) i, Tube (8 * ρ) (xE (fc i)) (w (fc i)) ⊆ W →
      Tube δ (x i) (v i) ⊆ lam⁻¹ • W := by
    intro W i hW p hp
    have hp' : lam • p ∈ W := by
      apply hW
      have := smul_mem_ntube (r := 8 * ρ) he0 hsmall2e
        (by nlinarith : (1 - 2 * e) * ρ ≤ 8 * ρ) ((hfc i) hp)
      exact this
    refine ⟨lam • p, hp', ?_⟩
    simp only [smul_smul, inv_mul_cancel₀ hlam0.ne', one_smul]
  have hfrost : ∀ l j1 (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (((Finset.univ.filter (fun a => (L l).f a = (L l).f j1 ∧
          Tube (8 * ρ) (xE a) (w a) ⊆ W)).card : ℝ) * (L l).ρ ^ 2) ≤
        ENNReal.ofReal (32 * c ^ 3 *
          (Finset.univ.filter (fun a => (L l).f a = (L l).f j1)).card) * volume W := by
    rintro (l | u) j1 W hW
    · set g : Fin k → Fin (k'' l.1) := fun j => lc l.1 (rep j) with hg_def
      have hW' : Convex ℝ (lam⁻¹ • W) := hW.smul _
      have hQ := hfrost'' l.1 (g j1) (lam⁻¹ • W) hW'
      have hset2 : {i | tube δ (x i) (v i) ⊆ tube (ρ'' l.1) (z'' l.1 (g j1)) (w'' l.1 (g j1)) ∧
          tube δ (x i) (v i) ⊆ lam⁻¹ • W} =
          (Finset.univ.filter (fun i => g (fc i) = g j1 ∧ Tube δ (x i) (v i) ⊆ lam⁻¹ • W) :
            Set (Fin n)) := by
        ext i
        have hmem := Set.ext_iff.mp (hlcset l.1 (g j1)) i
        simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and] at hmem ⊢
        rw [hmem]
        exact Iff.rfl
      rw [hset2, hlcset l.1 (g j1), Set.ncard_coe_finset, Set.ncard_coe_finset] at hQ
      have hPQ := coarse_count_le fc hc0 hA j1 (fun j => g j = g j1 ∧ Tube (8 * ρ) (xE j) (w j) ⊆ W)
        (fun i => g (fc i) = g j1 ∧ Tube δ (x i) (v i) ⊆ lam⁻¹ • W)
        (fun i hi => ⟨hi.1, hcontract W i hi.2⟩)
      have hB := fine_count_le fc hA j1 (fun j => g j = g j1)
      have hA0 : (0 : ℝ) < (Finset.univ.filter (fun i => fc i = j1)).card := by
        have : (Finset.univ.filter (fun i => fc i = j1)).Nonempty :=
          ⟨rep j1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfcrep j1⟩⟩
        exact_mod_cast Finset.card_pos.mpr this
      have hG : (0 : ℝ) < (Finset.univ.filter (fun j => g j = g j1)).card := by
        have : (Finset.univ.filter (fun j => g j = g j1)).Nonempty :=
          ⟨j1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        exact_mod_cast Finset.card_pos.mpr this
      have hρ''l : 0 < ρ'' l.1 := by linarith [hρρ'' l.1]
      have h := frost_transfer hc1 hA0 hρ''l (R := ρ'' l.1 + 27 * ρ) (by positivity)
        (by linarith [hρρ'' l.1]) hlam (by linarith) (Nat.cast_nonneg _) hG hQ
        (hsmulvol W) hPQ hB (Nat.cast_nonneg _)
      exact h
    · have hW' : Convex ℝ (lam⁻¹ • W) := hW.smul _
      have hn0 : 0 < n := Fin.pos (rep j1)
      have hQ := Separated.global_frostman hS hδ hδ1'.le hn0 hball (lam⁻¹ • W) hW'
      have hset : {i | tube δ (x i) (v i) ⊆ lam⁻¹ • W} =
          (Finset.univ.filter (fun i => Tube δ (x i) (v i) ⊆ lam⁻¹ • W) : Set (Fin n)) := by
        ext i; simp [tube]
      rw [hset, Set.ncard_coe_finset] at hQ
      have hPQ := coarse_count_le fc hc0 hA j1
        (fun j => (0 : Fin 1) = 0 ∧ Tube (8 * ρ) (xE j) (w j) ⊆ W)
        (fun i => Tube δ (x i) (v i) ⊆ lam⁻¹ • W) (fun i hi => hcontract W i hi.2)
      have hB := fine_count_le fc hA j1 (fun _ => (0 : Fin 1) = 0)
      have hA0 : (0 : ℝ) < (Finset.univ.filter (fun i => fc i = j1)).card := by
        have : (Finset.univ.filter (fun i => fc i = j1)).Nonempty :=
          ⟨rep j1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfcrep j1⟩⟩
        exact_mod_cast Finset.card_pos.mpr this
      have hG : (0 : ℝ) < (Finset.univ.filter (fun j : Fin k => (0 : Fin 1) = 0)).card := by
        have : (Finset.univ.filter (fun j : Fin k => (0 : Fin 1) = 0)).Nonempty :=
          ⟨j1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        exact_mod_cast Finset.card_pos.mpr this
      have hnB : ((Finset.univ.filter (fun i : Fin n => (0 : Fin 1) = 0)).card : ℝ) = n := by
        simp
      rw [hnB] at hB
      have hQ' : ENNReal.ofReal (((Finset.univ.filter
          (fun i => Tube δ (x i) (v i) ⊆ lam⁻¹ • W)).card : ℝ) * 1 ^ 2) ≤
          ENNReal.ofReal (c * (n : ℝ)) * volume (lam⁻¹ • W) := by
        rw [one_pow, mul_one]; exact hQ
      have h := frost_transfer hc1 hA0 one_pos (R := 1) zero_le_one (by norm_num) hlam
        (by linarith) (Nat.cast_nonneg _) hG hQ' (hsmulvol W) hPQ hB (Nat.cast_nonneg _)
      exact h
  -- the selection
  obtain ⟨Q, hQE, hQC, hQmass⟩ := select_frozen_sys (Nat.succ_pos bigBound) (s := 8 * ρ)
    (K := 32 * c ^ 3) xE w L hf (elemConflict (8 * ρ) e z w) elemConflict_symm hcEdeg hcC
    hcCdeg hunit hC hsep hbal hfrost ω hωM hMw ht
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro j hj j' hj' hne
    have hnc := hQE j hj j' hj' hne
    by_contra hlt
    push Not at hlt
    exact hnc ⟨hne, Or.inl hlt⟩
  · intro hQne r' hr' hr'1
    have h8ρ : 0 < 8 * ρ := by positivity
    set u := max r' (32 * ρ) with hu_def
    have hu4 : u ≤ 4 * r' := max_le (by linarith) (by linarith)
    have hδu : δ ≤ u := le_max_of_le_right (by linarith)
    have hu1 : u ≤ 1 := max_le hr'1 (by linarith)
    obtain ⟨l, hl1, hl2⟩ := hnet u hδu hu1
    have hsl : max (s l) (32 * ρ) = s l := max_eq_left ((le_max_right _ _).trans hl1)
    have hρ''u : ρ'' l ≤ δ ^ (-(2 * η)) * u := by
      have h1 := hρ''hi l
      rw [hsl] at h1
      calc ρ'' l ≤ δ ^ (-η) * s l := h1
        _ ≤ δ ^ (-η) * (δ ^ (-η) * u) := mul_le_mul_of_nonneg_left hl2 (by positivity)
        _ = δ ^ (-(2 * η)) * u := by
          rw [← mul_assoc, ← Real.rpow_add hδ]; ring_nf
    have hr'ρ'' : r' ≤ ρ'' l := by
      calc r' ≤ u := le_max_left _ _
        _ ≤ s l := hl1
        _ ≤ ρ'' l := by rw [← hsl]; exact hρ''lo l
    have hKt : 32 * c ^ 3 / t ≤ (8 * ρ) ^ (-η') := hP2
    by_cases hreg : ρ'' l ≤ c0
    · obtain ⟨k', hk', z', w', hcov, hsepQ⟩ := hQC hQne (Sum.inl ⟨l, hreg⟩)
      refine ⟨ρ'' l + 27 * ρ, by linarith, ?_, ?_,
        separated_level_of_cover hk' (CoverAt.mono_const hcov hKt) hsepQ⟩
      · have : ρ'' l ≤ 1 / 10 ^ 9 := hreg
        norm_num at this ⊢; linarith
      · have h2 : ρ'' l + 27 * ρ ≤ 2 * ρ'' l := by linarith [hρρ'' l]
        calc ρ'' l + 27 * ρ ≤ 2 * ρ'' l := h2
          _ ≤ 2 * (δ ^ (-(2 * η)) * u) := by linarith
          _ ≤ 2 * (δ ^ (-(2 * η)) * (4 * r')) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_left hu4 (by positivity)
          _ = (8 * δ ^ (-(2 * η))) * r' := by ring
          _ ≤ (8 * ρ) ^ (-η') * r' := mul_le_mul_of_nonneg_right hP1a (by linarith)
    · obtain ⟨k', hk', z', w', hcov, hsepQ⟩ := hQC hQne (Sum.inr ())
      refine ⟨1, hr'1, le_rfl, ?_, separated_level_of_cover hk' (CoverAt.mono_const hcov hKt) hsepQ⟩
      push Not at hreg
      have hlow : δ ^ (2 * η) / (4 * 10 ^ 9) ≤ r' := by
        have h1 : c0 < δ ^ (-(2 * η)) * (4 * r') :=
          hreg.trans_le (hρ''u.trans (mul_le_mul_of_nonneg_left hu4 (by positivity)))
        have hpos : 0 < δ ^ (2 * η) := by positivity
        have hinv : δ ^ (-(2 * η)) * δ ^ (2 * η) = 1 := by
          rw [← Real.rpow_add hδ]; simp
        rw [div_le_iff₀ (by norm_num)]
        have := mul_lt_mul_of_pos_right h1 hpos
        simp only [hc0_def] at this
        nlinarith
      have hpow : (8 * ρ) ^ (-η') * (8 * ρ) ^ η' = 1 := by
        rw [← Real.rpow_add h8ρ]; simp
      have hpos' : 0 ≤ (8 * ρ) ^ (-η') := by positivity
      calc (1 : ℝ) = (8 * ρ) ^ (-η') * (8 * ρ) ^ η' := hpow.symm
        _ ≤ (8 * ρ) ^ (-η') * r' :=
          mul_le_mul_of_nonneg_left (hP1b.trans hlow) hpos'
  · -- mass
    have hB1 : (1 : ℝ) ≤ ((bigBound + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos bigBound
    have hcardΛ : Fintype.card (Λr ⊕ Unit) + 1 ≤ ⌈η⁻¹⌉₊ + 3 := by
      rw [Fintype.card_sum, Fintype.card_unit]
      have : Fintype.card Λr ≤ N + 1 := by
        calc Fintype.card Λr ≤ Fintype.card (Fin (N + 1)) := Fintype.card_subtype_le _
          _ = N + 1 := Fintype.card_fin _
      omega
    have hsum0 : 0 ≤ ∑ j, ω j := Finset.sum_nonneg (fun j _ => hω0 j)
    have hpowle : ((bigBound + 1 : ℕ) : ℝ) ^ (Fintype.card (Λr ⊕ Unit) + 1) ≤
        ((bigBound + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) := pow_le_pow_right₀ hB1 hcardΛ
    have hdiv : (∑ j, ω j) / ((bigBound + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) ≤
        (∑ j, ω j) / ((bigBound + 1 : ℕ) : ℝ) ^ (Fintype.card (Λr ⊕ Unit) + 1) :=
      div_le_div_of_nonneg_left hsum0 (by positivity) hpowle
    have hloss : Mw * t * (((Fintype.card (Λr ⊕ Unit) + 1 : ℕ) : ℝ) * k) ≤
        Mw * t * (((⌈η⁻¹⌉₊ + 3 : ℕ) : ℝ) * k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hcardΛ
    linarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
