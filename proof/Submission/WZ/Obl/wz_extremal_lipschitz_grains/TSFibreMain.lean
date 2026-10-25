-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TSFibreMain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSFibre
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSCoarseMain

/-!
# Rescaled fibres as exact frozen families

The fine tubes of one coarse tube, oriented along the coarse direction, rescaled
anisotropically and extended to unit length, are thinned by `select_frozen` into
an exact separated family at scale `b a δ`. Each rescaled tube contains the image
of its original tube, so shadings and convex counts transfer.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical RealInnerProductSpace
open WangZahlLot.Obl.wz_separated_cover_refinement
  (Tube Dilate CoverAt SeparatedAt enumerate enumerate_mem enumerate_injective
    enumerate_surjective enumerate_count enumerate_sum ncard_setOf power_net)

/-- Finer covers containing a fibre tube contain only fibre tubes. -/
theorem fibre_tree {δ ρ ρ'' : ℝ} (hδ : 0 < δ) (hδρ'' : δ ≤ ρ'') (hρ''ρ : ρ'' ≤ ρ)
    {n k : ℕ} {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1)
    {z w : Fin k → Space} (fc : Fin n → Fin k)
    (hfc : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (z (fc i)) (w (fc i)))
    (hdil : ∀ i j j', Tube δ (x i) (v i) ⊆ Dilate ρ (z j) (w j) →
      Tube δ (x i) (v i) ⊆ Dilate ρ (z j') (w j') → j = j')
    {z'' w'' : Space} (hw'' : ‖w''‖ = 1) {i i' : Fin n}
    (hi : Tube δ (x i) (v i) ⊆ Tube ρ'' z'' w'') (hi' : Tube δ (x i') (v i') ⊆ Tube ρ'' z'' w'') :
    fc i' = fc i := by
  have hd := subset_dilate_of_same_coarse hδ hδρ'' hρ''ρ (hv i) hw'' hi hi' (hfc i)
  exact hdil i' _ _ ((hfc i').trans (tube_subset_dilate _ _ _)) hd

/-- Arithmetic of the convex count transfer under a rescaling with Jacobian `J`. -/
theorem frost_resc {c J ρ'' R K P Qc Bm : ℝ} {W W' : Set Space}
    (hc : 0 < c) (hJ : 0 < J) (hρ'' : 0 < ρ'') (hP : 0 ≤ P) (hPQ : P ≤ Qc) (hBm : 0 < Bm)
    (hK : 0 < K) (hRK : R ^ 2 * c ≤ K * ρ'' ^ 2 * J)
    (hQ : ENNReal.ofReal (Qc * ρ'' ^ 2) ≤ ENNReal.ofReal (c * Bm) * volume W')
    (hvol : ENNReal.ofReal J * volume W' = volume W) :
    ENNReal.ofReal (P * R ^ 2) ≤ ENNReal.ofReal (K * Bm) * volume W := by
  rcases eq_or_ne (volume W) ⊤ with hW | hW
  · rw [hW, ENNReal.mul_top (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
    exact le_top
  have hW' : volume W' ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by simp [hJ])] at hvol; exact hW hvol.symm
  set V' := (volume W').toReal
  have hV' : volume W' = ENNReal.ofReal V' := (ENNReal.ofReal_toReal hW').symm
  have hV'0 : 0 ≤ V' := ENNReal.toReal_nonneg
  rw [hV', ← ENNReal.ofReal_mul (by positivity)] at hQ
  have hQr : Qc * ρ'' ^ 2 ≤ c * Bm * V' :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hQ
  rw [← hvol, hV', ← ENNReal.ofReal_mul hJ.le, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hR2 : R ^ 2 ≤ K * ρ'' ^ 2 * J / c := by rw [le_div_iff₀ hc]; linarith
  calc P * R ^ 2 ≤ Qc * (K * ρ'' ^ 2 * J / c) :=
        mul_le_mul hPQ hR2 (sq_nonneg _) (le_trans hP hPQ)
    _ = (K * J / c) * (Qc * ρ'' ^ 2) := by ring
    _ ≤ (K * J / c) * (c * Bm * V') := mul_le_mul_of_nonneg_left hQr (by positivity)
    _ = K * Bm * (J * V') := by field_simp

/-- The tubes of one coarse tube, rescaled and thinned, form an exact separated
family at scale `δ' = b a δ` keeping a fixed fraction of any weight on the fibre. -/
theorem fibre_family {η δ ρ lam0 a b δ' η' t Mw : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hη : 0 < η)
    {n : ℕ} {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hhalf : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i)))
    (hS : Separated η δ n x v)
    {k : ℕ} {z w : Fin k → Space}
    (huniq : ∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j))
    (hfrostρ : ∀ j (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧
          tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ)) *
          volume W)
    (hdilρ : ∀ i j j', Tube δ (x i) (v i) ⊆ Dilate ρ (z j) (w j) →
      Tube δ (x i) (v i) ⊆ Dilate ρ (z j') (w j') → j = j')
    (j0 : Fin k) {z0 w0 : Space} (hw0 : ‖w0‖ = 1) (hz0 : Tube ρ z0 w0 = Tube ρ (z j0) (w j0))
    (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1 / 1000) (hlam0 : lam0 ≤ 1 / 100) (hlamρ : ρ ≤ lam0)
    (hlam8 : 1 / 10 ^ 8 ≤ lam0)
    (ha : a = lam0 / ρ) (hb : b = 1 / (1 + 144 * lam0 ^ 2)) (hδ'def : δ' = b * a * δ)
    (hδ'small : δ' ≤ 1 / 10000000)
    (hC2a : 34 * δ ^ (-(2 * η)) ≤ δ' ^ (-η'))
    (hC2b : δ' ^ η' ≤ δ ^ (2 * η) / (34 * 10 ^ 7))
    (hC2c : 2312 * δ ^ (-η) / lam0 ^ 2 / t ≤ δ' ^ (-η'))
    (ht : 0 < t) (ω : Fin n → ℝ) (hω0 : ∀ i, 0 ≤ ω i) (hωM : ∀ i, ω i ≤ Mw) (hMw : 0 < Mw) :
    ∃ (m : ℕ) (ι : Fin m → Fin n), Function.Injective ι ∧
      (∀ q, Tube δ (x (ι q)) (v (ι q)) ⊆ Tube ρ (z j0) (w j0)) ∧
      (∀ q, ‖ndir w0 a (orDir w0 (v (ι q)))‖ = 1 ∧
        Tube δ' (resc w0 (z0 + (1 / 2 : ℝ) • w0) a b (orStart w0 (x (ι q)) (v (ι q))))
          (ndir w0 a (orDir w0 (v (ι q)))) ⊆ ball 0 1 ∧
        resc w0 (z0 + (1 / 2 : ℝ) • w0) a b '' Tube δ (x (ι q)) (v (ι q)) ⊆
          Tube δ' (resc w0 (z0 + (1 / 2 : ℝ) • w0) a b (orStart w0 (x (ι q)) (v (ι q))))
            (ndir w0 a (orDir w0 (v (ι q))))) ∧
      (∀ q q', q ≠ q' →
        volume (Tube δ' (resc w0 (z0 + (1 / 2 : ℝ) • w0) a b (orStart w0 (x (ι q)) (v (ι q))))
            (ndir w0 a (orDir w0 (v (ι q)))) ∩
          Tube δ' (resc w0 (z0 + (1 / 2 : ℝ) • w0) a b (orStart w0 (x (ι q')) (v (ι q'))))
            (ndir w0 a (orDir w0 (v (ι q'))))) ≤
        (1 / 2 : ℝ≥0∞) *
          volume (Tube δ' (resc w0 (z0 + (1 / 2 : ℝ) • w0) a b
            (orStart w0 (x (ι q)) (v (ι q)))) (ndir w0 a (orDir w0 (v (ι q)))))) ∧
      (0 < m → Separated η' δ' m
        (fun q => resc w0 (z0 + (1 / 2 : ℝ) • w0) a b (orStart w0 (x (ι q)) (v (ι q))))
        (fun q => ndir w0 a (orDir w0 (v (ι q))))) ∧
      (∑ i ∈ Finset.univ.filter (fun i => Tube δ (x i) (v i) ⊆ Tube ρ (z j0) (w j0)), ω i) /
          ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) -
        Mw * t * (((⌈η⁻¹⌉₊ + 3 : ℕ) : ℝ) *
          (Finset.univ.filter (fun i => Tube δ (x i) (v i) ⊆ Tube ρ (z j0) (w j0))).card) ≤
        ∑ q, ω (ι q) := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hlam0pos : 0 < lam0 := lt_of_lt_of_le hρ0 hlamρ
  have ha1 : 1 ≤ a := by rw [ha, le_div_iff₀ hρ0]; linarith
  have haρ : a * ρ = lam0 := by rw [ha]; field_simp
  have hb0 : 0 < b := by rw [hb]; positivity
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one (by positivity)]; nlinarith [sq_nonneg lam0]
  have hbhalf : 1 / 2 ≤ b := by
    rw [hb, le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg lam0]
  have hbinv : b * (1 + 144 * lam0 ^ 2) = 1 := by rw [hb]; field_simp
  have hδ'0 : 0 < δ' := by rw [hδ'def]; positivity
  set c0 : Space := z0 + (1 / 2 : ℝ) • w0 with hc0_def
  set X : Fin n → Space := fun i => resc w0 c0 a b (orStart w0 (x i) (v i)) with hX_def
  set U : Fin n → Space := fun i => ndir w0 a (orDir w0 (v i)) with hU_def
  -- fine-to-coarse assignment
  choose fc hfc using fun i => (huniq i).exists
  have hfcu : ∀ i j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) → j = fc i :=
    fun i j h => (huniq i).unique h (hfc i)
  set F := Finset.univ.filter (fun i => Tube δ (x i) (v i) ⊆ Tube ρ (z j0) (w j0)) with hF_def
  have hFiff : ∀ i, i ∈ F ↔ fc i = j0 := by
    intro i
    simp only [hF_def, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact (hfcu i j0 h).symm
    · intro h; rw [← h]; exact hfc i
  -- facts about fibre tubes
  have hor : ∀ i, Tube δ (orStart w0 (x i) (v i)) (orDir w0 (v i)) = Tube δ (x i) (v i) :=
    fun i => Tube_orient δ w0 (x i) (v i)
  have horv : ∀ i, ‖orDir w0 (v i)‖ = 1 := fun i => (norm_orDir w0 (v i)).trans (hv i)
  have hFin0 : ∀ i ∈ F, Tube δ (orStart w0 (x i) (v i)) (orDir w0 (v i)) ⊆ Tube ρ z0 w0 := by
    intro i hi
    rw [hor, hz0]
    exact (Finset.mem_filter.mp hi).2
  have hFends : ∀ i ∈ F, ‖orStart w0 (x i) (v i) - z0‖ ≤ 3 * ρ ∧
      ‖orStart w0 (x i) (v i) + orDir w0 (v i) - (z0 + w0)‖ ≤ 3 * ρ := fun i hi =>
    oriented_in_coarse hδ (by linarith) (horv i) hw0 (inner_orDir_nonneg w0 (v i)) (hFin0 i hi)
  have hFdir : ∀ i ∈ F, ‖orDir w0 (v i) - w0‖ ≤ 6 * ρ := by
    intro i hi
    obtain ⟨h0, h1⟩ := hFends i hi
    have := dir_close_of_endpoints h0 h1
    linarith
  have hFinner : ∀ i ∈ F, 1 / 2 ≤ ⟪orDir w0 (v i), w0⟫ := by
    intro i hi
    have := inner_ge_of_close hw0 (hFdir i hi)
    linarith
  have hFbL : ∀ i ∈ F, b * ‖aniso w0 a (orDir w0 (v i))‖ ≤ 1 := by
    intro i hi
    have h := norm_aniso_unit_le hw0 (horv i) ha1 (hFdir i hi)
    have h2 : a ^ 2 * (6 * ρ) ^ 2 ≤ 144 * lam0 ^ 2 := by
      have : a ^ 2 * (6 * ρ) ^ 2 = 36 * (a * ρ) ^ 2 := by ring
      rw [this, haρ]; nlinarith [sq_nonneg lam0]
    calc b * ‖aniso w0 a (orDir w0 (v i))‖ ≤ b * (1 + 144 * lam0 ^ 2) :=
          mul_le_mul_of_nonneg_left (h.trans (by linarith)) hb0.le
      _ = 1 := hbinv
  have hδ'lam : δ' ≤ lam0 := by
    rw [hδ'def, ← haρ]
    calc b * a * δ ≤ 1 * a * ρ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hb1 (by linarith)) hδρ hδ.le
            (by positivity)
      _ = a * ρ := by ring
  have hFball : ∀ i ∈ F, Tube δ' (X i) (U i) ⊆ ball 0 1 := by
    intro i hi
    rw [hδ'def]
    exact resc_tube_subset_ball hρ0 ha ha1 hbhalf hb1 hlam0
      (by rw [← hδ'def]; exact hδ'lam) hw0 (horv i) (hFends i hi).1 (hFdir i hi)
  have hFimg : ∀ i ∈ F, resc w0 c0 a b '' Tube δ (x i) (v i) ⊆ Tube δ' (X i) (U i) := by
    intro i hi
    rw [← hor i, hδ'def]
    exact resc_tube_subset hw0 ha1 hb0 (hFbL i hi)
      (lt_of_lt_of_le one_pos ((horv i) ▸ norm_le_norm_aniso hw0 ha1 _))
  -- the fibre, enumerated
  set nF := F.card with hnF
  set eF : Fin nF → Fin n := enumerate F with heF_def
  have heF : ∀ q, eF q ∈ F := enumerate_mem F
  have heFinj : Function.Injective eF := enumerate_injective F
  set XE : Fin nF → Space := fun q => X (eF q) with hXE
  set UE : Fin nF → Space := fun q => U (eF q) with hUE
  -- the net of original scales
  set N : ℕ := ⌈η⁻¹⌉₊ with hN_def
  have hN : 0 < N := Nat.ceil_pos.mpr (inv_pos.mpr hη)
  have hgap : (N : ℝ)⁻¹ ≤ η := by
    rw [inv_le_comm₀ (by exact_mod_cast hN) hη]
    exact Nat.le_ceil _
  have hδ1' : δ < 1 := by linarith
  obtain ⟨sn, hsn, hnet⟩ := power_net hδ hδ1'.le hN hgap
  have hlev := fun l : Fin (N + 1) => hS (sn l) (hsn l).1 (hsn l).2
  choose ρ'' hρ''lo hρ''1 hρ''hi k'' hk'' z'' w'' hw'' hsep'' huniq'' hfull'' hbal''
    hfrost'' hdil'' using hlev
  choose lc hlc using fun l i => (huniq'' l i).exists
  have hlcu : ∀ l i m, Tube δ (x i) (v i) ⊆ Tube (ρ'' l) (z'' l m) (w'' l m) → m = lc l i :=
    fun l i m h => (huniq'' l i).unique h (hlc l i)
  -- oriented covers
  set zo : (l : Fin (N + 1)) → Fin (k'' l) → Space :=
    fun l m => orStart w0 (z'' l m) (w'' l m) with hzo
  set wo : (l : Fin (N + 1)) → Fin (k'' l) → Space :=
    fun l m => orDir w0 (w'' l m) with hwo
  have hor'' : ∀ l m, Tube (ρ'' l) (zo l m) (wo l m) = Tube (ρ'' l) (z'' l m) (w'' l m) :=
    fun l m => Tube_orient _ w0 _ _
  have hwo1 : ∀ l m, ‖wo l m‖ = 1 := fun l m => (norm_orDir w0 _).trans (hw'' l m)
  -- regular levels
  let Λr := {l : Fin (N + 1) // 17 * a * ρ'' l ≤ 1 / 10000000}
  have hregρ : ∀ l : Λr, ρ'' l.1 ≤ ρ := by
    intro l
    have h : 17 * a * ρ'' l.1 ≤ 1 / 10000000 := l.2
    have hρ''0 : 0 < ρ'' l.1 := lt_of_lt_of_le hδ ((hsn l.1).1.trans (hρ''lo l.1))
    -- ρ'' · lam0 = (a ρ'') ρ ≤ ρ / (17 · 10^7)
    have h1 : ρ'' l.1 * lam0 ≤ ρ / (17 * 10000000) := by
      rw [← haρ]
      have : a * ρ'' l.1 ≤ 1 / (17 * 10000000) := by linarith
      calc ρ'' l.1 * (a * ρ) = (a * ρ'' l.1) * ρ := by ring
        _ ≤ 1 / (17 * 10000000) * ρ := mul_le_mul_of_nonneg_right this hρ0.le
        _ = ρ / (17 * 10000000) := by ring
    have h2 : ρ'' l.1 * (1 / 10 ^ 8) ≤ ρ'' l.1 * lam0 :=
      mul_le_mul_of_nonneg_left hlam8 hρ''0.le
    nlinarith
  have hreg100 : ∀ l : Λr, ρ'' l.1 ≤ 1 / 100 := fun l => (hregρ l).trans (by linarith)
  have hδρ'' : ∀ l, δ ≤ ρ'' l := fun l => (hsn l).1.trans (hρ''lo l)
  -- tree property: covers hit by the fibre contain only fibre tubes
  have htreeF : ∀ (l : Λr) i i', lc l.1 i' = lc l.1 i → i ∈ F → i' ∈ F := by
    intro l i i' he hi
    rw [hFiff] at hi ⊢
    have h := fibre_tree hδ (hδρ'' l.1) (hregρ l) hv fc hfc hdilρ (hw'' l.1 (lc l.1 i))
      (hlc l.1 i) (by rw [← he]; exact hlc l.1 i')
    rw [h, hi]
  -- oriented containment of fibre tubes in their regular covers
  have hFcov : ∀ (l : Λr) i, i ∈ F →
      Tube δ (orStart w0 (x i) (v i)) (orDir w0 (v i)) ⊆
        Tube (ρ'' l.1) (zo l.1 (lc l.1 i)) (wo l.1 (lc l.1 i)) := by
    intro l i hi
    rw [hor, hor'']
    exact hlc l.1 i
  have hFcovdir : ∀ (l : Λr) i, i ∈ F → ‖orDir w0 (v i) - wo l.1 (lc l.1 i)‖ ≤ 6 * ρ'' l.1 := by
    intro l i hi
    obtain ⟨h0, h1⟩ := endpoints_close_oriented hδ (hreg100 l) (horv i) (hwo1 l.1 _) hw0
      (hFinner i hi) (inner_orDir_nonneg w0 _) (hFcov l i hi)
    have := dir_close_of_endpoints h0 h1
    linarith
  -- hit covers
  let hitR : (l : Λr) → Fin (k'' l.1) → Prop := fun l m => ∃ q, lc l.1 (eF q) = m
  have hithbL : ∀ (l : Λr) m, hitR l m → b * ‖aniso w0 a (wo l.1 m)‖ ≤ 1 := by
    rintro l m ⟨q, rfl⟩
    have h1 := hFcovdir l (eF q) (heF q)
    have h2 := hFdir (eF q) (heF q)
    have hθ : ‖wo l.1 (lc l.1 (eF q)) - w0‖ ≤ 12 * ρ := by
      have := norm_sub_le_norm_sub_add_norm_sub (wo l.1 (lc l.1 (eF q)))
        (orDir w0 (v (eF q))) w0
      have h1' : ‖wo l.1 (lc l.1 (eF q)) - orDir w0 (v (eF q))‖ ≤ 6 * ρ'' l.1 := by
        rw [norm_sub_rev]; exact h1
      linarith [hregρ l]
    have h := norm_aniso_unit_le hw0 (hwo1 l.1 _) ha1 hθ
    have h3 : a ^ 2 * (12 * ρ) ^ 2 = 144 * lam0 ^ 2 := by rw [← haρ]; ring
    calc b * ‖aniso w0 a (wo l.1 (lc l.1 (eF q)))‖ ≤ b * (1 + 144 * lam0 ^ 2) :=
          mul_le_mul_of_nonneg_left (h.trans (by rw [h3])) hb0.le
      _ = 1 := hbinv
  have hitax : ∀ (l : Λr) m, hitR l m → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖resc w0 c0 a b (zo l.1 m) + t • ndir w0 a (wo l.1 m)‖ ≤ 2 := by
    rintro l m ⟨q, rfl⟩ t ht
    have hc := resc_axis_close (c0 := c0) hδ (hreg100 l) ha1 hb0 hb1 hw0 (horv _)
      (hwo1 l.1 _) (hFinner _ (heF q)) (inner_orDir_nonneg w0 _) (hFcov l _ (heF q)) ht
    have hin := hFball (eF q) (heF q) (axis_mem_Tube hδ'0 _ _ ht)
    rw [mem_ball_zero_iff] at hin
    have hsmall : 15 * a * ρ'' l.1 ≤ 1 := by
      have := l.2
      have h0 : 0 ≤ a * ρ'' l.1 := by
        have : 0 < ρ'' l.1 := lt_of_lt_of_le hδ (hδρ'' l.1)
        positivity
      linarith
    have := norm_sub_le_norm_sub_add_norm_sub
      (resc w0 c0 a b (zo l.1 (lc l.1 (eF q))) + t • ndir w0 a (wo l.1 (lc l.1 (eF q))))
      (X (eF q) + t • U (eF q)) 0
    simp only [sub_zero] at this
    linarith
  -- cover systems
  let Lr : Λr → CoverSys nF := fun l =>
    { k := k'' l.1, ρ := 17 * a * ρ'' l.1,
      z := fun m => resc w0 c0 a b (zo l.1 m), w := fun m => ndir w0 a (wo l.1 m),
      f := fun q => lc l.1 (eF q),
      conf := rescCoverConflict δ' (17 * a * ρ'' l.1) XE UE
        (fun m => resc w0 c0 a b (zo l.1 m)) (fun m => ndir w0 a (wo l.1 m)) (hitR l) }
  let Ltop : CoverSys nF :=
    { k := 1, ρ := 1, z := fun _ => -(1 / 2 : ℝ) • w0, w := fun _ => w0,
      f := fun _ => 0, conf := fun _ _ => False }
  let L : Λr ⊕ Unit → CoverSys nF := Sum.elim Lr (fun _ => Ltop)
  have hball_top : ball (0 : Space) 1 ⊆ Tube 1 (-(1 / 2 : ℝ) • w0) w0 := by
    intro p hp
    apply mem_Tube_of_param (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    have : p - (-(1 / 2 : ℝ) • w0 + (1 / 2 : ℝ) • w0) = p := by module
    rw [this]
    simpa using hp
  -- the hypotheses of the selection
  have hf : ∀ l q, Tube δ' (XE q) (UE q) ⊆
      Tube (L l).ρ ((L l).z ((L l).f q)) ((L l).w ((L l).f q)) := by
    rintro (l | u) q
    · change Tube δ' (X (eF q)) (U (eF q)) ⊆
        Tube (17 * a * ρ'' l.1) (resc w0 c0 a b (zo l.1 (lc l.1 (eF q))))
          (ndir w0 a (wo l.1 (lc l.1 (eF q))))
      rw [hδ'def]
      exact resc_subset_cover hδ (hreg100 l) ha1 hb0 hb1 (hδρ'' l.1) hw0 (horv _)
        (hwo1 l.1 _) (hFinner _ (heF q)) (inner_orDir_nonneg w0 _) (hFcov l _ (heF q))
    · exact (hFball _ (heF q)).trans hball_top
  have hhalfE : ∀ q q', q ≠ q' →
      volume (Tube δ (orStart w0 (x (eF q)) (v (eF q))) (orDir w0 (v (eF q))) ∩
        Tube δ (orStart w0 (x (eF q')) (v (eF q'))) (orDir w0 (v (eF q')))) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (orStart w0 (x (eF q)) (v (eF q))) (orDir w0 (v (eF q)))) := by
    intro q q' hqq
    rw [hor, hor]
    exact hhalf _ _ (heFinj.ne hqq)
  have hcEdeg : ∀ q, (Finset.univ.filter (elemConflict δ' 0 XE UE q)).card < 10 ^ 61 + 1 := by
    intro q
    have h := resc_elem_conflict_card (c0 := c0) hδ ha1 hbhalf hb1 (by rw [← hδ'def]; exact hδ'small)
      hw0 (fun q => orStart w0 (x (eF q)) (v (eF q))) (fun q => orDir w0 (v (eF q)))
      (fun q => horv _) hhalfE (fun q => hFbL _ (heF q))
      (fun q => by rw [← hδ'def]; exact hFball _ (heF q)) q
    rw [← hδ'def] at h
    have h' : ((Finset.univ.filter (elemConflict δ' 0 XE UE q)).card : ℝ) ≤ 10 ^ 53 := h
    have : (Finset.univ.filter (elemConflict δ' 0 XE UE q)).card ≤ 10 ^ 53 := by exact_mod_cast h'
    omega
  have hcC : ∀ l {m m'}, (L l).conf m m' → (L l).conf m' m := by
    rintro (l | u) m m' h
    · exact rescCoverConflict_symm (s := δ') (R := 17 * a * ρ'' l.1) (X := XE) (U := UE)
        (Z := fun m => resc w0 c0 a b (zo l.1 m)) (V := fun m => ndir w0 a (wo l.1 m))
        (hit := hitR l) h
    · exact h
  have hsepo : ∀ (l : Λr) m m', m ≠ m' →
      volume (Tube (ρ'' l.1) (zo l.1 m) (wo l.1 m) ∩ Tube (ρ'' l.1) (zo l.1 m') (wo l.1 m')) ≤
        (1 / 2 : ℝ≥0∞) * volume (Tube (ρ'' l.1) (zo l.1 m) (wo l.1 m)) := by
    intro l m m' hmm
    simp only [hor'']
    exact hsep'' l.1 m m' hmm
  have hcCdeg : ∀ l m, (Finset.univ.filter ((L l).conf m)).card < 10 ^ 61 + 1 := by
    rintro (l | u) m
    · have hρ''0 : 0 < ρ'' l.1 := lt_of_lt_of_le hδ (hδρ'' l.1)
      have h := resc_cover_conflict_card (c0 := c0) hδ'0 hρ''0 ha1 hbhalf hb1 l.2 hw0 XE UE
        (fun q => norm_ndir hw0 ha1 (horv _)) (zo l.1) (wo l.1) (hwo1 l.1) (hsepo l) (hitR l)
        (hithbL l) (hitax l) m
      have : (Finset.univ.filter ((L (Sum.inl l)).conf m)).card ≤ 10 ^ 61 := by exact_mod_cast h
      omega
    · have hempty : Finset.univ.filter ((L (Sum.inr u)).conf m) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun _ _ h => h)
      rw [hempty]; simp
  have hunit : ∀ l m, ‖(L l).w m‖ = 1 := by
    rintro (l | u) m
    · exact norm_ndir hw0 ha1 (hwo1 l.1 m)
    · exact hw0
  have hC : ∀ l m m', (∃ i, (L l).f i = m) → (∃ i, (L l).f i = m') → m ≠ m' →
      ¬(L l).conf m m' →
      volume (Tube (L l).ρ ((L l).z m) ((L l).w m) ∩ Tube (L l).ρ ((L l).z m') ((L l).w m')) ≤
        (1 / 2 : ℝ≥0∞) * volume (Tube (L l).ρ ((L l).z m) ((L l).w m)) := by
    rintro (l | u) m m' hm hm' hne hnc
    · by_contra hlt
      push Not at hlt
      exact hnc ⟨hne, hm, hm', Or.inl hlt⟩
    · have h1 : (m : ℕ) < 1 := m.isLt
      have h2 : (m' : ℕ) < 1 := m'.isLt
      exact absurd (Fin.ext (by omega)) hne
  have hsep : ∀ l q m m', (∃ i, (L l).f i = m) → (∃ i, (L l).f i = m') →
      Tube δ' (XE q) (UE q) ⊆ Dilate (L l).ρ ((L l).z m) ((L l).w m) →
      Tube δ' (XE q) (UE q) ⊆ Dilate (L l).ρ ((L l).z m') ((L l).w m') →
        m = m' ∨ (L l).conf m m' := by
    rintro (l | u) q m m' hm hm' h1 h2
    · by_cases hmm : m = m'
      · exact Or.inl hmm
      · exact Or.inr ⟨hmm, hm, hm', Or.inr (Or.inr ⟨q, h1, h2⟩)⟩
    · have h1 : (m : ℕ) < 1 := m.isLt
      have h2 : (m' : ℕ) < 1 := m'.isLt
      exact Or.inl (Fin.ext (by omega))
  -- constants
  set c : ℝ := δ ^ (-η) with hc_def
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1'.le (by linarith)
  set K : ℝ := 2312 * c / lam0 ^ 2 with hK_def
  have hlam2 : lam0 ^ 2 ≤ 1 := by nlinarith
  have hK : c ≤ K := by
    rw [hK_def, le_div_iff₀ (by positivity)]; nlinarith
  have hK0 : 0 < K := by positivity
  have hc0' : 0 < c := by linarith
  have hb3 : 1 / 8 ≤ b ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hbhalf 3; norm_num at this ⊢; linarith
  -- fibre counts at regular levels
  have hcnt : ∀ (l : Λr) q1,
      ((Finset.univ.filter (fun q => lc l.1 (eF q) = lc l.1 (eF q1))).card : ℝ) =
        ({i | tube δ (x i) (v i) ⊆ tube (ρ'' l.1) (z'' l.1 (lc l.1 (eF q1)))
          (w'' l.1 (lc l.1 (eF q1)))}.ncard : ℝ) := by
    intro l q1
    congr 1
    have h1 := enumerate_count F (fun i => lc l.1 i = lc l.1 (eF q1))
    rw [ncard_setOf] at h1
    rw [h1]
    have h2 : F.filter (fun i => lc l.1 i = lc l.1 (eF q1)) =
        Finset.univ.filter (fun i => lc l.1 i = lc l.1 (eF q1)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨htreeF l (eF q1) i h (heF q1), h⟩
    rw [h2]
    have h3 : {i | tube δ (x i) (v i) ⊆ tube (ρ'' l.1) (z'' l.1 (lc l.1 (eF q1)))
        (w'' l.1 (lc l.1 (eF q1)))} =
        (Finset.univ.filter (fun i => lc l.1 i = lc l.1 (eF q1)) : Set (Fin n)) := by
      ext i
      simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact (hlcu l.1 i _ h).symm
      · intro h; rw [← h]; exact hlc l.1 i
    rw [h3, Set.ncard_coe_finset]
  have hbal : ∀ l q1 q2, ((Finset.univ.filter (fun q => (L l).f q = (L l).f q1)).card : ℝ) ≤
      K * (Finset.univ.filter (fun q => (L l).f q = (L l).f q2)).card := by
    rintro (l | u) q1 q2
    · change ((Finset.univ.filter (fun q => lc l.1 (eF q) = lc l.1 (eF q1))).card : ℝ) ≤
        K * (Finset.univ.filter (fun q => lc l.1 (eF q) = lc l.1 (eF q2))).card
      rw [hcnt l q1, hcnt l q2]
      have h := hbal'' l.1 (lc l.1 (eF q1)) (lc l.1 (eF q2))
      exact h.trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _))
    · change ((Finset.univ.filter (fun q : Fin nF => (0 : Fin 1) = 0)).card : ℝ) ≤
        K * (Finset.univ.filter (fun q : Fin nF => (0 : Fin 1) = 0)).card
      have h0 : (0 : ℝ) ≤ ((Finset.univ.filter (fun q : Fin nF => (0 : Fin 1) = 0)).card : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
  -- convex counts
  have hJ : 0 < b ^ 3 * a ^ 2 := by positivity
  have hpre : ∀ (W : Set Space) i, i ∈ F → Tube δ' (X i) (U i) ⊆ W →
      Tube δ (x i) (v i) ⊆ resc w0 c0 a b ⁻¹' W := by
    intro W i hi hW p hp
    exact hW (hFimg i hi ⟨p, hp, rfl⟩)
  have hfrost : ∀ l q1 (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (((Finset.univ.filter (fun q => (L l).f q = (L l).f q1 ∧
          Tube δ' (XE q) (UE q) ⊆ W)).card : ℝ) * (L l).ρ ^ 2) ≤
        ENNReal.ofReal (K * (Finset.univ.filter (fun q => (L l).f q = (L l).f q1)).card) *
          volume W := by
    rintro (l | u) q1 W hW
    · change ENNReal.ofReal (((Finset.univ.filter (fun q => lc l.1 (eF q) = lc l.1 (eF q1) ∧
          Tube δ' (X (eF q)) (U (eF q)) ⊆ W)).card : ℝ) * (17 * a * ρ'' l.1) ^ 2) ≤
        ENNReal.ofReal (K * (Finset.univ.filter
          (fun q => lc l.1 (eF q) = lc l.1 (eF q1))).card) * volume W
      rw [hcnt l q1]
      set m := lc l.1 (eF q1)
      set W' := resc w0 c0 a b ⁻¹' W
      have hW' : Convex ℝ W' := convex_preimage_resc hW w0 c0 a b
      have hQ := hfrost'' l.1 m W' hW'
      have hρ''0 : 0 < ρ'' l.1 := lt_of_lt_of_le hδ (hδρ'' l.1)
      apply frost_resc (c := c) (J := b ^ 3 * a ^ 2) (ρ'' := ρ'' l.1) hc0' hJ hρ''0
        (Nat.cast_nonneg _) _ _ hK0 _ hQ (volume_preimage_resc hw0 (by linarith) hb0 W)
      · -- P ≤ Qc
        have h1 := enumerate_count F (fun i => lc l.1 i = m ∧ Tube δ' (X i) (U i) ⊆ W)
        rw [ncard_setOf] at h1
        rw [h1]
        have hsub : F.filter (fun i => lc l.1 i = m ∧ Tube δ' (X i) (U i) ⊆ W) ⊆
            Finset.univ.filter (fun i => lc l.1 i = m ∧ Tube δ (x i) (v i) ⊆ W') := by
          intro i hi
          obtain ⟨hiF, him, hiW⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, him, hpre W i hiF hiW⟩
        have hset : {i | tube δ (x i) (v i) ⊆ tube (ρ'' l.1) (z'' l.1 m) (w'' l.1 m) ∧
            tube δ (x i) (v i) ⊆ W'} =
            (Finset.univ.filter (fun i => lc l.1 i = m ∧ Tube δ (x i) (v i) ⊆ W') :
              Set (Fin n)) := by
          ext i
          simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨(hlcu l.1 i _ h1).symm, h2⟩
          · rintro ⟨h1, h2⟩; rw [← h1]; exact ⟨hlc l.1 i, h2⟩
        rw [hset, Set.ncard_coe_finset]
        exact_mod_cast Finset.card_le_card hsub
      · -- the fibre is nonempty
        have hpos : 0 < ({i | tube δ (x i) (v i) ⊆ tube (ρ'' l.1) (z'' l.1 m)
            (w'' l.1 m)}.ncard : ℝ) := by
          rw [← hcnt l q1]
          have : (Finset.univ.filter (fun q => lc l.1 (eF q) = m)).Nonempty :=
            ⟨q1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
          exact_mod_cast Finset.card_pos.mpr this
        exact hpos
      · -- R² c ≤ K ρ''² J
        rw [hK_def]
        have hl : 0 < lam0 ^ 2 := by positivity
        rw [show (17 * a * ρ'' l.1) ^ 2 * c = 289 * c * (a ^ 2 * ρ'' l.1 ^ 2) by ring,
          show 2312 * c / lam0 ^ 2 * ρ'' l.1 ^ 2 * (b ^ 3 * a ^ 2) =
            (2312 * b ^ 3 / lam0 ^ 2) * c * (a ^ 2 * ρ'' l.1 ^ 2) by ring]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        rw [le_div_iff₀ hl]
        nlinarith
    · change ENNReal.ofReal (((Finset.univ.filter (fun q : Fin nF => (0 : Fin 1) = 0 ∧
          Tube δ' (X (eF q)) (U (eF q)) ⊆ W)).card : ℝ) * 1 ^ 2) ≤
        ENNReal.ofReal (K * (Finset.univ.filter (fun q : Fin nF => (0 : Fin 1) = 0)).card) *
          volume W
      set W' := resc w0 c0 a b ⁻¹' W
      have hW' : Convex ℝ W' := convex_preimage_resc hW w0 c0 a b
      have hQ := hfrostρ j0 W' hW'
      have hFset : {i | tube δ (x i) (v i) ⊆ tube ρ (z j0) (w j0)} = (F : Set (Fin n)) := by
        ext i; simp [hF_def, tube]
      have hcard : ((Finset.univ.filter (fun q : Fin nF => (0 : Fin 1) = 0)).card : ℝ) =
          ({i | tube δ (x i) (v i) ⊆ tube ρ (z j0) (w j0)}.ncard : ℝ) := by
        rw [hFset, Set.ncard_coe_finset]
        simp [nF]
      rw [hcard]
      apply frost_resc (c := c) (J := b ^ 3 * a ^ 2) (ρ'' := ρ) hc0' hJ hρ0
        (Nat.cast_nonneg _) _ _ hK0 _ hQ (volume_preimage_resc hw0 (by linarith) hb0 W)
      · have hset : {i | tube δ (x i) (v i) ⊆ tube ρ (z j0) (w j0) ∧ tube δ (x i) (v i) ⊆ W'} =
            (Finset.univ.filter (fun i => i ∈ F ∧ Tube δ (x i) (v i) ⊆ W') : Set (Fin n)) := by
          ext i; simp [hF_def, tube]
        rw [hset, Set.ncard_coe_finset]
        have h1 := enumerate_count F (fun i => (0 : Fin 1) = 0 ∧ Tube δ' (X i) (U i) ⊆ W)
        rw [ncard_setOf] at h1
        rw [h1]
        have hsub : F.filter (fun i => (0 : Fin 1) = 0 ∧ Tube δ' (X i) (U i) ⊆ W) ⊆
            Finset.univ.filter (fun i => i ∈ F ∧ Tube δ (x i) (v i) ⊆ W') := by
          intro i hi
          obtain ⟨hiF, -, hiW⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiF, hpre W i hiF hiW⟩
        exact_mod_cast Finset.card_le_card hsub
      · rw [← hcard]
        have : (Finset.univ.filter (fun q : Fin nF => (0 : Fin 1) = 0)).Nonempty :=
          ⟨q1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        exact_mod_cast Finset.card_pos.mpr this
      · rw [hK_def]
        have hl : 0 < lam0 ^ 2 := by positivity
        have haρ2 : a ^ 2 * ρ ^ 2 = lam0 ^ 2 := by rw [← haρ]; ring
        rw [show (1 : ℝ) ^ 2 * c = 1 * c by ring,
          show 2312 * c / lam0 ^ 2 * ρ ^ 2 * (b ^ 3 * a ^ 2) =
            2312 * c * b ^ 3 * ((a ^ 2 * ρ ^ 2) / lam0 ^ 2) by ring, haρ2,
          div_self hl.ne', mul_one]
        nlinarith
  -- the selection
  obtain ⟨Q, hQE, hQC, hQmass⟩ := select_frozen_sys (Nat.succ_pos (10 ^ 61)) (s := δ')
    (K := K) XE UE L hf (elemConflict δ' 0 XE UE) elemConflict_symm hcEdeg hcC hcCdeg
    hunit hC hsep hbal hfrost (fun q => ω (eF q)) (fun q => hωM _) hMw ht
  refine ⟨Q.card, fun q => eF (enumerate Q q), heFinj.comp (enumerate_injective Q),
    fun q => (Finset.mem_filter.mp (heF _)).2, fun q => ⟨norm_ndir hw0 ha1 (horv _),
      hFball _ (heF _), hFimg _ (heF _)⟩, ?_, ?_, ?_⟩
  · intro q q' hqq
    have hne : enumerate Q q ≠ enumerate Q q' := (enumerate_injective Q).ne hqq
    have hnc := hQE _ (enumerate_mem Q q) _ (enumerate_mem Q q') hne
    by_contra hlt
    push Not at hlt
    exact hnc ⟨hne, Or.inl (by simpa [ntube_zero] using hlt)⟩
  · intro hm r' hr' hr'1
    have hQne : Q.Nonempty := Finset.card_pos.mp hm
    set rr := max δ (r' / (17 * a)) with hrr
    have h17a : 0 < 17 * a := by linarith
    have hrr1 : rr ≤ 1 := max_le hδ1'.le (by
      rw [div_le_one h17a]; linarith)
    obtain ⟨l, hl1, hl2⟩ := hnet rr (le_max_left _ _) hrr1
    have h17δ : 17 * a * δ ≤ 34 * r' := by
      have : 17 * a * δ = 17 * δ' / b := by rw [hδ'def]; field_simp
      rw [this, div_le_iff₀ hb0]
      nlinarith
    have hρ''r : 17 * a * ρ'' l ≤ δ ^ (-(2 * η)) * (34 * r') := by
      have h1 := hρ''hi l
      have hstep : ρ'' l ≤ δ ^ (-(2 * η)) * rr := by
        calc ρ'' l ≤ δ ^ (-η) * sn l := h1
          _ ≤ δ ^ (-η) * (δ ^ (-η) * rr) := mul_le_mul_of_nonneg_left hl2 (by positivity)
          _ = δ ^ (-(2 * η)) * rr := by
            rw [← mul_assoc, ← Real.rpow_add hδ]; ring_nf
      have hrr' : 17 * a * rr ≤ 34 * r' := by
        rw [hrr]
        rcases le_total δ (r' / (17 * a)) with h | h
        · rw [max_eq_right h, mul_div_cancel₀ _ h17a.ne']; linarith
        · rw [max_eq_left h]; exact h17δ
      calc 17 * a * ρ'' l ≤ 17 * a * (δ ^ (-(2 * η)) * rr) :=
            mul_le_mul_of_nonneg_left hstep h17a.le
        _ = δ ^ (-(2 * η)) * (17 * a * rr) := by ring
        _ ≤ δ ^ (-(2 * η)) * (34 * r') := mul_le_mul_of_nonneg_left hrr' (by positivity)
    have hr'ρ'' : r' ≤ 17 * a * ρ'' l := by
      have h1 : r' / (17 * a) ≤ ρ'' l := (le_max_right _ _).trans (hl1.trans (hρ''lo l))
      rw [div_le_iff₀ h17a] at h1
      linarith
    have hKt : K / t ≤ δ' ^ (-η') := by
      rw [hK_def]; simpa [hc_def] using hC2c
    by_cases hreg : 17 * a * ρ'' l ≤ 1 / 10000000
    · obtain ⟨k', hk', z', w', hcov, hsepQ⟩ := hQC hQne (Sum.inl ⟨l, hreg⟩)
      refine ⟨17 * a * ρ'' l, hr'ρ'', by linarith, ?_,
        separated_level_of_cover hk' (CoverAt.mono_const hcov hKt) hsepQ⟩
      calc 17 * a * ρ'' l ≤ δ ^ (-(2 * η)) * (34 * r') := hρ''r
        _ = (34 * δ ^ (-(2 * η))) * r' := by ring
        _ ≤ δ' ^ (-η') * r' := mul_le_mul_of_nonneg_right hC2a (by linarith)
    · obtain ⟨k', hk', z', w', hcov, hsepQ⟩ := hQC hQne (Sum.inr ())
      refine ⟨1, hr'1, le_rfl, ?_, separated_level_of_cover hk' (CoverAt.mono_const hcov hKt)
        hsepQ⟩
      push Not at hreg
      have hlow : δ ^ (2 * η) / (34 * 10 ^ 7) ≤ r' := by
        have h1 : 1 / 10000000 < δ ^ (-(2 * η)) * (34 * r') := hreg.trans_le hρ''r
        have hpos : 0 < δ ^ (2 * η) := by positivity
        have hinv : δ ^ (-(2 * η)) * δ ^ (2 * η) = 1 := by
          rw [← Real.rpow_add hδ]; simp
        rw [div_le_iff₀ (by norm_num)]
        have := mul_lt_mul_of_pos_right h1 hpos
        nlinarith
      have hpow : δ' ^ (-η') * δ' ^ η' = 1 := by
        rw [← Real.rpow_add hδ'0]; simp
      calc (1 : ℝ) = δ' ^ (-η') * δ' ^ η' := hpow.symm
        _ ≤ δ' ^ (-η') * r' := mul_le_mul_of_nonneg_left (hC2b.trans hlow) (by positivity)
  · -- mass
    have hB1 : (1 : ℝ) ≤ ((10 ^ 61 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hcardΛ : Fintype.card (Λr ⊕ Unit) + 1 ≤ ⌈η⁻¹⌉₊ + 3 := by
      rw [Fintype.card_sum, Fintype.card_unit]
      have : Fintype.card Λr ≤ N + 1 := by
        calc Fintype.card Λr ≤ Fintype.card (Fin (N + 1)) := Fintype.card_subtype_le _
          _ = N + 1 := Fintype.card_fin _
      omega
    have hsumF : ∑ q, ω (eF q) = ∑ i ∈ F, ω i := enumerate_sum F ω
    have hsumQ : ∑ q ∈ Q, ω (eF q) = ∑ q, ω (eF (enumerate Q q)) :=
      (enumerate_sum Q (fun q => ω (eF q))).symm
    rw [hsumF, hsumQ] at hQmass
    have hsum0 : 0 ≤ ∑ i ∈ F, ω i := Finset.sum_nonneg (fun i _ => hω0 i)
    have hpowle : ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (Fintype.card (Λr ⊕ Unit) + 1) ≤
        ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) := pow_le_pow_right₀ hB1 hcardΛ
    have hdiv : (∑ i ∈ F, ω i) / ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) ≤
        (∑ i ∈ F, ω i) / ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (Fintype.card (Λr ⊕ Unit) + 1) :=
      div_le_div_of_nonneg_left hsum0 (by positivity) hpowle
    have hloss : Mw * t * (((Fintype.card (Λr ⊕ Unit) + 1 : ℕ) : ℝ) * nF) ≤
        Mw * t * (((⌈η⁻¹⌉₊ + 3 : ℕ) : ℝ) * F.card) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hcardΛ
    linarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
