-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomGlobal

/-!
# The zoomed family

From a family with separated all-scale covers and grains, zooming by `r` about a pigeonholed
centre, colouring away conflicts of fine pieces and of coarse pieces at every scale of a net,
and pruning fibres produces a family at scale `r δ` with the exact density, separated covers,
compact shadings, volume bound and grains of the frozen statement.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric MeasureTheory Finset
open scoped ENNReal RealInnerProductSpace Classical

noncomputable section

/-- The heaviest colour class inside a candidate set. -/
theorem heavy_class {I : Type*} [Fintype I] {K : ℕ} (hK : 0 < K) (col : I → Fin K)
    (w : I → ℝ) (P₀ : Finset I) :
    ∃ a : Fin K, (∑ i ∈ P₀, w i) / K ≤ ∑ i ∈ P₀.filter (fun i => col i = a), w i := by
  let mass : Fin K → ℝ := fun a => ∑ i ∈ P₀.filter (fun i => col i = a), w i
  have hne : (univ : Finset (Fin K)).Nonempty := ⟨⟨0, hK⟩, mem_univ _⟩
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image univ mass hne
  refine ⟨a, ?_⟩
  have hsum : ∑ b, mass b = ∑ i ∈ P₀, w i :=
    sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
  rw [div_le_iff₀ (by exact_mod_cast hK), ← hsum]
  calc ∑ b, mass b ≤ ∑ _b : Fin K, mass a := sum_le_sum fun b hb => hmax b hb
    _ = mass a * K := by simp [mul_comm]

/-- A colouring of a symmetric relation with degree at most `D`. -/
theorem color_of_degree {I : Type*} [Fintype I] {D : ℝ} (R : I → I → Prop)
    (hR : ∀ {i j}, R i j → R j i) (hdeg : ∀ i, ((univ.filter (R i)).card : ℝ) ≤ D) :
    ∃ col : I → Fin (⌊D⌋₊ + 1), ∀ i j, i ≠ j → R i j → col i ≠ col j := by
  apply WangZahlLot.Obl.wz_separated_cover_refinement.color_relation (Nat.succ_pos _) R hR
  intro i
  have h := hdeg i
  have : (univ.filter (R i)).card ≤ ⌊D⌋₊ := Nat.le_floor h
  omega

/-- The number of colours for conflicts. -/
def Kc (r : ℝ) : ℕ := ⌊conflictConst * r ^ 4⌋₊ + 1

/-- The number of grid points. -/
def Ng (r : ℝ) : ℕ := (⌈64 * r⌉₊ + 1) ^ 3

/-- The retention fraction of the fibre pruning. -/
def tpar (δ η₁ r : ℝ) (N : ℕ) : ℝ :=
  δ ^ η₁ * r / (768 * Ng r * Kc r * (Kc r : ℝ) ^ (N + 1) * (N + 2))

theorem tpar_pos {δ η₁ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (N : ℕ) : 0 < tpar δ η₁ r N := by
  unfold tpar Ng Kc; positivity

set_option maxHeartbeats 8000000 in
/-- The zoomed family at scale `r δ`, under explicit parameter conditions: the pieces of a
subfamily `e`, zoomed about `c`, with the zoomed cut shadings. -/
theorem zoom_family_core {σ η η₁ δ r : ℝ} {n N : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hr : 16 ≤ r) (hη : 0 < η) (hη₁ : 0 < η₁)
    (hN : 0 < N) (hgap : (N : ℝ)⁻¹ ≤ η / 4)
    (hfam : ExtremalFamily σ η₁ δ n x v Y)
    (hP1 : δ ≤ 1 / (131072 * r)) (hP2 : r * δ ≤ 1 / 8)
    (hP4 : δ ^ (-η₁) * (r * δ) ^ (η / 4) ≤ 1 / 16384)
    (hP4' : δ ^ (-η₁) * δ ≤ 1 / (131072 * r))
    (hP5 : 8 * δ ^ (-η₁) ≤ (r * δ) ^ (-η))
    (hP5' : δ ^ (-η₁) * (r * δ) ^ (-(η / 4)) ≤ (r * δ) ^ (-η))
    (hP7 : 64 * (432 * 512) * r ^ 2 * δ ^ (-η₁) ≤ (r * δ) ^ (-η) * tpar δ η₁ r N)
    (hP8 : (r * δ) ^ η ≤ 384 * tpar δ η₁ r N)
    (hP9 : r ^ 3 * δ ^ (σ - η₁) ≤ (r * δ) ^ (σ - η)) :
    ∃ (c : Space) (m : ℕ) (e : Fin m → Fin n),
      ExtremalFamily σ η (r * δ) m (fun a => pieceBase r c (x (e a)) (v (e a)))
        (fun a => v (e a)) (fun a => zshade r c (v (e a)) (Y (e a))) := by
  obtain ⟨hD, hS, hcomp, hvol⟩ := hfam
  obtain ⟨hn, hv, hball, hsep, hmeas, hY, hmass⟩ := hD
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hδ1' : δ ≤ 1 := by linarith
  have hδ' : 0 < r * δ := mul_pos hr0 hδ
  have hδ'1 : r * δ ≤ 1 := by linarith
  have hKpos : 0 < δ ^ (-η₁) := Real.rpow_pos_of_pos hδ _
  have hK1 : 1 ≤ δ ^ (-η₁) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1' (by linarith)
  have hδ16 : δ ≤ 1 / (16 * r) := hP1.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
  -- the zoom centre
  obtain ⟨c, hcentre⟩ := exists_zoom_centre hr1 hδ16 x v Y hv hY hball
  set I₀ := univ.filter (fun i => FNear r c (x i) (v i))
  have hI₀ : ∀ i ∈ I₀, FNear r c (x i) (v i) := fun i hi => (Finset.mem_filter.mp hi).2
  -- weights: volumes of the zoomed cut shadings
  have hshade_sub : ∀ i, zshade r c (v i) (Y i) ⊆
      Tube (r * δ) (pieceBase r c (x i) (v i)) (v i) := by
    rintro i _ ⟨p, ⟨hp, hps⟩, rfl⟩
    exact zoom_mem_piece hr0 (hv i) (hY i hp) hps
  have hwvol : ∀ i, volume (zshade r c (v i) (Y i)) ≤ ENNReal.ofReal (384 * (r * δ) ^ 2) :=
    fun i => (measure_mono (hshade_sub i)).trans
      (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ' hδ'1 _ _ (hv i))
  have hwfin : ∀ i, volume (zshade r c (v i) (Y i)) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hwvol i)
  set w : Fin n → ℝ := fun i => (volume (zshade r c (v i) (Y i))).toReal
  have hwM : ∀ i, w i ≤ 384 * (r * δ) ^ 2 := fun i =>
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hwvol i)
  have hw0 : ∀ i, 0 ≤ w i := fun i => ENNReal.toReal_nonneg
  have hzvol : ∀ i, volume (zshade r c (v i) (Y i)) =
      ENNReal.ofReal (r ^ 3) * volume (Y i ∩ zslab r c (v i)) :=
    fun i => volume_zoom_image hr0 c _
  -- the mass carried by the candidates
  have hsumI : ∑ i ∈ I₀, volume (zshade r c (v i) (Y i)) = ENNReal.ofReal (∑ i ∈ I₀, w i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i)]
    exact Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_toReal (hwfin i)).symm)
  have hmassI : r ^ 3 * (δ ^ η₁ * n * δ ^ 2) ≤ (Ng r : ℝ) * ∑ i ∈ I₀, w i := by
    have h1 : ENNReal.ofReal (r ^ 3) * ENNReal.ofReal (δ ^ η₁ * n * δ ^ 2) ≤
        (Ng r : ℝ≥0∞) * ∑ i ∈ I₀, volume (zshade r c (v i) (Y i)) := by
      calc ENNReal.ofReal (r ^ 3) * ENNReal.ofReal (δ ^ η₁ * n * δ ^ 2)
          ≤ ENNReal.ofReal (r ^ 3) * ((Ng r : ℝ≥0∞) *
              ∑ i ∈ I₀, volume (Y i ∩ zslab r c (v i))) := by
            gcongr; exact hmass.trans hcentre
        _ = (Ng r : ℝ≥0∞) * ∑ i ∈ I₀, volume (zshade r c (v i) (Y i)) := by
            rw [mul_left_comm, Finset.mul_sum]
            congr 1
            exact Finset.sum_congr rfl (fun i _ => (hzvol i).symm)
    rw [hsumI, ← ENNReal.ofReal_mul (by positivity),
      show ((Ng r : ℕ) : ℝ≥0∞) = ENNReal.ofReal (Ng r : ℝ) by simp,
      ← ENNReal.ofReal_mul (by positivity)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by
      exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hw0 i))).mp h1
  -- colouring of fine conflicts
  obtain ⟨colf, hcolf⟩ := color_of_degree (FConf r δ c x v) (fun h => h.symm)
    (fun i => fconf_card_le hr hδ hP1 x v hv hsep i)
  obtain ⟨af, hfine⟩ := heavy_class (Nat.succ_pos _) colf w I₀
  set P₀ := I₀.filter (fun i => colf i = af)
  -- the net of scales
  obtain ⟨s, hs, hnet⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.power_net
    (η := η / 4) hδ' hδ'1 hN hgap
  let L := {j : Fin (N + 1) // s j ≤ (r * δ) ^ (η / 4)}
  let u : L → ℝ := fun l => max δ (s l.1 / (8 * r))
  have hu : ∀ l, δ ≤ u l ∧ u l ≤ 1 := by
    intro l
    refine ⟨le_max_left _ _, max_le hδ1' ?_⟩
    rw [div_le_one (by positivity)]
    linarith [(hs l.1).2]
  have hcov_ex : ∀ l : L, ∃ ρ : ℝ, u l ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η₁) * u l ∧
      ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space,
        CoverAt δ (δ ^ (-η₁)) ρ x v z w ∧ SeparatedAt δ ρ x v z w :=
    fun l => hS (u l) (hu l).1 (hu l).2
  choose ρ hρu hρ1 hρK k hk z wv hcov hsepc using hcov_ex
  have hfex : ∀ l, ∃ f : Fin n → Fin (k l), ∀ i j,
      Tube δ (x i) (v i) ⊆ Tube (ρ l) (z l j) (wv l j) ↔ f i = j := by
    intro l
    have huniq := (hcov l).2.2.1
    choose f hf using (fun i => (huniq i).exists)
    exact ⟨f, fun i j => ⟨fun hij => (huniq i).unique (hf i) hij, fun hij => hij ▸ hf i⟩⟩
  choose f hf using hfex
  have hρδ : ∀ l, δ ≤ ρ l := fun l => (hu l).1.trans (hρu l)
  have hρr : ∀ l, ρ l ≤ 1 / (131072 * r) := by
    intro l
    refine (hρK l).trans ?_
    rcases le_total δ (s l.1 / (8 * r)) with hcase | hcase
    · simp only [u, max_eq_right hcase]
      have hsl : s l.1 ≤ (r * δ) ^ (η / 4) := l.2
      calc δ ^ (-η₁) * (s l.1 / (8 * r)) ≤ δ ^ (-η₁) * ((r * δ) ^ (η / 4) / (8 * r)) := by
            gcongr
        _ = (δ ^ (-η₁) * (r * δ) ^ (η / 4)) / (8 * r) := by ring
        _ ≤ (1 / 16384) / (8 * r) := by gcongr
        _ = 1 / (131072 * r) := by field_simp; ring
    · simp only [u, max_eq_left hcase]; exact hP4'
  -- colouring of coarse conflicts at each scale
  have hcolex : ∀ l, ∃ col : Fin (k l) → Fin (Kc r), ∀ j j', j ≠ j' →
      CConf r δ (ρ l) c I₀ x v (z l) (wv l) j j' → col j ≠ col j' := by
    intro l
    exact color_of_degree _ (fun h => h.symm) (fun j => cconf_card_le hr hδ (hρδ l) (hρr l)
      I₀ x v (z l) (wv l) hv (hcov l).1 (hcov l).2.1 j)
  choose col hcol using hcolex
  -- selection
  obtain ⟨Q, hQP, hret, hsame, hQmass⟩ := select_in (fun l : L => Fin (k l)) f
    (Nat.succ_pos _) col w (M := 384 * (r * δ) ^ 2) (t := tpar δ η₁ r N) (by positivity)
    (tpar_pos hδ hr0 N) hwM P₀
  set t := tpar δ η₁ r N
  have ht : 0 < t := tpar_pos hδ hr0 N
  have hKc1 : (1 : ℝ) ≤ Kc r := by unfold Kc; exact_mod_cast Nat.succ_pos _
  have hcardL : Fintype.card L ≤ N + 1 := by
    calc Fintype.card L ≤ Fintype.card (Fin (N + 1)) := Fintype.card_subtype_le _
      _ = N + 1 := Fintype.card_fin _
  have hpowL : (Kc r : ℝ) ^ Fintype.card L ≤ (Kc r : ℝ) ^ (N + 1) :=
    pow_le_pow_right₀ hKc1 hcardL
  set mQ := 384 * (r * δ) ^ 2 * n * t * (N + 2)
  have hNg : (0 : ℝ) < Ng r := by unfold Ng; positivity
  set Dd : ℝ := Ng r * Kc r * (Kc r : ℝ) ^ (N + 1)
  have hDd : 0 < Dd := by positivity
  have hAD : r ^ 3 * (δ ^ η₁ * n * δ ^ 2) / Dd = 2 * mQ := by
    rw [div_eq_iff hDd.ne']
    simp only [mQ, t, tpar, Dd]
    field_simp
    ring
  have hQmass' : mQ ≤ ∑ i ∈ Q, w i := by
    have hA : r ^ 3 * (δ ^ η₁ * n * δ ^ 2) / Dd ≤
        (∑ i ∈ P₀, w i) / (Kc r : ℝ) ^ Fintype.card L := by
      have h1 : r ^ 3 * (δ ^ η₁ * n * δ ^ 2) / (Ng r * Kc r) ≤ ∑ i ∈ P₀, w i := by
        calc r ^ 3 * (δ ^ η₁ * n * δ ^ 2) / (Ng r * Kc r)
            ≤ ((Ng r : ℝ) * ∑ i ∈ I₀, w i) / (Ng r * Kc r) := by gcongr
          _ = (∑ i ∈ I₀, w i) / Kc r := by field_simp
          _ ≤ ∑ i ∈ P₀, w i := hfine
      calc r ^ 3 * (δ ^ η₁ * n * δ ^ 2) / Dd
          = (r ^ 3 * (δ ^ η₁ * n * δ ^ 2) / (Ng r * Kc r)) / (Kc r : ℝ) ^ (N + 1) := by
            simp only [Dd]; field_simp
        _ ≤ (∑ i ∈ P₀, w i) / (Kc r : ℝ) ^ (N + 1) := by gcongr
        _ ≤ (∑ i ∈ P₀, w i) / (Kc r : ℝ) ^ Fintype.card L := by
            apply div_le_div_of_nonneg_left (Finset.sum_nonneg fun i _ => hw0 i)
              (by positivity) hpowL
    have hB : 384 * (r * δ) ^ 2 * t * ((Fintype.card L : ℝ) * Fintype.card (Fin n)) ≤
        384 * (r * δ) ^ 2 * n * t * (N + 1) := by
      rw [Fintype.card_fin]
      have : (Fintype.card L : ℝ) ≤ N + 1 := by exact_mod_cast hcardL
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have h384 : 0 ≤ 384 * (r * δ) ^ 2 * t := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg h384 hn0)]
    have hm0 : 0 ≤ 384 * (r * δ) ^ 2 * n * t := by positivity
    have hC : mQ ≤ 2 * mQ - 384 * (r * δ) ^ 2 * n * t * (N + 1) := by
      simp only [mQ]; nlinarith
    rw [hAD] at hA
    rw [Fintype.card_fin] at hQmass hB
    change (∑ i ∈ P₀, w i) / (Kc r : ℝ) ^ Fintype.card L - _ ≤ _ at hQmass
    linarith
  -- the selected family is nonempty and not too small
  have hmQpos : 0 < mQ := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [mQ]; positivity
  have hQne : Q.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hQmass'
    linarith only [hQmass', hmQpos]
  have hQcard : (n : ℝ) * t ≤ Q.card := by
    have h1 : ∑ i ∈ Q, w i ≤ Q.card * (384 * (r * δ) ^ 2) := by
      calc ∑ i ∈ Q, w i ≤ ∑ _i ∈ Q, 384 * (r * δ) ^ 2 := Finset.sum_le_sum fun i _ => hwM i
        _ = Q.card * (384 * (r * δ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : mQ ≤ Q.card * (384 * (r * δ) ^ 2) := hQmass'.trans h1
    have h3 : (n : ℝ) * t * (384 * (r * δ) ^ 2) ≤ Q.card * (384 * (r * δ) ^ 2) := by
      have h4 : (n : ℝ) * t * (384 * (r * δ) ^ 2) ≤ mQ := by
        simp only [mQ]
        have h5 : (0 : ℝ) ≤ 384 * (r * δ) ^ 2 * n * t := by positivity
        have h6 : (1 : ℝ) ≤ N + 2 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
        calc (n : ℝ) * t * (384 * (r * δ) ^ 2) = 384 * (r * δ) ^ 2 * n * t * 1 := by ring
          _ ≤ 384 * (r * δ) ^ 2 * n * t * (N + 2) := mul_le_mul_of_nonneg_left h6 h5
      exact h4.trans h2
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hQn : (Q.card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_le_card (Finset.subset_univ Q)).trans_eq (by simp)
  have hQI : Q ⊆ I₀ := hQP.trans (Finset.filter_subset _ _)
  -- the new family
  set e := enumerate Q
  have hemem : ∀ a, e a ∈ Q := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_mem Q
  have heinj : Function.Injective e :=
    WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_injective Q
  set x' : Fin Q.card → Space := fun a => pieceBase r c (x (e a)) (v (e a))
  set v' : Fin Q.card → Space := fun a => v (e a)
  set Y' : Fin Q.card → Set Space := fun a => zshade r c (v (e a)) (Y (e a))
  have hFN : ∀ a, FNear r c (x (e a)) (v (e a)) := fun a => hI₀ _ (hQI (hemem a))
  have hball' : ∀ a, Tube (r * δ) (x' a) (v' a) ⊆ ball 0 1 := by
    intro a
    apply piece_subset_ball (hv _) _ hP2
    rw [show zoom r c (cpt c (x (e a)) (v (e a))) = r • (cpt c (x (e a)) (v (e a)) - c) from rfl,
      norm_smul, Real.norm_of_nonneg hr0.le]
    calc r * ‖cpt c (x (e a)) (v (e a)) - c‖ ≤ r * (1 / (8 * r)) :=
          mul_le_mul_of_nonneg_left (hFN a).1 hr0.le
      _ ≤ 1 / 4 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith only [hr]
  have hcompact' : ∀ a, IsCompact (Y' a) := fun a =>
    ((hcomp _).inter_right (zslab_closed r c _)).image (by unfold zoom; fun_prop)
  have hdense : Dense η (r * δ) Q.card x' v' Y' := by
    refine ⟨Finset.card_pos.mpr hQne, fun a => hv _, hball', ?_, fun a => (hcompact' a).measurableSet,
      fun a => hshade_sub _, ?_⟩
    · intro a a' haa'
      have hne : e a ≠ e a' := heinj.ne haa'
      have hcolor : colf (e a) = colf (e a') := by
        have h1 := (Finset.mem_filter.mp (hQP (hemem a))).2
        have h2 := (Finset.mem_filter.mp (hQP (hemem a'))).2
        rw [h1, h2]
      have hnot : ¬ FConf r δ c x v (e a) (e a') := fun h => hcolf _ _ hne h hcolor
      have hpar : ∀ b, cpar c (x (e b)) (v (e b)) ∈ Icc (-(1 / 4) : ℝ) (5 / 4) := by
        intro b
        have h8 : 1 / (8 * r) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hr]
        exact ⟨by linarith only [(hFN b).2.1, h8], by linarith only [(hFN b).2.2, h8]⟩
      by_contra hlt
      exact hnot ⟨hpar a, hpar a', Or.inl (lt_of_not_ge hlt)⟩
    · rw [WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_sum Q
        (fun i => volume (zshade r c (v i) (Y i)))]
      have hsumQ : ∑ i ∈ Q, volume (zshade r c (v i) (Y i)) = ENNReal.ofReal (∑ i ∈ Q, w i) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i)]
        exact Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_toReal (hwfin i)).symm)
      rw [hsumQ]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (r * δ) ^ η * Q.card * (r * δ) ^ 2 ≤ 384 * t * n * (r * δ) ^ 2 := by
        have h7 := mul_le_mul hP8 hQn (Nat.cast_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right h7 (sq_nonneg _)
      have h2 : 384 * t * n * (r * δ) ^ 2 ≤ mQ := by
        simp only [mQ]
        have h5 : (0 : ℝ) ≤ 384 * (r * δ) ^ 2 * n * t := by positivity
        have h6 : (1 : ℝ) ≤ N + 2 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
        calc 384 * t * n * (r * δ) ^ 2 = 384 * (r * δ) ^ 2 * n * t * 1 := by ring
          _ ≤ 384 * (r * δ) ^ 2 * n * t * (N + 2) := mul_le_mul_of_nonneg_left h6 h5
      exact (h1.trans h2).trans hQmass'
  -- the separated covers of the new family
  have hK'pos : 0 < (r * δ) ^ (-η) := Real.rpow_pos_of_pos hδ' _
  have hK'1 : 1 ≤ (r * δ) ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ' hδ'1 (by linarith only [hη])
  have hr2 : 1 ≤ r ^ 2 := by nlinarith only [hr]
  have hKt : δ ^ (-η₁) ≤ (r * δ) ^ (-η) * t := by
    refine le_trans ?_ hP7
    have : δ ^ (-η₁) ≤ r ^ 2 * δ ^ (-η₁) := le_mul_of_one_le_left hKpos.le hr2
    nlinarith only [this, hKpos]
  have hold := global_frostman hδ hδ1' hball hS
  have hstrong : Strong η (r * δ) Q.card x' v' := by
    intro r' hr'δ hr'1
    obtain ⟨j, hj1, hj2⟩ := hnet r' hr'δ hr'1
    by_cases hjL : s j ≤ (r * δ) ^ (η / 4)
    · let l : L := ⟨j, hjL⟩
      obtain ⟨k', hk', z', w', hcov', hsep'⟩ := zoom_cover (K' := (r * δ) ^ (-η)) hr hδ (hρδ l)
        (hρr l) hP2 ht hKpos hKt (by simpa only [mul_comm] using hP7) hv (hcov l) (f l) (hf l)
        I₀ hI₀ Q hQI hQne (hret l) (col l) (hcol l) (hsame l)
      refine ⟨8 * r * ρ l, ?_, ?_, ?_, k', hk', z', w', hcov', hsep'⟩
      · have h1 : s j / (8 * r) ≤ u l := le_max_right _ _
        have h2 : s j ≤ 8 * r * u l := by
          rw [div_le_iff₀ (by positivity)] at h1; linarith only [h1]
        have h3 : 8 * r * u l ≤ 8 * r * ρ l := mul_le_mul_of_nonneg_left (hρu l) (by positivity)
        linarith only [hj1, h2, h3]
      · have := hρr l
        calc 8 * r * ρ l ≤ 8 * r * (1 / (131072 * r)) := mul_le_mul_of_nonneg_left this (by positivity)
          _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; nlinarith only [hr]
      · have hK := hρK l
        rcases le_total δ (s j / (8 * r)) with hcase | hcase
        · have hu : u l = s j / (8 * r) := max_eq_right hcase
          calc 8 * r * ρ l ≤ 8 * r * (δ ^ (-η₁) * u l) :=
                mul_le_mul_of_nonneg_left hK (by positivity)
            _ = δ ^ (-η₁) * s j := by rw [hu]; field_simp
            _ ≤ δ ^ (-η₁) * ((r * δ) ^ (-(η / 4)) * r') :=
                mul_le_mul_of_nonneg_left hj2 hKpos.le
            _ = (δ ^ (-η₁) * (r * δ) ^ (-(η / 4))) * r' := by ring
            _ ≤ (r * δ) ^ (-η) * r' := mul_le_mul_of_nonneg_right hP5' (by linarith only [hr'δ, hδ'])
        · have hu : u l = δ := max_eq_left hcase
          calc 8 * r * ρ l ≤ 8 * r * (δ ^ (-η₁) * u l) :=
                mul_le_mul_of_nonneg_left hK (by positivity)
            _ = (8 * δ ^ (-η₁)) * (r * δ) := by rw [hu]; ring
            _ ≤ (r * δ) ^ (-η) * (r * δ) := mul_le_mul_of_nonneg_right hP5 hδ'.le
            _ ≤ (r * δ) ^ (-η) * r' := mul_le_mul_of_nonneg_left hr'δ hK'pos.le
    · replace hjL := not_le.mp hjL
      have hbig : (r * δ) ^ η ≤ r' := by
        have h1 : (r * δ) ^ (η / 4) * (r * δ) ^ (η / 4) ≤ s j * (r * δ) ^ (η / 4) :=
          mul_le_mul_of_nonneg_right hjL.le (Real.rpow_nonneg hδ'.le _)
        have h2 : s j * (r * δ) ^ (η / 4) ≤ r' := by
          have := mul_le_mul_of_nonneg_right hj2 (Real.rpow_nonneg hδ'.le (η / 4))
          calc s j * (r * δ) ^ (η / 4) ≤ (r * δ) ^ (-(η / 4)) * r' * (r * δ) ^ (η / 4) := this
            _ = r' := by
              rw [mul_comm ((r * δ) ^ (-(η / 4))) r', mul_assoc, ← Real.rpow_add hδ',
                neg_add_cancel, Real.rpow_zero, mul_one]
        have h3 : (r * δ) ^ η ≤ (r * δ) ^ (η / 4) * (r * δ) ^ (η / 4) := by
          rw [← Real.rpow_add hδ']
          exact Real.rpow_le_rpow_of_exponent_ge hδ' hδ'1 (by linarith only [hη])
        linarith only [h1, h2, h3]
      have hfr : ∀ W : Set Space, Convex ℝ W →
          ENNReal.ofReal (ncard {a | Tube (r * δ) (x' a) (v' a) ⊆ W} : ℝ) ≤
            ENNReal.ofReal ((r * δ) ^ (-η) * Q.card) * volume W := by
        intro W hW
        have h1 := zoom_global_frostman hr hδ hP2 hv (A := δ ^ (-η₁) * n)
          (by have : (0 : ℝ) < n := by exact_mod_cast hn
              positivity) hold Q (fun i hi => hI₀ i (hQI hi)) W hW
        refine h1.trans ?_
        gcongr ENNReal.ofReal ?_ * _
        have h2 : 432 * 512 * δ ^ (-η₁) ≤ (r * δ) ^ (-η) * t := by
          refine le_trans ?_ hP7
          have : 432 * 512 * δ ^ (-η₁) ≤ 64 * (432 * 512) * δ ^ (-η₁) := by
            nlinarith only [hKpos]
          nlinarith only [this, hr2, hKpos]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        calc 432 * 512 * (δ ^ (-η₁) * n) = (432 * 512 * δ ^ (-η₁)) * n := by ring
          _ ≤ ((r * δ) ^ (-η) * t) * n := mul_le_mul_of_nonneg_right h2 hn0
          _ = (r * δ) ^ (-η) * (n * t) := by ring
          _ ≤ (r * δ) ^ (-η) * Q.card := mul_le_mul_of_nonneg_left hQcard hK'pos.le
      obtain ⟨z', w', hcov', hsep'⟩ := single_cover (Finset.card_pos.mpr hQne) hK'1 hball' hfr
      refine ⟨1, hr'1, le_rfl, ?_, 1, one_pos, z', w', hcov', hsep'⟩
      calc (1 : ℝ) = (r * δ) ^ (-η) * (r * δ) ^ η := by
            rw [← Real.rpow_add hδ', neg_add_cancel, Real.rpow_zero]
        _ ≤ (r * δ) ^ (-η) * r' := mul_le_mul_of_nonneg_left hbig hK'pos.le
  -- volume and grains
  have hvol' : volume (⋃ a, Y' a) ≤ ENNReal.ofReal ((r * δ) ^ (σ - η)) := by
    have hsub : (⋃ a, Y' a) ⊆ zoom r c '' ⋃ i, Y i := by
      intro p hp
      obtain ⟨a, ha⟩ := mem_iUnion.mp hp
      obtain ⟨q, ⟨hq, -⟩, rfl⟩ := ha
      exact ⟨q, mem_iUnion.mpr ⟨e a, hq⟩, rfl⟩
    calc volume (⋃ a, Y' a) ≤ volume (zoom r c '' ⋃ i, Y i) := measure_mono hsub
      _ = ENNReal.ofReal (r ^ 3) * volume (⋃ i, Y i) := volume_zoom_image hr0 c _
      _ ≤ ENNReal.ofReal (r ^ 3) * ENNReal.ofReal (δ ^ (σ - η₁)) := by gcongr
      _ = ENNReal.ofReal (r ^ 3 * δ ^ (σ - η₁)) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal ((r * δ) ^ (σ - η)) := ENNReal.ofReal_le_ofReal hP9
  exact ⟨c, Q.card, e, ⟨hdense, hstrong, hcompact', hvol'⟩⟩

/-- The zoomed family at scale `r δ` with its grains, under explicit parameter conditions. -/
theorem zoom_family {σ η η₁ δ r : ℝ} {n N : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    {g : ℝ → ℝ} {P : Space → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hr : 16 ≤ r) (hη : 0 < η) (hη₁ : 0 < η₁)
    (hN : 0 < N) (hgap : (N : ℝ)⁻¹ ≤ η / 4)
    (hfam : ExtremalFamily σ η₁ δ n x v Y) (hgr : Grains σ δ (δ ^ (-η₁)) v Y g P)
    (hP1 : δ ≤ 1 / (131072 * r)) (hP2 : r * δ ≤ 1 / 8)
    (hP4 : δ ^ (-η₁) * (r * δ) ^ (η / 4) ≤ 1 / 16384)
    (hP4' : δ ^ (-η₁) * δ ≤ 1 / (131072 * r))
    (hP5 : 8 * δ ^ (-η₁) ≤ (r * δ) ^ (-η))
    (hP5' : δ ^ (-η₁) * (r * δ) ^ (-(η / 4)) ≤ (r * δ) ^ (-η))
    (hP7 : 64 * (432 * 512) * r ^ 2 * δ ^ (-η₁) ≤ (r * δ) ^ (-η) * tpar δ η₁ r N)
    (hP8 : (r * δ) ^ η ≤ 384 * tpar δ η₁ r N)
    (hP9 : r ^ 3 * δ ^ (σ - η₁) ≤ (r * δ) ^ (σ - η)) :
    ∃ (c : Space) (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      ExtremalFamily σ η (r * δ) m x' v' Y' ∧
      Grains σ (r * δ) (δ ^ (-η₁)) v' Y' (fun t => g (c 2 + t / r))
        (fun p => P (unzoom r c p)) := by
  obtain ⟨c, m, e, hfam'⟩ := zoom_family_core hδ hδ1 hr hη hη₁ hN hgap hfam hP1 hP2 hP4 hP4'
    hP5 hP5' hP7 hP8 hP9
  have hballY : ∀ p ∈ ⋃ i, Y i, ‖p‖ < 1 := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    simpa using hfam.1.2.2.1 i (hfam.1.2.2.2.2.2.1 i hi)
  have hδ1' : δ ≤ 1 := by linarith
  have hKpos : 0 < δ ^ (-η₁) := Real.rpow_pos_of_pos hδ _
  exact ⟨c, m, _, _, _, hfam', hgr.zoomed (r := r) hδ hδ1' (by linarith) hKpos.le hballY e c⟩

end

end WangZahlLot.Obl.wz_c2_slope_normalization
