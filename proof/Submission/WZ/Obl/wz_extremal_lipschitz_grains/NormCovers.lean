-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormCovers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormFamily

/-!
# Covers of the zoomed family

An original balanced, locally Frostman cover at scale `ρ`, restricted to the covers met by `Q`
and zoomed (radius `25 lam ρ`), is a cover of the zoomed family: non-conflicting pieces are
half-distinct and contain no common zoomed fine piece, so the zoomed fibres are the original
fibres intersected with `Q`; the retention bound transfers balance, and the difference body
transfers the local convex counts.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory Finset
open scoped ENNReal
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_mem enumerate_injective
  enumerate_surjective enumerate_sum enumerate_count CoverAt ncard_setOf)

/-- The zoom preimage of an open convex set is open and convex. -/
theorem zoom_preimage_isOpen_convex {c : Space} {lam : ℝ} {U' : Set Space} (hU'o : IsOpen U')
    (hU' : Convex ℝ U') :
    IsOpen (zoom c lam ⁻¹' U') ∧ Convex ℝ (zoom c lam ⁻¹' U') := by
  constructor
  · exact hU'o.preimage ((continuous_const_smul lam).comp (continuous_id.sub continuous_const))
  · intro p hp q hq a b ha hb hab
    show zoom c lam (a • p + b • q) ∈ U'
    have he : zoom c lam (a • p + b • q) = a • zoom c lam p + b • zoom c lam q := by
      have h1 : a • p + b • q - c = a • (p - c) + b • (q - c) := by
        calc a • p + b • q - c = a • p + b • q - (a + b) • c := by rw [hab, one_smul]
          _ = a • (p - c) + b • (q - c) := by module
      simp only [zoom]
      rw [h1]
      module
    rw [he]
    exact hU' hp hq ha hb hab

theorem volume_zoom_preimage {c : Space} {lam : ℝ} (hlam : 0 < lam) (U' : Set Space) :
    ENNReal.ofReal (lam ^ 3) * volume (zoom c lam ⁻¹' U') = volume U' := by
  rw [← volume_zoom_image hlam]
  congr 1
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro hq
    refine ⟨c + lam⁻¹ • q, ?_, ?_⟩
    · show zoom c lam (c + lam⁻¹ • q) ∈ U'
      simpa [zoom, smul_smul, mul_inv_cancel₀ hlam.ne'] using hq
    · simp [zoom, smul_smul, mul_inv_cancel₀ hlam.ne']

/-- The foot lies in the original piece. -/
theorem foot_mem_subTube {c : Space} {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (x v : Space) :
    foot c x v ∈ subTube c lam δ x v := by
  refine mem_tube_iff.mpr ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
  have h : foot c x v - (foot c x v - (1 / (2 * lam)) • v + (1 / 2 : ℝ) • (1 / lam) • v) = 0 := by
    rw [smul_smul, show (1 / 2 : ℝ) * (1 / lam) = 1 / (2 * lam) by field_simp]; abel
  rw [h, norm_zero]; exact hδ

open scoped Classical in
/-- One level of covers of the zoomed family. -/
theorem coverAt_zoom {n k : ℕ} {c : Space} {lam δ ρ K₀ t : ℝ} {x v : Fin n → Space}
    {z w : Fin k → Space} (f : Fin n → Fin k) {Q : Finset (Fin n)}
    (hlam : 1 ≤ lam) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hR : lam * (25 * ρ) ≤ 1 / 10000)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ j, ‖w j‖ = 1)
    (hsep : ∀ j j', j ≠ j' → volume (tube ρ (z j) (w j) ∩ tube ρ (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (tube ρ (z j) (w j)))
    (hf : ∀ i j, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ↔ f i = j)
    (hbal : ∀ j j', ((univ.filter (fun i => f i = j)).card : ℝ) ≤
      K₀ * ((univ.filter (fun i => f i = j')).card : ℝ))
    (hfrost : ∀ j (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (((univ.filter (fun i => f i = j ∧ tube δ (x i) (v i) ⊆ W)).card : ℝ) *
        ρ ^ 2) ≤ ENNReal.ofReal (K₀ * ((univ.filter (fun i => f i = j)).card : ℝ)) * volume W)
    (hK₀ : 0 ≤ K₀) (ht : 0 < t)
    (hQ : Q ⊆ zoomThrough c lam x v) (hQne : Q.Nonempty)
    (hnc : ∀ i ∈ Q, ∀ i' ∈ Q, f i ≠ f i' →
      ¬ conflict c lam (lam * (25 * ρ)) z w (fun j => ∃ i ∈ zoomThrough c lam x v, f i = j) (f i) (f i'))
    (hret : ∀ j, (Q.filter (fun i => f i = j)).Nonempty →
      t * ((univ.filter (fun i => f i = j)).card : ℝ) ≤ ((Q.filter (fun i => f i = j)).card : ℝ)) :
    ∃ k' : ℕ, 0 < k' ∧ ∃ z' w' : Fin k' → Space,
      CoverAt (lam * δ) (5000000 * lam ^ 2 * K₀ / t) (lam * (25 * ρ))
        (zx c lam x v Q) (zv v Q) z' w' := by
  classical
  have hlam0 : 0 < lam := by linarith
  have hρ : 0 < ρ := hδ.trans_le hδρ
  set R := lam * (25 * ρ) with hRdef
  have hR0 : 0 < R := by positivity
  set U : Fin k → Prop := fun j => ∃ i ∈ zoomThrough c lam x v, f i = j with hU
  set G := Q.image f with hG
  set b := enumerate G with hb
  have hbmem : ∀ j, b j ∈ G := enumerate_mem G
  have hbinj : Function.Injective b := enumerate_injective G
  have hGpos : 0 < G.card := card_pos.mpr (hQne.image f)
  -- containment of each zoomed fine piece in the zoomed piece of its cover
  have hcont : ∀ i ∈ Q, tube (lam * δ) (pieceStart c lam (x i) (v i)) (v i) ⊆
      tube R (pieceStart c lam (z (f i)) (w (f i))) (w (f i)) := by
    intro i hi
    have hthr := hQ hi
    exact piece_subset_piece hlam0 hδ hδρ (hv i) (hw (f i)) ((hf i (f i)).mpr rfl)
      (param_mem_of_mem_through hv hthr)
      (by
        have : 1 / (4 * lam) + 1 / (2 * lam) = 3 / (4 * lam) := by field_simp; ring
        rw [this, div_le_one (by positivity)]; linarith)
      (norm_sub_x_le_of_mem_through hlam hv hthr)
  -- the fibre identity
  have hfib : ∀ (a : Fin Q.card) (j : Fin k), j ∈ G →
      (tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube R (pieceStart c lam (z j) (w j)) (w j) ↔ f (enumerate Q a) = j) := by
    intro a j hj
    constructor
    · intro hsub
      by_contra hne
      obtain ⟨i', hi'Q, hi'j⟩ := mem_image.mp hj
      have hia := enumerate_mem Q a
      have hncf := hnc _ hia i' hi'Q (by rw [hi'j]; exact hne)
      have hUa : U (f (enumerate Q a)) := ⟨enumerate Q a, hQ hia, rfl⟩
      have hUj : U (f i') := ⟨i', hQ hi'Q, rfl⟩
      exact not_common_of_not_conflict (by positivity) hw hUa hUj
        (by rw [hi'j]; exact hne) hncf (hv _) (hcont _ hia) (by rw [hi'j]; exact hsub)
    · intro he
      rw [← he]
      exact hcont _ (enumerate_mem Q a)
  have hoccupied : ∀ j', (Q.filter (fun i => f i = b j')).Nonempty := by
    intro j'
    obtain ⟨i, hi, he⟩ := mem_image.mp (hbmem j')
    exact ⟨i, mem_filter.mpr ⟨hi, he⟩⟩
  have hnew : ∀ j', ncard {a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
      tube R (pieceStart c lam (z (b j')) (w (b j'))) (w (b j'))} =
      (Q.filter (fun i => f i = b j')).card := by
    intro j'
    have : {a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube R (pieceStart c lam (z (b j')) (w (b j'))) (w (b j'))} =
        {a | f (enumerate Q a) = b j'} := by
      ext a; exact hfib a (b j') (hbmem j')
    rw [this]
    exact enumerate_count Q (fun i => f i = b j')
  refine ⟨G.card, hGpos, fun j' => pieceStart c lam (z (b j')) (w (b j')), fun j' => w (b j'),
    fun j' => hw _, ?_, ?_, ?_, ?_, ?_⟩
  · -- distinct pieces
    intro j₁ j₂ hne
    have hne' : b j₁ ≠ b j₂ := hbinj.ne hne
    obtain ⟨i₁, hi₁, he₁⟩ := mem_image.mp (hbmem j₁)
    obtain ⟨i₂, hi₂, he₂⟩ := mem_image.mp (hbmem j₂)
    have hncf := hnc i₁ hi₁ i₂ hi₂ (by rw [he₁, he₂]; exact hne')
    rw [he₁, he₂] at hncf
    exact half_of_not_conflict hR0 hR hw ⟨i₁, hQ hi₁, he₁⟩ ⟨i₂, hQ hi₂, he₂⟩ hne' hncf
  · -- unique containment
    intro a
    obtain ⟨j₀, hj₀⟩ := enumerate_surjective G
      (mem_image.mpr ⟨enumerate Q a, enumerate_mem Q a, rfl⟩)
    refine ⟨j₀, ?_, ?_⟩
    · show tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube R (pieceStart c lam (z (b j₀)) (w (b j₀))) (w (b j₀))
      exact (hfib a (b j₀) (hbmem j₀)).mpr hj₀.symm
    · intro j₁ hj₁
      have h1 : f (enumerate Q a) = b j₁ := (hfib a (b j₁) (hbmem j₁)).mp hj₁
      exact hbinj (h1.symm.trans hj₀.symm)
  · -- nonempty fibres
    intro j'
    obtain ⟨i, hi⟩ := hoccupied j'
    obtain ⟨hiQ, hij⟩ := mem_filter.mp hi
    obtain ⟨a, rfl⟩ := enumerate_surjective Q hiQ
    exact ⟨a, (hfib a (b j') (hbmem j')).mpr hij⟩
  · -- balance
    intro j₁ j₂
    have hn1 := hnew j₁
    have hn2 := hnew j₂
    show (ncard {a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube R (pieceStart c lam (z (b j₁)) (w (b j₁))) (w (b j₁))} : ℝ) ≤
      5000000 * lam ^ 2 * K₀ / t * (ncard {a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a)
        (zv v Q a) ⊆ tube R (pieceStart c lam (z (b j₂)) (w (b j₂))) (w (b j₂))} : ℝ)
    rw [hn1, hn2]
    have h1 : ((Q.filter (fun i => f i = b j₁)).card : ℝ) ≤
        ((univ.filter (fun i => f i = b j₁)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (filter_subset_filter _ (subset_univ Q))
    have h2 := hbal (b j₁) (b j₂)
    have h3 := hret (b j₂) (hoccupied j₂)
    have hK : K₀ / t ≤ 5000000 * lam ^ 2 * K₀ / t := by
      apply div_le_div_of_nonneg_right _ ht.le
      have : 1 ≤ 5000000 * lam ^ 2 := by nlinarith
      nlinarith
    calc ((Q.filter (fun i => f i = b j₁)).card : ℝ) ≤
          K₀ * ((univ.filter (fun i => f i = b j₂)).card : ℝ) := h1.trans h2
      _ ≤ K₀ * (((Q.filter (fun i => f i = b j₂)).card : ℝ) / t) := by
          gcongr
          rw [le_div_iff₀ ht]; linarith
      _ = K₀ / t * ((Q.filter (fun i => f i = b j₂)).card : ℝ) := by ring
      _ ≤ 5000000 * lam ^ 2 * K₀ / t * ((Q.filter (fun i => f i = b j₂)).card : ℝ) := by
          gcongr
  · -- local convex counts
    intro j' W hW
    show ENNReal.ofReal ((ncard {a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube R (pieceStart c lam (z (b j')) (w (b j'))) (w (b j')) ∧
        tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆ W} : ℝ) * R ^ 2) ≤
      ENNReal.ofReal (5000000 * lam ^ 2 * K₀ / t * (ncard {a : Fin Q.card |
        tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
          tube R (pieceStart c lam (z (b j')) (w (b j'))) (w (b j'))} : ℝ)) * volume W
    rw [hnew j']
    have hset : {a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube R (pieceStart c lam (z (b j')) (w (b j'))) (w (b j')) ∧
        tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆ W} =
        {a | (fun i => f i = b j' ∧ tube (lam * δ) (pieceStart c lam (x i) (v i)) (v i) ⊆ W)
          (enumerate Q a)} := by
      ext a
      simp only [mem_ofPred_eq]
      rw [hfib a (b j') (hbmem j')]
      rfl
    have hcnt := enumerate_count Q
      (fun i => f i = b j' ∧ tube (lam * δ) (pieceStart c lam (x i) (v i)) (v i) ⊆ W)
    rw [hset, hcnt]
    set A := Q.filter (fun i => f i = b j' ∧ tube (lam * δ) (pieceStart c lam (x i) (v i)) (v i) ⊆ W)
      with hA
    rcases A.eq_empty_or_nonempty with hAe | ⟨i₀, hi₀⟩
    · rw [hAe, Finset.card_empty, Nat.cast_zero, zero_mul, ENNReal.ofReal_zero]
      exact zero_le
    obtain ⟨hi₀Q, hi₀f, hi₀W⟩ := by simpa [hA] using hi₀
    set U' := interior W with hU'
    have hU'o : IsOpen U' := isOpen_interior
    have hU'c : Convex ℝ U' := hW.interior
    set U := zoom c lam ⁻¹' U' with hUdef
    obtain ⟨hUo, hUc⟩ := zoom_preimage_isOpen_convex (c := c) (lam := lam) hU'o hU'c
    have hsubU : ∀ i ∈ A, subTube c lam δ (x i) (v i) ⊆ U := by
      intro i hi p hp
      obtain ⟨-, -, hiW⟩ := by simpa [hA] using hi
      have hpiece := zoom_mem_piece hlam0 hp
      exact interior_maximal hiW isOpen_thickening hpiece
    have hp₀ : foot c (x i₀) (v i₀) ∈ U := hsubU i₀ hi₀ (foot_mem_subTube hlam0 hδ _ _)
    set κ := 2 + (1 + 2) * lam with hκ
    have hκ0 : 0 ≤ κ := by positivity
    set E := enlarge (foot c (x i₀) (v i₀)) κ U with hE
    have hEc : Convex ℝ E := convex_enlarge hUc _ _
    have hsubE : A ⊆ univ.filter (fun i => f i = b j' ∧ tube δ (x i) (v i) ⊆ E) := by
      intro i hi
      have hi' := hi
      obtain ⟨hiQ, hif, -⟩ := by simpa [hA] using hi'
      refine mem_filter.mpr ⟨mem_univ _, hif, ?_⟩
      have hpar := param_mem_of_mem_through hv (hQ hiQ)
      have hK : |inner ℝ (c - x i) (v i)| ≤ 2 := by
        rw [abs_le]
        have : 1 / (4 * lam) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        constructor <;> linarith [hpar.1, hpar.2]
      exact tube_subset_enlarge hlam0 hδ hUc (hsubU i hi) hp₀ hK
    have hfr := hfrost (b j') E hEc
    have hvolE := volume_enlarge_le hUo hUc (foot c (x i₀) (v i₀)) hκ0
    have hvolU : ENNReal.ofReal (lam ^ 3) * volume U ≤ volume W :=
      (volume_zoom_preimage hlam0 U').le.trans (measure_mono interior_subset)
    have hcardA : (A.card : ℝ) ≤ ((univ.filter (fun i => f i = b j' ∧
        tube δ (x i) (v i) ⊆ E)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubE
    have hret' := hret (b j') (hoccupied j')
    set Fj := ((univ.filter (fun i => f i = b j')).card : ℝ) with hFj
    set Qj := ((Q.filter (fun i => f i = b j')).card : ℝ) with hQj
    set B := ((univ.filter (fun i => f i = b j' ∧ tube δ (x i) (v i) ⊆ E)).card : ℝ) with hB
    have hlam3 : ENNReal.ofReal (lam ^ 3) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    have hlam3' : ENNReal.ofReal (lam ^ 3) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [← ENNReal.mul_le_mul_iff_right hlam3 hlam3']
    have hκb : κ ≤ 5 * lam := by rw [hκ]; linarith
    calc ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal ((A.card : ℝ) * R ^ 2)
        ≤ ENNReal.ofReal (lam ^ 3) * (ENNReal.ofReal (B * ρ ^ 2) * ENNReal.ofReal (625 * lam ^ 2)) := by
          have hB0 : 0 ≤ B := le_trans (Nat.cast_nonneg _) hcardA
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hR2 : R ^ 2 = 625 * lam ^ 2 * ρ ^ 2 := by rw [hRdef]; ring
          rw [hR2]
          have hpos : 0 ≤ lam ^ 3 * (625 * lam ^ 2 * ρ ^ 2) := by positivity
          have := mul_le_mul_of_nonneg_left hcardA hpos
          nlinarith [this]
      _ = ENNReal.ofReal (625 * lam ^ 2) * (ENNReal.ofReal (B * ρ ^ 2) * ENNReal.ofReal (lam ^ 3)) := by
          ring
      _ ≤ ENNReal.ofReal (625 * lam ^ 2) * ((ENNReal.ofReal (K₀ * Fj) * volume E) *
            ENNReal.ofReal (lam ^ 3)) := by gcongr
      _ = ENNReal.ofReal (625 * lam ^ 2) * ENNReal.ofReal (K₀ * Fj) *
            (ENNReal.ofReal (lam ^ 3) * volume E) := by ring
      _ ≤ ENNReal.ofReal (625 * lam ^ 2) * ENNReal.ofReal (K₀ * Fj) *
            (ENNReal.ofReal (lam ^ 3) * (ENNReal.ofReal (κ ^ 3) * (64 * volume U))) := by gcongr
      _ = ENNReal.ofReal (625 * lam ^ 2) * ENNReal.ofReal (K₀ * Fj) *
            (ENNReal.ofReal (κ ^ 3) * 64) * (ENNReal.ofReal (lam ^ 3) * volume U) := by ring
      _ ≤ ENNReal.ofReal (625 * lam ^ 2) * ENNReal.ofReal (K₀ * Fj) *
            (ENNReal.ofReal (κ ^ 3) * 64) * volume W := by gcongr
      _ = ENNReal.ofReal (625 * lam ^ 2 * (K₀ * Fj) * (κ ^ 3 * 64)) * volume W := by
          have hFj0 : 0 ≤ Fj := by positivity
          rw [ENNReal.ofReal_mul (p := 625 * lam ^ 2 * (K₀ * Fj)) (by positivity),
            ENNReal.ofReal_mul (p := 625 * lam ^ 2) (by positivity),
            ENNReal.ofReal_mul (p := κ ^ 3) (by positivity), ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (lam ^ 3 * (5000000 * lam ^ 2 * K₀ / t * Qj)) * volume W := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          have hFQ : t * Fj ≤ Qj := hret'
          have hκ3 : κ ^ 3 ≤ (5 * lam) ^ 3 := by gcongr
          have hFj0 : 0 ≤ Fj := by positivity
          calc 625 * lam ^ 2 * (K₀ * Fj) * (κ ^ 3 * 64) ≤
                625 * lam ^ 2 * (K₀ * Fj) * ((5 * lam) ^ 3 * 64) := by gcongr
            _ = lam ^ 3 * (5000000 * lam ^ 2 * K₀ / t * (t * Fj)) := by field_simp; ring
            _ ≤ lam ^ 3 * (5000000 * lam ^ 2 * K₀ / t * Qj) := by gcongr
      _ = ENNReal.ofReal (lam ^ 3) * (ENNReal.ofReal (5000000 * lam ^ 2 * K₀ / t * Qj) *
            volume W) := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring

/-- The unit ball lies in the radius-one tube around any unit segment centred at the origin. -/
theorem ball_subset_tube_one {u : Space} (hu : ‖u‖ = 1) :
    ball (0 : Space) 1 ⊆ tube 1 (-(1 / 2 : ℝ) • u) u := by
  intro p hp
  refine mem_tube_iff.mpr ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
  have : p - (-(1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u) = p := by
    rw [neg_smul, neg_add_cancel, sub_zero]
  rw [this]; simpa using hp

open scoped Classical in
/-- The top-level cover of the zoomed family: one radius-one tube. -/
theorem coverAt_zoom_top {n : ℕ} {c : Space} {lam δ η t₀ : ℝ} {x v : Fin n → Space}
    {Q : Finset (Fin n)} (hlam : 1 ≤ lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η)
    (hlδ : lam * δ ≤ 1 / 4)
    (hv : ∀ i, ‖v i‖ = 1)
    (hglob : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ({i | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W)
    (ht₀ : 0 < t₀) (hQ : Q ⊆ zoomThrough c lam x v) (hQne : Q.Nonempty)
    (hret : t₀ * (n : ℝ) ≤ (Q.card : ℝ)) :
    CoverAt (lam * δ) (8000 * δ ^ (-η) / t₀) 1 (zx c lam x v Q) (zv v Q)
      (fun _ : Fin 1 => -(1 / 2 : ℝ) • zv v Q ⟨0, card_pos.mpr hQne⟩)
      (fun _ : Fin 1 => zv v Q ⟨0, card_pos.mpr hQne⟩) := by
  classical
  have hlam0 : 0 < lam := by linarith
  set u := zv v Q ⟨0, card_pos.mpr hQne⟩ with hu
  have hu1 : ‖u‖ = 1 := hv _
  have hin : ∀ a : Fin Q.card, tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
      tube 1 (-(1 / 2 : ℝ) • u) u := by
    intro a
    refine (piece_subset_ball hlam0 (hv _)
      (foot_close_of_mem_through hv (hQ (enumerate_mem Q a)))
      (by rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith) hlδ).trans ?_
    exact ball_subset_tube_one hu1
  have hall : {a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
      tube 1 (-(1 / 2 : ℝ) • u) u} = univ := by
    ext a; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact hin a
  have hcard : ({a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
      tube 1 (-(1 / 2 : ℝ) • u) u}.ncard : ℝ) = Q.card := by
    rw [hall, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hnpos : (0 : ℝ) < n := by
    have : 0 < Q.card := card_pos.mpr hQne
    have h2 : Q.card ≤ n := by
      calc Q.card ≤ (univ : Finset (Fin n)).card := Finset.card_le_card (subset_univ Q)
        _ = n := by simp
    exact_mod_cast (lt_of_lt_of_le this h2)
  have hK1 : 1 ≤ 8000 * δ ^ (-η) / t₀ := by
    have hδη : 0 < δ ^ (-η) := Real.rpow_pos_of_pos hδ _
    have hQn : (Q.card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_le_card (subset_univ Q)).trans (by simp)
    have ht1 : t₀ ≤ 1 := by
      have := hret.trans hQn
      nlinarith
    have hδη1 : 1 ≤ δ ^ (-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    rw [le_div_iff₀ ht₀]
    nlinarith
  refine ⟨fun _ => hu1, fun j j' h => absurd (Subsingleton.elim j j') h, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨0, hin a, fun j _ => Subsingleton.elim j 0⟩
  · intro j
    exact ⟨⟨0, card_pos.mpr hQne⟩, hin _⟩
  · intro j j'
    show ({a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube 1 (-(1 / 2 : ℝ) • u) u}.ncard : ℝ) ≤ 8000 * δ ^ (-η) / t₀ *
      ({a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube 1 (-(1 / 2 : ℝ) • u) u}.ncard : ℝ)
    rw [hcard]
    nlinarith [Nat.cast_nonneg (α := ℝ) Q.card]
  · intro j W hW
    show ENNReal.ofReal (({a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube 1 (-(1 / 2 : ℝ) • u) u ∧ tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆ W}.ncard : ℝ) *
        1 ^ 2) ≤ ENNReal.ofReal (8000 * δ ^ (-η) / t₀ *
      ({a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube 1 (-(1 / 2 : ℝ) • u) u}.ncard : ℝ)) * volume W
    rw [hcard, one_pow, mul_one]
    have hset : {a : Fin Q.card | tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆
        tube 1 (-(1 / 2 : ℝ) • u) u ∧ tube (lam * δ) (zx c lam x v Q a) (zv v Q a) ⊆ W} =
        {a | (fun i => tube (lam * δ) (pieceStart c lam (x i) (v i)) (v i) ⊆ W)
          (enumerate Q a)} := by
      ext a
      simp only [mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨hin a, h⟩⟩
    have hcnt := enumerate_count Q (fun i => tube (lam * δ) (pieceStart c lam (x i) (v i)) (v i) ⊆ W)
    rw [hset, hcnt]
    set A := Q.filter (fun i => tube (lam * δ) (pieceStart c lam (x i) (v i)) (v i) ⊆ W) with hA
    rcases A.eq_empty_or_nonempty with hAe | ⟨i₀, hi₀⟩
    · rw [hAe, Finset.card_empty, Nat.cast_zero, ENNReal.ofReal_zero]
      exact zero_le
    obtain ⟨hi₀Q, hi₀W⟩ := by simpa [hA] using hi₀
    set U' := interior W with hU'
    have hU'o : IsOpen U' := isOpen_interior
    have hU'c : Convex ℝ U' := hW.interior
    set U := zoom c lam ⁻¹' U' with hUdef
    obtain ⟨hUo, hUc⟩ := zoom_preimage_isOpen_convex (c := c) (lam := lam) hU'o hU'c
    have hsubU : ∀ i ∈ A, subTube c lam δ (x i) (v i) ⊆ U := by
      intro i hi p hp
      obtain ⟨-, hiW⟩ := by simpa [hA] using hi
      exact interior_maximal hiW isOpen_thickening (zoom_mem_piece hlam0 hp)
    have hp₀ : foot c (x i₀) (v i₀) ∈ U := hsubU i₀ hi₀ (foot_mem_subTube hlam0 hδ _ _)
    set κ := 2 + (1 + 2) * lam with hκ
    have hκ0 : 0 ≤ κ := by positivity
    set E := enlarge (foot c (x i₀) (v i₀)) κ U with hE
    have hEc : Convex ℝ E := convex_enlarge hUc _ _
    have hsubE : (A : Set (Fin n)) ⊆ {i | tube δ (x i) (v i) ⊆ E} := by
      intro i hi
      have hi' : i ∈ A := hi
      obtain ⟨hiQ, -⟩ := by simpa [hA] using hi'
      show tube δ (x i) (v i) ⊆ E
      have hpar := param_mem_of_mem_through hv (hQ hiQ)
      have hK : |inner ℝ (c - x i) (v i)| ≤ 2 := by
        rw [abs_le]
        have : 1 / (4 * lam) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        constructor <;> linarith [hpar.1, hpar.2]
      exact tube_subset_enlarge hlam0 hδ hUc (hsubU i hi') hp₀ hK
    have hcardA : (A.card : ℝ) ≤ ({i | tube δ (x i) (v i) ⊆ E}.ncard : ℝ) := by
      rw [← Set.ncard_coe_finset]
      exact_mod_cast Set.ncard_le_ncard hsubE
    have hfr := hglob E hEc
    have hvolE := volume_enlarge_le hUo hUc (foot c (x i₀) (v i₀)) hκ0
    have hvolU : ENNReal.ofReal (lam ^ 3) * volume U ≤ volume W :=
      (volume_zoom_preimage hlam0 U').le.trans (measure_mono interior_subset)
    have hlam3 : ENNReal.ofReal (lam ^ 3) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    rw [← ENNReal.mul_le_mul_iff_right hlam3 ENNReal.ofReal_ne_top]
    have hκb : κ ≤ 5 * lam := by rw [hκ]; linarith
    have hδη : 0 < δ ^ (-η) := Real.rpow_pos_of_pos hδ _
    calc ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal (A.card : ℝ)
        ≤ ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal ({i | tube δ (x i) (v i) ⊆ E}.ncard : ℝ) := by
          gcongr
      _ ≤ ENNReal.ofReal (lam ^ 3) * (ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume E) := by
          gcongr
      _ = ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * (ENNReal.ofReal (lam ^ 3) * volume E) := by ring
      _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) *
            (ENNReal.ofReal (lam ^ 3) * (ENNReal.ofReal (κ ^ 3) * (64 * volume U))) := by gcongr
      _ = ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * (ENNReal.ofReal (κ ^ 3) * 64) *
            (ENNReal.ofReal (lam ^ 3) * volume U) := by ring
      _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * (ENNReal.ofReal (κ ^ 3) * 64) * volume W := by
          gcongr
      _ = ENNReal.ofReal (δ ^ (-η) * (n : ℝ) * (κ ^ 3 * 64)) * volume W := by
          rw [ENNReal.ofReal_mul (p := δ ^ (-η) * (n : ℝ)) (by positivity),
            ENNReal.ofReal_mul (p := κ ^ 3) (by positivity), ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (lam ^ 3 * (8000 * δ ^ (-η) / t₀ * (Q.card : ℝ))) * volume W := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          have hκ3 : κ ^ 3 ≤ (5 * lam) ^ 3 := by gcongr
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          calc δ ^ (-η) * (n : ℝ) * (κ ^ 3 * 64) ≤ δ ^ (-η) * (n : ℝ) * ((5 * lam) ^ 3 * 64) := by
                gcongr
            _ = lam ^ 3 * (8000 * δ ^ (-η) / t₀ * (t₀ * n)) := by field_simp; ring
            _ ≤ lam ^ 3 * (8000 * δ ^ (-η) / t₀ * (Q.card : ℝ)) := by gcongr
      _ = ENNReal.ofReal (lam ^ 3) * (ENNReal.ofReal (8000 * δ ^ (-η) / t₀ * (Q.card : ℝ)) *
            volume W) := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
