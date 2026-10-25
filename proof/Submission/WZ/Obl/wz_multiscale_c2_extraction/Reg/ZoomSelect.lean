-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.ZoomSelect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ZoomFrost

/-!
# Selection of the zoomed family and its covers at one scale

`select_in` chooses, inside a prescribed candidate set, a common colour pattern and prunes the
fibres so that every occupied fibre keeps a fixed fraction of its full original size.
`zoom_cover` turns an old balanced Frostman cover into a separated balanced Frostman cover of
the selected zoomed pieces.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory Finset
open scoped ENNReal RealInnerProductSpace Classical

noncomputable section

/-- Select a common colour pattern inside `P₀`, then prune all fibres simultaneously,
measuring retention against the full original fibres. -/
theorem select_in {I L : Type*} [Fintype I] [Fintype L]
    (J : L → Type*) [∀ l, Fintype (J l)] [∀ l, DecidableEq (J l)]
    (f : ∀ l, I → J l) {K : ℕ} (hK : 0 < K) (col : ∀ l, J l → Fin K)
    (w : I → ℝ) {M t : ℝ} (hM : 0 < M) (ht : 0 < t) (hw : ∀ i, w i ≤ M) (P₀ : Finset I) :
    ∃ Q : Finset I, Q ⊆ P₀ ∧
      (∀ l j, (Q.filter (fun i => f l i = j)).Nonempty →
        t * ((univ.filter (fun i => f l i = j)).card : ℝ) ≤
          ((Q.filter (fun i => f l i = j)).card : ℝ)) ∧
      (∀ l, ∀ i ∈ Q, ∀ i' ∈ Q, col l (f l i) = col l (f l i')) ∧
      (∑ i ∈ P₀, w i) / (K : ℝ) ^ Fintype.card L -
        M * t * ((Fintype.card L : ℝ) * Fintype.card I) ≤ ∑ i ∈ Q, w i := by
  let : NeZero K := ⟨Nat.ne_of_gt hK⟩
  let color : I → (L → Fin K) := fun i l => col l (f l i)
  let mass : (L → Fin K) → ℝ := fun a => ∑ i ∈ P₀.filter (fun i => color i = a), w i
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image univ mass univ_nonempty
  have hsum : ∑ b, mass b = ∑ i ∈ P₀, w i :=
    sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
  have hcard : (Fintype.card (L → Fin K) : ℝ) = (K : ℝ) ^ Fintype.card L := by simp
  have hP : (∑ i ∈ P₀, w i) / (K : ℝ) ^ Fintype.card L ≤ mass a := by
    rw [div_le_iff₀ (by positivity), ← hsum, ← hcard, mul_comm]
    calc ∑ b, mass b ≤ ∑ _b : L → Fin K, mass a := sum_le_sum fun b hb => hmax b hb
      _ = (Fintype.card (L → Fin K) : ℝ) * mass a := by simp
  let P := P₀.filter (fun i => color i = a)
  let F : (Σ l, J l) → Finset I := fun j => univ.filter (fun i => f j.1 i = j.2)
  obtain ⟨Q, hQP, hQfib, hmass⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.prune_fibres P F w hM ht hw
  have hfib : ∀ l, ∑ j : J l, ((univ.filter (fun i => f l i = j)).card : ℝ) =
      Fintype.card I := by
    intro l
    have h := sum_card_fiberwise_eq_card_filter (univ : Finset I) (univ : Finset (J l)) (f l)
    exact_mod_cast (by simpa using h : (∑ j, (univ.filter (fun i => f l i = j)).card) =
      Fintype.card I)
  have hsumF : ∑ j, ((F j).card : ℝ) = (Fintype.card L : ℝ) * Fintype.card I := by
    rw [Fintype.sum_sigma]
    dsimp [F]
    simp_rw [hfib]
    simp
  have he : ∀ l j, Q ∩ F ⟨l, j⟩ = Q.filter (fun i => f l i = j) := by
    intro l j
    ext i
    simp [F]
  refine ⟨Q, hQP.trans (filter_subset _ _), ?_, ?_, ?_⟩
  · intro l j hj
    have h := hQfib ⟨l, j⟩ (by rwa [he])
    simpa only [he] using h
  · intro l i hi i' hi'
    have hi := (mem_filter.mp (hQP hi)).2
    have hi' := (mem_filter.mp (hQP hi')).2
    exact congrFun (hi.trans hi'.symm) l
  · rw [hsumF] at hmass
    linarith

abbrev SeparatedAt := @WangZahlLot.Obl.wz_separated_cover_refinement.SeparatedAt
abbrev enumerate := @WangZahlLot.Obl.wz_separated_cover_refinement.enumerate

theorem tube_subset_dilate {ρ : ℝ} (hρ : 0 ≤ ρ) (z w : Space) : Tube ρ z w ⊆ Dilate ρ z w := by
  have hseg : segment ℝ z (z + w) ⊆
      segment ℝ (z - (9 / 2 : ℝ) • w) (z + (11 / 2 : ℝ) • w) := by
    intro p hp
    rw [segment_eq_image'] at hp ⊢
    obtain ⟨θ, hθ, rfl⟩ := hp
    refine ⟨(θ + 9 / 2) / 10, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ?_⟩
    simp only
    module
  exact (thickening_subset_of_subset ρ hseg).trans (thickening_mono (by linarith) _)

/-- A coarse tube containing a near fine tube is near. -/
theorem cnear_of_fnear {r δ ρ : ℝ} (hr : 16 ≤ r) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hρr : ρ ≤ 1 / (131072 * r)) {c x v z w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hT : Tube δ x v ⊆ Tube ρ z w) (hn : FNear r c x v) : CNear r c z w := by
  have hr0 : 0 < r := by linarith
  have hR : 1 / (8 * r) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨h1, h2⟩ := coarse_near hδ hδρ hR hv hw hT hn.1 hn.2
  have hρ' : 5 * ρ ≤ 1 / (8 * r) := by
    have := mul_le_mul_of_nonneg_left hρr (show (0 : ℝ) ≤ 5 by norm_num)
    calc 5 * ρ ≤ 5 * (1 / (131072 * r)) := this
      _ ≤ 1 / (8 * r) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h8 : 1 / (8 * r) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨?_, ?_, ?_⟩
  · calc ‖cpt c z w - c‖ ≤ ‖cpt c z w - cpt c x v‖ + ‖cpt c x v - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 5 * ρ + 1 / (8 * r) := by rw [norm_sub_rev]; linarith [hn.1]
      _ ≤ 1 / (4 * r) := by
        have : 1 / (4 * r) = 2 * (1 / (8 * r)) := by field_simp; ring
        linarith
  · linarith [h2.1]
  · linarith [h2.2]

/-- An old balanced Frostman cover yields a separated balanced Frostman cover of the selected
zoomed pieces. -/
theorem zoom_cover {n k K₀ : ℕ} {r δ ρ K t K' : ℝ} {c : Space}
    (hr : 16 ≤ r) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρr : ρ ≤ 1 / (131072 * r))
    (hrδ : r * δ ≤ 1 / 8) (ht : 0 < t) (hK : 0 < K)
    (hK'1 : K ≤ K' * t) (hK'2 : 64 * (432 * 512) * r ^ 2 * K ≤ K' * t)
    {x v : Fin n → Space} {z w : Fin k → Space} (hv : ∀ i, ‖v i‖ = 1)
    (hcov : CoverAt δ K ρ x v z w)
    (f : Fin n → Fin k) (hf : ∀ i j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) ↔ f i = j)
    (I₀ : Finset (Fin n)) (hI₀ : ∀ i ∈ I₀, FNear r c (x i) (v i))
    (Q : Finset (Fin n)) (hQI : Q ⊆ I₀) (hQ : Q.Nonempty)
    (hret : ∀ j, (Q.filter (fun i => f i = j)).Nonempty →
      t * ((univ.filter (fun i => f i = j)).card : ℝ) ≤ ((Q.filter (fun i => f i = j)).card : ℝ))
    (col : Fin k → Fin K₀)
    (hcol : ∀ j j', j ≠ j' → CConf r δ ρ c I₀ x v z w j j' → col j ≠ col j')
    (hsame : ∀ i ∈ Q, ∀ i' ∈ Q, col (f i) = col (f i')) :
    ∃ k' : ℕ, 0 < k' ∧ ∃ z' w' : Fin k' → Space,
      CoverAt (r * δ) K' (8 * r * ρ)
        (fun a => pieceBase r c (x (enumerate Q a)) (v (enumerate Q a)))
        (fun a => v (enumerate Q a)) z' w' ∧
      SeparatedAt (r * δ) (8 * r * ρ)
        (fun a => pieceBase r c (x (enumerate Q a)) (v (enumerate Q a)))
        (fun a => v (enumerate Q a)) z' w' := by
  obtain ⟨hw, hsep, huniq, hfull, hbal, hfrost⟩ := hcov
  have hr0 : 0 < r := by linarith
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hK' : 0 < K' := by
    by_contra hneg
    have : K' * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) ht.le
    linarith
  have hR : 1 / (8 * r) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- containment of pieces
  have hF1 : ∀ i ∈ I₀, fpiece r δ c (x i) (v i) ⊆ cpiece r ρ c (z (f i)) (w (f i)) := by
    intro i hi
    exact piece_subset_piece (by linarith) hδ hδρ hR (hv i) (hw (f i)) ((hf i (f i)).mpr rfl)
      (hI₀ i hi).1 (hI₀ i hi).2
  have hF2 : ∀ i ∈ I₀, CNear r c (z (f i)) (w (f i)) := fun i hi =>
    cnear_of_fnear hr hδ hδρ hρr (hv i) (hw (f i)) ((hf i (f i)).mpr rfl) (hI₀ i hi)
  -- kept coarse tubes
  set G := Q.image f
  set b := enumerate G
  have hbmem : ∀ j, b j ∈ G := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_mem G
  have hbinj : Function.Injective b :=
    WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_injective G
  have hG : 0 < G.card := Finset.card_pos.mpr (hQ.image f)
  have hkept : ∀ j, ∃ i ∈ Q, f i = b j := by
    intro j
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (hbmem j)
    exact ⟨i, hi, he⟩
  have hcolkept : ∀ j j', col (b j) = col (b j') := by
    intro j j'
    obtain ⟨i, hi, hij⟩ := hkept j
    obtain ⟨i', hi', hij'⟩ := hkept j'
    rw [← hij, ← hij']
    exact hsame i hi i' hi'
  have hnoconf : ∀ j j', j ≠ j' → ¬ CConf r δ ρ c I₀ x v z w (b j) (b j') := by
    intro j j' hjj' hconf
    exact hcol _ _ (hbinj.ne hjj') hconf (hcolkept j j')
  have hnear : ∀ j, CNear r c (z (b j)) (w (b j)) := by
    intro j
    obtain ⟨i, hi, hij⟩ := hkept j
    rw [← hij]; exact hF2 i (hQI hi)
  set e := enumerate Q
  have hemem : ∀ a, e a ∈ Q := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_mem Q
  have hparent : ∀ a, ∃ j, f (e a) = b j := by
    intro a
    obtain ⟨j, hj⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_surjective G
      (Finset.mem_image.mpr ⟨e a, hemem a, rfl⟩)
    exact ⟨j, hj.symm⟩
  -- the new containment relation
  have hfnew : ∀ a j, Tube (r * δ) (pieceBase r c (x (e a)) (v (e a))) (v (e a)) ⊆
      Tube (8 * r * ρ) (pieceBase r c (z (b j)) (w (b j))) (w (b j)) ↔ f (e a) = b j := by
    intro a j
    constructor
    · intro hsub
      obtain ⟨j₀, hj₀⟩ := hparent a
      by_contra hne
      have hjj : j₀ ≠ j := by
        intro h; exact hne (by rw [hj₀, h])
      apply hnoconf j₀ j hjj
      refine ⟨hnear j₀, hnear j, Or.inl ⟨e a, hQI (hemem a), ?_, ?_⟩⟩
      · have h1 := hF1 (e a) (hQI (hemem a))
        rw [hj₀] at h1
        exact h1.trans (tube_subset_dilate (by positivity) _ _)
      · exact hsub.trans (tube_subset_dilate (by positivity) _ _)
    · intro hje
      have h1 := hF1 (e a) (hQI (hemem a))
      rw [hje] at h1
      exact h1
  have hncount : ∀ (P : Fin n → Prop), ncard {a | P (e a)} = (Q.filter P).card :=
    fun P => WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_count Q P
  have horig : ∀ j, ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z (b j)) (w (b j))} =
      (univ.filter (fun i => f i = b j)).card := by
    intro j
    simp_rw [hf]
    exact WangZahlLot.Obl.wz_separated_cover_refinement.ncard_setOf (fun i : Fin n => f i = b j)
  have hnew : ∀ j, ncard {a | Tube (r * δ) (pieceBase r c (x (e a)) (v (e a))) (v (e a)) ⊆
      Tube (8 * r * ρ) (pieceBase r c (z (b j)) (w (b j))) (w (b j))} =
      (Q.filter (fun i => f i = b j)).card := by
    intro j
    simp_rw [hfnew]
    convert hncount (fun i => f i = b j)
  have hoccupied : ∀ j, (Q.filter (fun i => f i = b j)).Nonempty := by
    intro j
    obtain ⟨i, hi, hij⟩ := hkept j
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩⟩
  have hretj : ∀ j, K * ((univ.filter (fun i => f i = b j)).card : ℝ) ≤
      K' * ((Q.filter (fun i => f i = b j)).card : ℝ) := by
    intro j
    calc K * ((univ.filter (fun i => f i = b j)).card : ℝ)
        ≤ (K' * t) * ((univ.filter (fun i => f i = b j)).card : ℝ) := by gcongr
      _ = K' * (t * ((univ.filter (fun i => f i = b j)).card : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hret _ (hoccupied j)) hK'.le
  refine ⟨G.card, hG, (fun j => pieceBase r c (z (b j)) (w (b j))), (fun j => w (b j)),
    ⟨fun j => hw (b j), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j j' hjj'
    by_contra h
    exact hnoconf j j' hjj' ⟨hnear j, hnear j', Or.inr (Or.inl (lt_of_not_ge h))⟩
  · intro a
    obtain ⟨j, hj⟩ := hparent a
    exact ⟨j, (hfnew a j).mpr hj, fun j' hj' => hbinj (((hfnew a j').mp hj').symm.trans hj)⟩
  · intro j
    obtain ⟨i, hi, hij⟩ := hkept j
    obtain ⟨a, rfl⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_surjective Q hi
    exact ⟨a, (hfnew a j).mpr hij⟩
  · intro j j'
    rw [hnew, hnew]
    have h1 : ((Q.filter (fun i => f i = b j)).card : ℝ) ≤
        ((univ.filter (fun i => f i = b j)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ Q))
    have h2 := hbal (b j) (b j')
    rw [horig, horig] at h2
    linarith [hretj j']
  · intro j W hW
    rw [hnew]
    set S := {a | Tube (r * δ) (pieceBase r c (x (e a)) (v (e a))) (v (e a)) ⊆
      Tube (8 * r * ρ) (pieceBase r c (z (b j)) (w (b j))) (w (b j)) ∧
        Tube (r * δ) (pieceBase r c (x (e a)) (v (e a))) (v (e a)) ⊆ W}
    rcases S.eq_empty_or_nonempty with hS | ⟨a₀, ha₀⟩
    · rw [hS, ncard_empty, Nat.cast_zero, zero_mul, ENNReal.ofReal_zero]
      exact bot_le
    by_cases hWtop : volume W = ⊤
    · have hne : ENNReal.ofReal (K' * ((Q.filter (fun i => f i = b j)).card : ℝ)) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        have : (0 : ℝ) < (Q.filter (fun i => f i = b j)).card := by
          exact_mod_cast Finset.card_pos.mpr (hoccupied j)
        positivity
      rw [hWtop, ENNReal.mul_top hne]
      exact le_top
    obtain ⟨B, hBconv, hBvol, hBsub⟩ := old_tubes_in_box hr hδ hrδ hW hWtop (hv (e a₀))
      (hI₀ _ (hQI (hemem a₀))) ha₀.2
    set O := {i | Tube δ (x i) (v i) ⊆ Tube ρ (z (b j)) (w (b j)) ∧ Tube δ (x i) (v i) ⊆ B}
    have hSO : ncard S ≤ ncard O := by
      apply Set.ncard_le_ncard_of_injOn e
      · intro a ha
        have hfa : f (e a) = b j := (hfnew a j).mp ha.1
        exact ⟨(hf _ _).mpr hfa, hBsub _ _ (hv _) (hI₀ _ (hQI (hemem a))) ha.2⟩
      · intro a _ a' _ h
        exact WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_injective Q h
    have hold := hfrost (b j) B hBconv
    rw [horig] at hold
    have hS' : ((ncard S : ℕ) : ℝ) ≤ ((ncard O : ℕ) : ℝ) := by exact_mod_cast hSO
    calc ENNReal.ofReal ((ncard S : ℝ) * (8 * r * ρ) ^ 2)
        ≤ ENNReal.ofReal (64 * r ^ 2) * ENNReal.ofReal ((ncard O : ℝ) * ρ ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [sq_nonneg (r * ρ)]
      _ ≤ ENNReal.ofReal (64 * r ^ 2) * (ENNReal.ofReal
            (K * ((univ.filter (fun i => f i = b j)).card : ℝ)) * volume B) := by gcongr
      _ ≤ ENNReal.ofReal (64 * r ^ 2) * (ENNReal.ofReal
            (K * ((univ.filter (fun i => f i = b j)).card : ℝ)) *
              (ENNReal.ofReal (432 * 512) * volume W)) := by gcongr
      _ = ENNReal.ofReal (64 * (432 * 512) * r ^ 2 * K *
            ((univ.filter (fun i => f i = b j)).card : ℝ)) * volume W := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
      _ ≤ ENNReal.ofReal (K' * ((Q.filter (fun i => f i = b j)).card : ℝ)) * volume W := by
          gcongr ENNReal.ofReal ?_ * _
          calc 64 * (432 * 512) * r ^ 2 * K * ((univ.filter (fun i => f i = b j)).card : ℝ)
              ≤ (K' * t) * ((univ.filter (fun i => f i = b j)).card : ℝ) := by gcongr
            _ = K' * (t * ((univ.filter (fun i => f i = b j)).card : ℝ)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (hret _ (hoccupied j)) hK'.le
  · intro a j j' h1 h2
    by_contra hne
    exact hnoconf j j' hne ⟨hnear j, hnear j', Or.inl ⟨e a, hQI (hemem a), h1, h2⟩⟩

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
