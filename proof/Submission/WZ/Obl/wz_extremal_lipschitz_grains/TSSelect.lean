-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TSSelect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_cover_refinement.Covers
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic

set_option autoImplicit false

/-!
# Selection of exact separated covers from approximate data

A finite family of elements (tubes) comes with candidate covers at finitely many
levels. Exactness may fail: candidate covers may overlap by more than half, an
element may lie in several candidate covers, and elements may overlap. Each
failure is recorded by a symmetric conflict relation of bounded degree. A common
colour pattern followed by simultaneous pruning (o060's `select_regular`)
retains a fixed fraction of any bounded weight and yields, at every level, an
exact balanced, locally Frostman and separated cover of the retained elements.
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory Finset
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_separated_cover_refinement
  (Tube Dilate CoverAt SeparatedAt enumerate enumerate_mem enumerate_injective
    enumerate_surjective enumerate_count enumerate_sum ncard_setOf color_relation
    select_regular)

/-- A tube lies in its tenfold concentric dilation. -/
theorem tube_subset_dilate (r : ℝ) (z w : Space) : Tube r z w ⊆ Dilate r z w := by
  rcases lt_or_ge r 0 with hr | hr
  · intro p hp
    simp [Tube, thickening_of_nonpos hr.le] at hp
  have hseg : segment ℝ z (z + w) ⊆
      segment ℝ (z - (9 / 2 : ℝ) • w) (z + (11 / 2 : ℝ) • w) := by
    apply (convex_segment _ _).segment_subset
    · refine ⟨11 / 20, 9 / 20, by norm_num, by norm_num, by norm_num, ?_⟩
      module
    · refine ⟨9 / 20, 11 / 20, by norm_num, by norm_num, by norm_num, ?_⟩
      module
  exact (thickening_mono (by linarith) _).trans (thickening_subset_of_subset _ hseg)

/-- Exact covers at every level, selected from approximate covers. -/
theorem select_frozen {n B : ℕ} {Λ : Type} [Fintype Λ] (hB : 0 < B) {s M t K : ℝ}
    (x v : Fin n → Space)
    (ρ : Λ → ℝ) (k : Λ → ℕ) (z w : (l : Λ) → Fin (k l) → Space)
    (f : (l : Λ) → Fin n → Fin (k l))
    (hf : ∀ l i, Tube s (x i) (v i) ⊆ Tube (ρ l) (z l (f l i)) (w l (f l i)))
    (cE : Fin n → Fin n → Prop) (hcE : ∀ {i j}, cE i j → cE j i)
    (hcEdeg : ∀ i, (univ.filter (cE i)).card < B)
    (cC : (l : Λ) → Fin (k l) → Fin (k l) → Prop)
    (hcC : ∀ l {m m'}, cC l m m' → cC l m' m)
    (hcCdeg : ∀ l m, (univ.filter (cC l m)).card < B)
    (hunit : ∀ l m, ‖w l m‖ = 1)
    (hC : ∀ l m m', (∃ i, f l i = m) → (∃ i, f l i = m') → m ≠ m' → ¬cC l m m' →
      volume (Tube (ρ l) (z l m) (w l m) ∩ Tube (ρ l) (z l m') (w l m')) ≤
        (1 / 2 : ℝ≥0∞) * volume (Tube (ρ l) (z l m) (w l m)))
    (hsep : ∀ l i m m', (∃ i, f l i = m) → (∃ i, f l i = m') →
      Tube s (x i) (v i) ⊆ Dilate (ρ l) (z l m) (w l m) →
      Tube s (x i) (v i) ⊆ Dilate (ρ l) (z l m') (w l m') → m = m' ∨ cC l m m')
    (hbal : ∀ l i i', ((univ.filter (fun a => f l a = f l i)).card : ℝ) ≤
      K * (univ.filter (fun a => f l a = f l i')).card)
    (hfrost : ∀ l i (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (((univ.filter (fun a => f l a = f l i ∧
          Tube s (x a) (v a) ⊆ W)).card : ℝ) * ρ l ^ 2) ≤
        ENNReal.ofReal (K * (univ.filter (fun a => f l a = f l i)).card) * volume W)
    (ω : Fin n → ℝ) (hωM : ∀ i, ω i ≤ M) (hM : 0 < M) (ht : 0 < t) :
    ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → ¬cE i j) ∧
      (Q.Nonempty → ∀ l, ∃ k' : ℕ, 0 < k' ∧ ∃ z' w' : Fin k' → Space,
        CoverAt s (K / t) (ρ l) (fun i => x (enumerate Q i))
          (fun i => v (enumerate Q i)) z' w' ∧
        SeparatedAt s (ρ l) (fun i => x (enumerate Q i))
          (fun i => v (enumerate Q i)) z' w') ∧
      (∑ i, ω i) / (B : ℝ) ^ (Fintype.card Λ + 1) -
        M * t * (((Fintype.card Λ + 1 : ℕ) : ℝ) * n) ≤ ∑ i ∈ Q, ω i := by
  classical
  -- colourings
  have hcolE := color_relation hB cE hcE hcEdeg
  obtain ⟨cEc, hcEc⟩ := hcolE
  have hcolC : ∀ l, ∃ c : Fin (k l) → Fin B, ∀ m m', m ≠ m' → cC l m m' → c m ≠ c m' :=
    fun l => color_relation hB (cC l) (hcC l) (hcCdeg l)
  choose cCc hcCc using hcolC
  -- levels indexed by `Option Λ`: `none` is the element level
  let J : Option Λ → Type := fun o => match o with
    | none => Fin n
    | some l => Fin (k l)
  let _ : ∀ o, Fintype (J o) := fun o => match o with
    | none => inferInstanceAs (Fintype (Fin n))
    | some l => inferInstanceAs (Fintype (Fin (k l)))
  let _ : ∀ o, DecidableEq (J o) := fun o => match o with
    | none => inferInstanceAs (DecidableEq (Fin n))
    | some l => inferInstanceAs (DecidableEq (Fin (k l)))
  let F : ∀ o, Fin n → J o := fun o => match o with
    | none => fun i => i
    | some l => f l
  let c : ∀ o, J o → Fin B := fun o => match o with
    | none => cEc
    | some l => cCc l
  obtain ⟨Q, hQfib, hQcol, hQmass⟩ := select_regular J F hB c ω hM ht hωM
  have hcardL : Fintype.card (Option Λ) = Fintype.card Λ + 1 := by simp
  rw [hcardL] at hQmass
  simp only [Fintype.card_fin] at hQmass
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro i hi j hj hij hcij
    have h := hQcol none i hi j hj
    exact hcEc i j hij hcij h
  · intro hQne l
    -- retained covers at level `l`
    have hfib : ∀ m, (Q.filter (fun i => f l i = m)).Nonempty →
        t * ((univ.filter (fun i => f l i = m)).card : ℝ) ≤
          ((Q.filter (fun i => f l i = m)).card : ℝ) := fun m hm => hQfib (some l) m hm
    have hcol : ∀ i ∈ Q, ∀ i' ∈ Q, cCc l (f l i) = cCc l (f l i') :=
      fun i hi i' hi' => hQcol (some l) i hi i' hi'
    let G := Q.image (f l)
    let b := enumerate G
    have hbmem : ∀ j, b j ∈ G := enumerate_mem G
    have hbinj : Function.Injective b := enumerate_injective G
    have hG : 0 < G.card := Finset.card_pos.mpr (hQne.image _)
    have hocc : ∀ j, ∃ i ∈ Q, f l i = b j := by
      intro j
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (hbmem j)
      exact ⟨i, hi, he⟩
    -- retained covers do not conflict
    have hnc : ∀ j j', b j ≠ b j' → ¬cC l (b j) (b j') := by
      intro j j' hne hcj
      obtain ⟨i, hi, hie⟩ := hocc j
      obtain ⟨i', hi', hie'⟩ := hocc j'
      have h := hcol i hi i' hi'
      rw [hie, hie'] at h
      exact hcCc l _ _ hne hcj h
    -- membership in a retained cover is the assignment
    have hiff : ∀ i ∈ Q, ∀ j, Tube s (x i) (v i) ⊆ Tube (ρ l) (z l (b j)) (w l (b j)) ↔
        f l i = b j := by
      intro i hi j
      constructor
      · intro hsub
        obtain ⟨j0, hj0⟩ := enumerate_surjective G (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        change b j0 = f l i at hj0
        by_contra hne
        have hbj : ∃ i', f l i' = b j := by
          obtain ⟨i', -, hi'⟩ := hocc j; exact ⟨i', hi'⟩
        rcases hsep l i (b j) (f l i) hbj ⟨i, rfl⟩ (hsub.trans (tube_subset_dilate _ _ _))
          ((hf l i).trans (tube_subset_dilate _ _ _)) with h | h
        · exact hne h.symm
        · rw [← hj0] at h hne
          exact hnc j j0 (Ne.symm hne) h
      · intro he
        rw [← he]
        exact hf l i
    have hcount : ∀ j, ncard {a | Tube s (x (enumerate Q a)) (v (enumerate Q a)) ⊆
        Tube (ρ l) (z l (b j)) (w l (b j))} = (Q.filter (fun i => f l i = b j)).card := by
      intro j
      rw [← enumerate_count Q (fun i => f l i = b j)]
      congr 1
      ext a
      exact hiff _ (enumerate_mem Q a) j
    have hcountW : ∀ j (W : Set Space), ncard {a | Tube s (x (enumerate Q a)) (v (enumerate Q a)) ⊆
        Tube (ρ l) (z l (b j)) (w l (b j)) ∧ Tube s (x (enumerate Q a)) (v (enumerate Q a)) ⊆ W} =
        (Q.filter (fun i => f l i = b j ∧ Tube s (x i) (v i) ⊆ W)).card := by
      intro j W
      rw [← enumerate_count Q (fun i => f l i = b j ∧ Tube s (x i) (v i) ⊆ W)]
      congr 1
      ext a
      simp only [Set.mem_ofPred_eq]
      rw [hiff _ (enumerate_mem Q a) j]
    have hKt : ∀ j, K * ((univ.filter (fun i => f l i = b j)).card : ℝ) ≤
        K / t * ((Q.filter (fun i => f l i = b j)).card : ℝ) := by
      intro j
      obtain ⟨i, hi, hie⟩ := hocc j
      have hne : (Q.filter (fun a => f l a = b j)).Nonempty :=
        ⟨i, Finset.mem_filter.mpr ⟨hi, hie⟩⟩
      have h := hfib (b j) hne
      have hK : 0 ≤ K := by
        have := hbal l i i
        have hpos : (0 : ℝ) < ((univ.filter (fun a => f l a = f l i)).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr ⟨i, by simp⟩
        nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ ht]
      calc K * ((univ.filter (fun i => f l i = b j)).card : ℝ) * t
          = K * (t * ((univ.filter (fun i => f l i = b j)).card : ℝ)) := by ring
        _ ≤ K * ((Q.filter (fun i => f l i = b j)).card : ℝ) :=
          mul_le_mul_of_nonneg_left h hK
    refine ⟨G.card, hG, fun j => z l (b j), fun j => w l (b j), ?_, ?_⟩
    · refine ⟨fun j => hunit l (b j), ?_, ?_, ?_, ?_, ?_⟩
      · intro j j' hjj
        obtain ⟨i1, -, hi1⟩ := hocc j
        obtain ⟨i2, -, hi2⟩ := hocc j'
        exact hC l (b j) (b j') ⟨i1, hi1⟩ ⟨i2, hi2⟩ (hbinj.ne hjj) (hnc j j' (hbinj.ne hjj))
      · intro a
        obtain ⟨j0, hj0⟩ := enumerate_surjective G
          (Finset.mem_image.mpr ⟨enumerate Q a, enumerate_mem Q a, rfl⟩)
        change b j0 = f l (enumerate Q a) at hj0
        refine ⟨j0, (hiff _ (enumerate_mem Q a) j0).mpr hj0.symm, ?_⟩
        intro j' hj'
        have h := (hiff _ (enumerate_mem Q a) j').mp hj'
        exact hbinj (h.symm.trans hj0.symm)
      · intro j
        obtain ⟨i, hi, hie⟩ := hocc j
        obtain ⟨a, ha⟩ := enumerate_surjective Q hi
        refine ⟨a, ?_⟩
        change Tube s (x (enumerate Q a)) (v (enumerate Q a)) ⊆ _
        rw [ha]
        exact (hiff i hi j).mpr hie
      · intro j j'
        rw [hcount j, hcount j']
        obtain ⟨i, hi, hie⟩ := hocc j
        obtain ⟨i', hi', hie'⟩ := hocc j'
        have hb := hbal l i i'
        rw [hie, hie'] at hb
        calc ((Q.filter (fun i => f l i = b j)).card : ℝ)
            ≤ ((univ.filter (fun i => f l i = b j)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card
                (Finset.filter_subset_filter _ (Finset.subset_univ Q))
          _ ≤ K * ((univ.filter (fun i => f l i = b j')).card : ℝ) := hb
          _ ≤ K / t * ((Q.filter (fun i => f l i = b j')).card : ℝ) := hKt j'
      · intro j W hW
        rw [hcountW j W, hcount j]
        obtain ⟨i, hi, hie⟩ := hocc j
        have h := hfrost l i W hW
        simp_rw [hie] at h
        calc ENNReal.ofReal (((Q.filter (fun i => f l i = b j ∧
                Tube s (x i) (v i) ⊆ W)).card : ℝ) * ρ l ^ 2)
            ≤ ENNReal.ofReal (((univ.filter (fun i => f l i = b j ∧
                Tube s (x i) (v i) ⊆ W)).card : ℝ) * ρ l ^ 2) := by
              apply ENNReal.ofReal_le_ofReal
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              exact_mod_cast Finset.card_le_card
                (Finset.filter_subset_filter _ (Finset.subset_univ Q))
          _ ≤ ENNReal.ofReal (K * ((univ.filter (fun i => f l i = b j)).card : ℝ)) *
              volume W := h
          _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (hKt j)) le_rfl
    · intro a j j' hj hj'
      by_cases hbb : b j = b j'
      · exact hbinj hbb
      · obtain ⟨i1, -, hi1⟩ := hocc j
        obtain ⟨i2, -, hi2⟩ := hocc j'
        rcases hsep l (enumerate Q a) (b j) (b j') ⟨i1, hi1⟩ ⟨i2, hi2⟩ hj hj' with h | h
        · exact absurd h hbb
        · exact absurd h (hnc j j' hbb)
  · simpa using hQmass

/-- A system of candidate covers of `n` elements: tubes, assignment and conflicts. -/
structure CoverSys (n : ℕ) where
  k : ℕ
  ρ : ℝ
  z : Fin k → Space
  w : Fin k → Space
  f : Fin n → Fin k
  conf : Fin k → Fin k → Prop

/-- `select_frozen` for levels given as cover systems. -/
theorem select_frozen_sys {n B : ℕ} {Λ : Type} [Fintype Λ] (hB : 0 < B) {s M t K : ℝ}
    (x v : Fin n → Space) (L : Λ → CoverSys n)
    (hf : ∀ l i, Tube s (x i) (v i) ⊆ Tube (L l).ρ ((L l).z ((L l).f i)) ((L l).w ((L l).f i)))
    (cE : Fin n → Fin n → Prop) (hcE : ∀ {i j}, cE i j → cE j i)
    (hcEdeg : ∀ i, (univ.filter (cE i)).card < B)
    (hcC : ∀ l {m m'}, (L l).conf m m' → (L l).conf m' m)
    (hcCdeg : ∀ l m, (univ.filter ((L l).conf m)).card < B)
    (hunit : ∀ l m, ‖(L l).w m‖ = 1)
    (hC : ∀ l m m', (∃ i, (L l).f i = m) → (∃ i, (L l).f i = m') → m ≠ m' →
      ¬(L l).conf m m' →
      volume (Tube (L l).ρ ((L l).z m) ((L l).w m) ∩ Tube (L l).ρ ((L l).z m') ((L l).w m')) ≤
        (1 / 2 : ℝ≥0∞) * volume (Tube (L l).ρ ((L l).z m) ((L l).w m)))
    (hsep : ∀ l i m m', (∃ i, (L l).f i = m) → (∃ i, (L l).f i = m') →
      Tube s (x i) (v i) ⊆ Dilate (L l).ρ ((L l).z m) ((L l).w m) →
      Tube s (x i) (v i) ⊆ Dilate (L l).ρ ((L l).z m') ((L l).w m') → m = m' ∨ (L l).conf m m')
    (hbal : ∀ l i i', ((univ.filter (fun a => (L l).f a = (L l).f i)).card : ℝ) ≤
      K * (univ.filter (fun a => (L l).f a = (L l).f i')).card)
    (hfrost : ∀ l i (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (((univ.filter (fun a => (L l).f a = (L l).f i ∧
          Tube s (x a) (v a) ⊆ W)).card : ℝ) * (L l).ρ ^ 2) ≤
        ENNReal.ofReal (K * (univ.filter (fun a => (L l).f a = (L l).f i)).card) * volume W)
    (ω : Fin n → ℝ) (hωM : ∀ i, ω i ≤ M) (hM : 0 < M) (ht : 0 < t) :
    ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → ¬cE i j) ∧
      (Q.Nonempty → ∀ l, ∃ k' : ℕ, 0 < k' ∧ ∃ z' w' : Fin k' → Space,
        CoverAt s (K / t) (L l).ρ (fun i => x (enumerate Q i))
          (fun i => v (enumerate Q i)) z' w' ∧
        SeparatedAt s (L l).ρ (fun i => x (enumerate Q i))
          (fun i => v (enumerate Q i)) z' w') ∧
      (∑ i, ω i) / (B : ℝ) ^ (Fintype.card Λ + 1) -
        M * t * (((Fintype.card Λ + 1 : ℕ) : ℝ) * n) ≤ ∑ i ∈ Q, ω i :=
  select_frozen hB x v (fun l => (L l).ρ) (fun l => (L l).k) (fun l => (L l).z)
    (fun l => (L l).w) (fun l => (L l).f) hf cE hcE hcEdeg (fun l => (L l).conf) hcC hcCdeg
    hunit hC hsep hbal hfrost ω hωM hM ht

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
