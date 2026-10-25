-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.PacketLabels.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketPower
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_measurable_angular_selection (pd)

abbrev PacketLabel := (Fin 3 → ℤ) × (Fin 3 → ℤ)

/-- Assign every retained incidence the spatial/angular label of its packet.
Different packets may have the same label. -/
def packetPiece {n : ℕ} (θ : ℝ) (v : Fin n → Space) (Z : Fin n → Set Space)
    (P : Space → Finset (Finset (Fin n))) (a : Space → Finset (Fin n) → Fin n)
    (ℓ : PacketLabel) (i : Fin n) : Set Space :=
  {p | p ∈ Z i ∧ ∃ W ∈ P p, i ∈ W ∧
    wz_balanced_cluster_cover.lab θ (fun q => v (a q W)) p = ℓ}

/-- Every packet label determines a measurable piece of each fine shading. -/
theorem PacketRefinement.measurable_piece {n : ℕ} {β δ θ : ℝ} {v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (ℓ : PacketLabel) (i : Fin n) : MeasurableSet (packetPiece θ v Z P a ℓ i) := by
  classical
  have he : packetPiece θ v Z P a ℓ i = Z i ∩ ⋃ W : Finset (Fin n),
      ({p | W ∈ P p ∧ i ∈ W} ∩
        {p | wz_balanced_cluster_cover.lab θ (fun q => v (a q W)) p = ℓ}) := by
    ext p
    simp [packetPiece, and_assoc]
  rw [he]
  apply (h.1 i).1.inter
  apply MeasurableSet.iUnion
  intro W
  apply MeasurableSet.inter
  · by_cases hi : i ∈ W
    · simpa only [hi, and_true] using h.2.1 W
    · simp [hi]
  · exact wz_balanced_cluster_cover.measurableSet_lab θ v (fun p => a p W)
      (h.2.2.1 W) ℓ

/-- The pieces cover each retained shading exactly. -/
theorem PacketRefinement.piece_cover {n : ℕ} {β δ θ : ℝ} {v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (i : Fin n) : (⋃ ℓ, packetPiece θ v Z P a ℓ i) = Z i := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨ℓ, hp⟩ := Set.mem_iUnion.mp hp
    exact hp.1
  · intro hp
    have hi : i ∈ (P p).biUnion id := by
      change i ∈ ((P p).biUnion id : Set (Fin n))
      rw [(h.2.2.2 p).2.1]
      exact hp
    obtain ⟨W, hW, hiW⟩ := Finset.mem_biUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨_, hp, W, hW, hiW, rfl⟩

/-- An incidence lies in just one labelled piece. -/
theorem PacketRefinement.piece_disjoint {n : ℕ} {β δ θ : ℝ} {v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (i : Fin n) : Pairwise (fun ℓ ℓ' => Disjoint (packetPiece θ v Z P a ℓ i) (packetPiece θ v Z P a ℓ' i)) := by
  intro ℓ ℓ' hne
  apply Set.disjoint_left.mpr
  rintro p ⟨_, W, hW, hi, hl⟩ ⟨_, W', hW', hi', hl'⟩
  have hWW : W = W' := by
    by_contra hn
    exact Finset.disjoint_left.mp ((h.2.2.2 p).1 hW hW' hn) hi hi'
  subst W'
  exact hne (hl.symm.trans hl')

/-- The accepted finite label bound applies to every incidence, independently
of how many angular packets occur elsewhere in the shading. -/
theorem PacketRefinement.piece_label {n : ℕ} {β δ θ : ℝ} {x v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (hθ : 0 < θ) (hδθ : δ ≤ θ) (hv : ∀ i, ‖v i‖ = 1)
    (hZT : ∀ i, Z i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i)))
    {ℓ : PacketLabel} {i : Fin n} {p : Space} (hp : p ∈ packetPiece θ v Z P a ℓ i) :
    ℓ ∈ wz_balanced_cluster_cover.labelBox θ 2 (x i) (v i) := by
  obtain ⟨hpZ, W, hW, hi, hl⟩ := hp
  have hc := (h.2.2.2 p).2.2 W hW
  rw [← hl]
  exact wz_balanced_cluster_cover.lab_mem_labelBox hθ hδθ (hv (a p W))
    (hZT i hpZ) (hc.2.1 i hi)

/-- A label records a fixed unit direction, close to each fine direction in
that label. -/
theorem PacketRefinement.piece_direction {n : ℕ} {β δ θ : ℝ} {v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (hθ : 0 < θ) (hv : ∀ i, ‖v i‖ = 1)
    {ℓ : PacketLabel} {i : Fin n} {p : Space} (hp : p ∈ packetPiece θ v Z P a ℓ i) :
    ‖wz_balanced_cluster_cover.W θ ℓ.1‖ = 1 ∧
      pd (v i) (wz_balanced_cluster_cover.W θ ℓ.1) ≤ 4 * θ := by
  obtain ⟨_, W, hW, hi, hl⟩ := hp
  have hfirst : wz_balanced_cluster_cover.cell θ (v (a p W)) = ℓ.1 := congrArg Prod.fst hl
  have hh := wz_balanced_cluster_cover.dir_close hθ (hv (a p W))
    (((h.2.2.2 p).2.2 W hW).2.1 i hi)
  rw [hfirst] at hh
  simpa only [pd, show (2 : ℝ) + 2 = 4 by norm_num] using hh

/-- All occupied fine tubes at a fixed label lie in a length-six carrier of
radius `8θ`. This uses full tubes, not just their retained shadings. -/
theorem PacketRefinement.piece_carrier {n : ℕ} {β δ θ : ℝ} {x v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (hθ : 0 < θ) (hδθ : δ ≤ θ) (hv : ∀ i, ‖v i‖ = 1)
    (hZT : ∀ i, Z i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i)))
    (hball : ∀ i, Z i ⊆ Metric.ball (0 : Space) 1)
    (ℓ : PacketLabel) (hne : ∃ i, (packetPiece θ v Z P a ℓ i).Nonempty) :
    ∃ z w : Space, ‖w‖ = 1 ∧
      ∀ i, (packetPiece θ v Z P a ℓ i).Nonempty →
        Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening (8 * θ) (segment ℝ z (z + (6 : ℝ) • w)) := by
  classical
  obtain ⟨i₀, p₀, hp₀⟩ := hne
  let w := wz_balanced_cluster_cover.W θ ℓ.1
  have hw : ‖w‖ = 1 := (h.piece_direction hθ hv hp₀).1
  have hsecond (i : Fin n) (p : Space) (hp : p ∈ packetPiece θ v Z P a ℓ i) :
      wz_balanced_cluster_cover.cell θ (wz_balanced_cluster_cover.proj w p) = ℓ.2 := by
    obtain ⟨_, W, hW, hi, hl⟩ := hp
    have hfirst : wz_balanced_cluster_cover.cell θ (v (a p W)) = ℓ.1 := congrArg Prod.fst hl
    have hh := congrArg Prod.snd hl
    change wz_balanced_cluster_cover.cell θ
      (wz_balanced_cluster_cover.proj (wz_balanced_cluster_cover.W θ
        (wz_balanced_cluster_cover.cell θ (v (a p W)))) p) = ℓ.2 at hh
    simpa only [hfirst] using hh
  refine ⟨wz_balanced_cluster_cover.proj w p₀ - (3 : ℝ) • w, w, hw, ?_⟩
  intro i hi
  obtain ⟨p, hp⟩ := hi
  have hd := (h.piece_direction hθ hv hp).2
  have hpc : ‖p‖ < 1 := by simpa using hball i hp.1
  simpa only [show (2 : ℝ) + 6 = 8 by norm_num] using
    wz_balanced_cluster_cover.tube_subset_cyl (A := 2) hθ hδθ hw hpc
      (hZT i hp.1) (by simpa only [pd, w, show (2 : ℝ) + 2 = 4 by norm_num] using hd) ((hsecond i p hp).trans (hsecond i₀ p₀ hp₀).symm)


/-- A finite label set supporting every retained incidence. -/
noncomputable def packetLabelUniverse {n : ℕ} (θ : ℝ) (x v : Fin n → Space) : Finset PacketLabel :=
  Finset.univ.biUnion (fun i => wz_balanced_cluster_cover.labelBox θ 2 (x i) (v i))

/-- Labelled pieces preserve the full retained shading mass. -/
theorem PacketRefinement.piece_mass {n : ℕ} {β δ θ : ℝ} {x v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (hθ : 0 < θ) (hδθ : δ ≤ θ) (hv : ∀ i, ‖v i‖ = 1)
    (hZT : ∀ i, Z i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) :
    (∑ ℓ ∈ packetLabelUniverse θ x v, ∑ i, volume (packetPiece θ v Z P a ℓ i)) =
      ∑ i, volume (Z i) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have he : (⋃ ℓ ∈ packetLabelUniverse θ x v, packetPiece θ v Z P a ℓ i) = Z i := by
    rw [← h.piece_cover i]
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun ℓ _ => Set.subset_iUnion (fun ℓ => packetPiece θ v Z P a ℓ i) ℓ
    · intro p hp
      obtain ⟨ℓ, hp⟩ := Set.mem_iUnion.mp hp
      have hl := h.piece_label hθ hδθ hv hZT hp
      exact Set.mem_iUnion₂.mpr ⟨ℓ, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hl⟩, hp⟩
  rw [← he]
  symm
  exact measure_biUnion_finset (fun ℓ _ ℓ' _ hne => h.piece_disjoint i hne)
    (fun ℓ _ => h.measurable_piece ℓ i)

/-- Each original tube contributes to only a constant number of clusters. -/
theorem PacketRefinement.piece_card_sum {n : ℕ} {β δ θ : ℝ} {x v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (hθ : 0 < θ) (hδθ : δ ≤ θ) (hv : ∀ i, ‖v i‖ = 1)
    (hZT : ∀ i, Z i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) :
    (∑ ℓ ∈ packetLabelUniverse θ x v,
      ({i | (packetPiece θ v Z P a ℓ i).Nonempty}.ncard : ℝ)) ≤
        (2 * 6 ^ 3 * 22 ^ 3 : ℝ) * n := by
  classical
  let Λ := packetLabelUniverse θ x v
  let S : PacketLabel → Finset (Fin n) :=
    fun ℓ => Finset.univ.filter (fun i => (packetPiece θ v Z P a ℓ i).Nonempty)
  have he : ∑ ℓ ∈ Λ, (S ℓ).card =
      ∑ i : Fin n, (Λ.filter (fun ℓ => (packetPiece θ v Z P a ℓ i).Nonempty)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, S] using
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun ℓ i => (packetPiece θ v Z P a ℓ i).Nonempty)
        (s := Λ) (t := (Finset.univ : Finset (Fin n)))
  have hb (i : Fin n) :
      ((Λ.filter (fun ℓ => (packetPiece θ v Z P a ℓ i).Nonempty)).card : ℝ) ≤
        2 * 6 ^ 3 * 22 ^ 3 := by
    have hsub : Λ.filter (fun ℓ => (packetPiece θ v Z P a ℓ i).Nonempty) ⊆
        wz_balanced_cluster_cover.labelBox θ 2 (x i) (v i) := by
      intro ℓ hℓ
      obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hℓ).2
      exact h.piece_label hθ hδθ hv hZT hp
    have hh := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
    apply hh.trans
    convert wz_balanced_cluster_cover.card_labelBox_le hθ (by norm_num : (0 : ℝ) ≤ 2) (x i) (v i) using 1 <;> norm_num
  calc
    _ = ∑ ℓ ∈ Λ, ((S ℓ).card : ℝ) := by simp [Λ, S, Set.ncard_eq_toFinset_card']
    _ = ∑ i : Fin n,
        ((Λ.filter (fun ℓ => (packetPiece θ v Z P a ℓ i).Nonempty)).card : ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _i : Fin n, (2 * 6 ^ 3 * 22 ^ 3 : ℝ) := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp [mul_comm]

/-- The labels active at a point are images of the angular packets there. -/
theorem PacketRefinement.piece_label_count {n : ℕ} {β δ θ : ℝ} {v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (_h : PacketRefinement β δ θ v Y Z P a)
    (p : Space) : {ℓ | ∃ i, p ∈ packetPiece θ v Z P a ℓ i}.ncard ≤ (P p).card := by
  classical
  let code : Finset (Fin n) → PacketLabel :=
    fun W => wz_balanced_cluster_cover.lab θ (fun q => v (a q W)) p
  have hs : {ℓ | ∃ i, p ∈ packetPiece θ v Z P a ℓ i} ⊆
      ((P p).image code : Set PacketLabel) := by
    rintro ℓ ⟨i, _, W, hW, hi, hl⟩
    exact Finset.mem_image.mpr ⟨W, hW, hl⟩
  calc
    _ ≤ ((P p).image code : Set PacketLabel).ncard := Set.ncard_le_ncard hs
    _ = ((P p).image code).card := Set.ncard_coe_finset _
    _ ≤ (P p).card := Finset.card_image_le

end WangZahlLot.Obl.wz_broad_grains_initialization
