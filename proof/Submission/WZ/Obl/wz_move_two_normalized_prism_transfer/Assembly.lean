-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.Assembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Crossing

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer

open Set MeasureTheory

/-- Total grain density suffices for the frozen grains predicate; density need
not hold separately in every prism. -/
theorem grains_of_separated_pieces_mass {δ h ρ a c m : ℝ} {n L N : ℕ}
    {x v : Fin n → V} {W : Fin n → Fin L → Set V} {S : Finset (Fin n)}
    {γ : Fin L → Fin N} {f : Fin n → Fin N} {y w : Fin N → V}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hac : a ≤ ρ * c) (hρc : ρ * c ≤ c) (hc1 : c ≤ 1)
    (hW : ∀ i j, MeasurableSet (W i j) ∧ W i j ⊆ P a (ρ * c) c (z j) (e j))
    (hgeom : ∀ j, P a (ρ * c) c (z j) (e j) ⊆ T ρ (y (γ j)) (w (γ j)) ∧
      ι (e j (w (γ j))) 0 ^ 2 + ι (e j (w (γ j))) 1 ^ 2 ≤ (10 * ρ) ^ 2)
    (hassign : ∀ i j, (W i j).Nonempty → i ∈ S ∧ f i = γ j)
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    (hmass : O (δ ^ h * L * a * (ρ * c) * c) ≤ ∑ j, μ (pieceSupport W j))
    (hmult : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ pieceUnion W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ pieceUnion W i} ∈ Set.Icc m (2 * m))
    (hcross : ∀ i j, (W i j).Nonempty →
      (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a (ρ * c) c (z j) (e j)),
        |ι (e j (p - z j)) 2| = c / 2) ∧
      ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
        ∃ p ∈ T δ (x i) (v i) ∩ P a (ρ * c) c (z j) (e j),
          ι (e j (p - z j)) 2 = t)
    (havoid : ∀ i j j', j ≠ j' → γ j = γ j' → (W i j).Nonempty →
      Disjoint (W i j') (P a (ρ * c) c (z j) (e j))) :
    ∃ g : ℝ, 0 < g ∧ H δ h n x v S (pieceUnion W) ρ N y w f a c 0 g := by
  have ha : 0 ≤ a := hδ.le.trans hδa
  have hrc : 0 ≤ ρ * c := ha.trans hac
  have hc : 0 ≤ c := hrc.trans hρc
  refine ⟨max 1 (L : ℝ), lt_of_lt_of_le one_pos (le_max_left _ _),
    L, z, e, pieceSupport W, γ, m, hδa, hac, hρc, hc1, ?_, hdisj,
    pieceUnion_fibre_cover hassign, hmass, hmult, ?_, hc, ?_⟩
  · intro j
    refine ⟨MeasurableSet.iUnion (fun i => (hW i j).1), ?_, (hgeom j).1, (hgeom j).2⟩
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact (hW i j).2 hi
  · intro i hi j hij hmeet
    have hne := pieceUnion_meets_support (fun i j h => (hassign i j h).2) hdisj hij hmeet
    exact ⟨pieceUnion_crossing (fun i j h => (hassign i j h).2) hdisj havoid hij hmeet,
      hcross i j hne⟩
  · intro j B hB
    apply WangZahlLot.Obl.wz_broad_grains_initialization.finite_uniform_volume_count volume
      (fun j' => P a (ρ * c) c (z j') (e j')) (by positivity)
    intro j'
    exact (WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha hrc hc
      (z j') (e j')).symm.le

/-- Dense assigned prism pieces yield the full frozen grains predicate when the
cross-prism avoidance and common multiplicity clauses have been supplied. -/
theorem grains_of_separated_pieces {δ h ρ a c m : ℝ} {n L N : ℕ}
    {x v : Fin n → V} {W : Fin n → Fin L → Set V} {S : Finset (Fin n)}
    {γ : Fin L → Fin N} {f : Fin n → Fin N} {y w : Fin N → V}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hac : a ≤ ρ * c) (hρc : ρ * c ≤ c) (hc1 : c ≤ 1)
    (hW : ∀ i j, MeasurableSet (W i j) ∧ W i j ⊆ P a (ρ * c) c (z j) (e j))
    (hgeom : ∀ j, P a (ρ * c) c (z j) (e j) ⊆ T ρ (y (γ j)) (w (γ j)) ∧
      ι (e j (w (γ j))) 0 ^ 2 + ι (e j (w (γ j))) 1 ^ 2 ≤ (10 * ρ) ^ 2)
    (hassign : ∀ i j, (W i j).Nonempty → i ∈ S ∧ f i = γ j)
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    (hdense : ∀ j, O (δ ^ h) * μ (P a (ρ * c) c (z j) (e j)) ≤ μ (pieceSupport W j))
    (hmult : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ pieceUnion W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ pieceUnion W i} ∈ Set.Icc m (2 * m))
    (hcross : ∀ i j, (W i j).Nonempty →
      (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a (ρ * c) c (z j) (e j)),
        |ι (e j (p - z j)) 2| = c / 2) ∧
      ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
        ∃ p ∈ T δ (x i) (v i) ∩ P a (ρ * c) c (z j) (e j),
          ι (e j (p - z j)) 2 = t)
    (havoid : ∀ i j j', j ≠ j' → γ j = γ j' → (W i j).Nonempty →
      Disjoint (W i j') (P a (ρ * c) c (z j) (e j))) :
    ∃ g : ℝ, 0 < g ∧ H δ h n x v S (pieceUnion W) ρ N y w f a c 0 g := by
  have ha : 0 ≤ a := hδ.le.trans hδa
  have hrc : 0 ≤ ρ * c := ha.trans hac
  have hc : 0 ≤ c := hrc.trans hρc
  have hmass : O (δ ^ h * L * a * (ρ * c) * c) ≤ ∑ j, μ (pieceSupport W j) := by
    calc
      _ = ∑ _j : Fin L, O (δ ^ h * (a * (ρ * c) * c)) := by
        rw [WangZahlLot.Obl.wz_move_two_long_grains_gain.sum_const_ofReal]
        congr 1
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        have hj := hdense j
        change O (δ ^ h) * volume (WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Box a (ρ * c) c (z j) (e j)) ≤ _ at hj
        rw [WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha hrc hc,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)] at hj
        exact hj
  exact grains_of_separated_pieces_mass hδ hδa hac hρc hc1 hW hgeom hassign hdisj
    hmass hmult hcross havoid

/-- No incidence mass is lost by taking the disjoint union along each fine tube. -/
theorem pieceUnion_mass {n L : ℕ} (W : Fin n → Fin L → Set V)
    (hW : ∀ i j, MeasurableSet (W i j))
    (hdisj : ∀ i j j', j ≠ j' → Disjoint (W i j) (W i j')) :
    (∑ i, μ (pieceUnion W i)) = ∑ i, ∑ j, μ (W i j) := by
  apply Finset.sum_congr rfl
  intro i _
  simpa only [μ, pieceUnion, tsum_fintype] using
    measure_iUnion (fun j j' hne => hdisj i j j' hne) (hW i)

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
