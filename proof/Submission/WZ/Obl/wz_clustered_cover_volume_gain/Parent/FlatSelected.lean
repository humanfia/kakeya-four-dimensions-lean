-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.FlatSelected.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SelectedGain
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.AssignedCover
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SplitV3b

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory Set Finset

namespace SelectedFamily

/-- Predicate counts in a selected enumeration are the original filtered counts. -/
theorem count_index {n : ℕ} (U : Finset (Fin n)) (r : Fin n → Prop)
    [DecidablePred r] :
    Interfaces.q {a | r (index U a)} = ((U.filter r).card : ℝ) := by
  change (Set.ncard {a | r ((U.equivFin.symm a : U) : Fin n)} : ℝ) = _
  rw [ncard_comp_equivFin, Factor.ncard_filter_eq]

end SelectedFamily

namespace Interfaces

open SelectedFamily

/-- Applying the flat-box estimate after weighted coarse selection. The result
is normalized by the original number of fine tubes, with the exact selection loss. -/
theorem flat_estimate_selected_cover {σ ω : ℝ} (hσ : σ ≤ 1) (hJ : Jb σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ δ ρ η h τ ν : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 →
      0 ≤ h → η ≤ h → h ≤ η₀ → ν ≤ η₀ → τ + η ≤ η₀ →
    ∀ (n N : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
      (y w : Fin N → V) (f : Fin n → Fin N),
    A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → C δ h n x v Y S Z ρ N y w f →
    ∀ (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → V)
      (e : Fin L → V ≃ₗᵢ[ℝ] V) (g : Fin N → Fin L),
      Factor.AssignedCover 4 ρ (δ ^ (-ν)) y w U m a b L z e g →
      o (δ ^ τ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S with f i ∈ U, μ (Z i) →
      384 * δ ^ (-(τ + η + 2 * h)) ≤ δ ^ (-η₀) →
    o (κ * δ ^ (ω + ε + (τ + η) * (1 - σ)) * (b / a) ^ ω *
      (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨κ, hκ, η₀, hη₀, hflat⟩ := hJ ε hε
  refine ⟨κ * (384 : ℝ) ^ (σ - 1), by positivity, η₀, hη₀, ?_⟩
  intro δ ρ η h τ ν hδ hδ100 hδρ hρ1 hh hηh hhη hνη hτη
    n N x v Y Z S y w f hA hC U m a b L z e g hbox hkeep hbudget
  classical
  have hδ1 : δ ≤ 1 := by linarith
  let P₀ := fine S f U
  obtain ⟨hA', hC'⟩ := normalized_selected_input U hδ hδ1 hh hηh hη₀.le hτη hhη
    hA hC hkeep hbudget
  have hbox' := hbox.mono (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hνη))
  have hvol := hflat δ hδ hδ100 P₀.card (x ∘ index P₀) (v ∘ index P₀)
    (Z ∘ index P₀) hA' ρ hδρ hρ1 U.card (y ∘ index U) (w ∘ index U)
    (assign S f U) hC' a b 8 hbox.width hbox.ordered
    (by simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hbox.bounded)
    (by norm_num) le_rfl L z e (g ∘ index U)
  have hcover : ∀ k, T ρ ((y ∘ index U) k) ((w ∘ index U) k) ⊆
      P a b 8 (z ((g ∘ index U) k)) (e ((g ∘ index U) k)) := by
    intro k
    simpa only [Factor.tube, Factor.box, P, ι, T, Function.comp_apply,
      show (2 : ℝ) * 4 = 8 by norm_num] using hbox.covers _ (index_mem U k)
  have hbalanced : ∀ j j', q {k | (g ∘ index U) k = j} ≤
      δ ^ (-η₀) * q {k | (g ∘ index U) k = j'} := by
    intro j j'
    simp only [Function.comp_apply]
    rw [count_index U (fun k => g k = j), count_index U (fun k => g k = j')]
    exact hbox'.balanced j j'
  have hdegree : ∀ k, q {j | T ρ ((y ∘ index U) k) ((w ∘ index U) k) ⊆
      P a b 8 (z j) (e j)} ≤ δ ^ (-η₀) := by
    intro k
    simpa only [q, Factor.ncard_univ_filter, Factor.tube, Factor.box, P, ι, T,
      Function.comp_apply, show (2 : ℝ) * 4 = 8 by norm_num] using hbox'.degree _ (index_mem U k)
  have habove : ∀ W, Convex ℝ W → o (q {j | P a b 8 (z j) (e j) ⊆ W} * (a * b * 8)) ≤
      o (δ ^ (-η₀)) * μ W := by
    intro W hW
    simpa only [q, Factor.ncard_univ_filter, Factor.box, P, ι, o, μ,
      show (2 : ℝ) * 4 = 8 by norm_num] using hbox'.above W hW
  have hbelow : ∀ j W, Convex ℝ W →
      o (q {k | (g ∘ index U) k = j ∧ T ρ ((y ∘ index U) k) ((w ∘ index U) k) ⊆
        P a b 8 (z j) (e j) ∩ W}) * μ (P a b 8 (z j) (e j)) ≤
      o (δ ^ (-η₀) * q {k | (g ∘ index U) k = j}) * μ (P a b 8 (z j) (e j) ∩ W) := by
    intro j W hW
    simp only [Function.comp_apply]
    rw [count_index U (fun k => g k = j ∧ T ρ (y k) (w k) ⊆ P a b 8 (z j) (e j) ∩ W),
      count_index U (fun k => g k = j)]
    have he : (U.filter fun k => g k = j ∧ T ρ (y k) (w k) ⊆ P a b 8 (z j) (e j) ∩ W) =
        (U.filter fun k => g k = j ∧ Factor.tube ρ y w k ⊆
          Factor.box a b (2 * 4) (z j) (e j) ∩ W) := by
      ext k
      norm_num [Factor.tube, Factor.box, P, ι, T]
    rw [he]
    have hboxeq : Factor.box a b (2 * 4) (z j) (e j) = P a b 8 (z j) (e j) := by
      norm_num [Factor.box, P, ι]
    rw [← hboxeq]
    exact hbox'.below j W hW
  have hvol' := hvol hcover hbalanced hdegree habove hbelow
  have hsub : (⋃ i, (Z ∘ index P₀) i) ⊆ ⋃ i, Y i := by
    apply Set.iUnion_subset
    intro i
    exact ((hC.1 _).2.1).trans (Set.subset_iUnion Y (index P₀ i))
  have hcard := retained_fine_card P₀ hδ hδ1 hA (fun i _ => (hC.1 i).2.1) hkeep
  have ha : 0 < a := hδ.trans_le (hδρ.trans hbox.width)
  have hb : 0 < b := ha.trans_le hbox.ordered
  have hbound := gain_of_selected_count hδ (Nat.cast_pos.mpr hA.1) (Nat.cast_pos.mpr hA'.1)
    hσ (by positivity : 0 ≤ κ * (b / a) ^ ω) (by norm_num : (0 : ℝ) < 384) hcard
    (by simpa only [o, μ, mul_assoc, mul_left_comm, mul_comm] using
      hvol'.trans (measure_mono hsub))
  simpa only [o, μ, mul_assoc, mul_left_comm, mul_comm] using hbound

end Interfaces
end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
