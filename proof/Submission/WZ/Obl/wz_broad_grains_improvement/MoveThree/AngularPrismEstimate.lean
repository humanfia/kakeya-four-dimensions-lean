-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AngularPrismEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AngularPrismEstimate.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrismFamilyMass
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AngularPieces

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped Classical
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyEstimate BodyConvexCount BodyPacking)
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement PacketLabel packetPiece packetLabelUniverse)

noncomputable section

/-- Apply the sharp estimate to the labelled angular prisms and sum them.
The old thin slab is retained in the new short dimension. -/
theorem angular_prism_body_estimate {σ ω : ℝ} (hbody : BodyEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (n : ℕ) (U Y Z : Fin n → Set V) (x s v : Fin n → V) (a r r₀ w m p β θ lam : ℝ),
      (n : ℝ) ≤ d ^ (-100 : ℝ) →
      0 < a → a ≤ 1 / 8 → 0 < θ → θ ≤ 1 → r₀ ≤ θ →
      0 < r → d ≤ r / 32768 → 0 < w → 1 ≤ m → 1 ≤ p → 0 < lam →
      (∀ i, IsCompact (U i)) → (∀ i, Convex ℝ (U i)) →
      (∀ i, ball (x i) r ⊆ U i) →
      (∀ i, ∃ q ∈ U i, ∃ q' ∈ U i, (1 / 4 : ℝ) ≤ dist q q') →
      (∀ i, μ (U i) = O w) → (∀ i, U i ⊆ ball (0 : V) 1) →
      (∀ i, Y i ⊆ U i) → (∀ i, ‖v i‖ = 1) → (∀ i, U i ⊆ T r₀ (s i) (v i)) →
      BodyConvexCount U w m → BodyPacking U w p →
      ∀ (u : V) (t : ℝ), ‖u‖ = 1 →
      (∀ i, U i ⊆ {q | |inner ℝ u q - t| ≤ a / 2}) →
      (∀ i, |inner ℝ u (v i)| ≤ 4 * a) →
      ∀ (packets : V → Finset (Finset (Fin n))) (center : V → Finset (Fin n) → Fin n),
      PacketRefinement β r₀ θ v Y Z packets center →
      O (lam * n * w) ≤ ∑ i, μ (Z i) →
      2 * d ^ η * (2 * 6 ^ 3 * 22 ^ 3) ≤ lam →
      let b' := min (80 * θ) 4
      let a' := min (36 * a) b'
      O ((A / 2) * d ^ ε * (r / (8192 * a')) ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) *
        (w / (4 * a' * b')) ^ (σ / 2) * lam * n * w) ≤
          O (2 * θ ^ (-β)) * μ (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hsmall, H⟩ := sharp_prism_family_mass hbody ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hsmall, ?_⟩
  intro d hd hdd n U Y Z x s v a r r₀ w m p β θ lam hnmax ha ha8 hθ hθ1 hr₀θ
    hr hdr hw hm hp hlam hcompact hconvex hinter hlong hvol hball hYU hv hUT hcount hpack
    u t hu hslab hflat packets center href hmass hbudget
  let b' := min (80 * θ) 4
  let a' := min (36 * a) b'
  have hb' : 0 < b' := lt_min (by positivity) (by norm_num)
  have ha' : 0 < a' := lt_min (by positivity) hb'
  have hab' : a' ≤ b' := min_le_right _ _
  have hb'4 : b' ≤ 4 := min_le_right _ _
  let Λ := packetLabelUniverse θ s v
  let W : {ℓ // ℓ ∈ Λ} → Fin n → Set V := fun ℓ => packetPiece θ v Z packets center ℓ.val
  let S : {ℓ // ℓ ∈ Λ} → Finset (Fin n) := fun ℓ => Finset.univ.filter fun i => (W ℓ i).Nonempty
  have hZW i : Z i ⊆ U i := (href.1 i).2.trans (hYU i)
  have hWT ℓ i : W ℓ i ⊆ U i := fun _ hq => hZW i hq.1
  have hWV ℓ i : W ℓ i ⊆ ⋃ i, Y i := fun q hq =>
    mem_iUnion.mpr ⟨i, (href.1 i).2 hq.1⟩
  have hbox : ∀ ℓ : {ℓ // ℓ ∈ Λ}, ∃ (z : V) (e : V ≃ₗᵢ[ℝ] V),
      ∀ i ∈ S ℓ, U i ⊆ P a' b' 4 z e := by
    intro ℓ
    by_cases hne : ∃ i, (W ℓ i).Nonempty
    · obtain ⟨z, e, he⟩ := packet_piece_prism href ha.le ha8 hθ hr₀θ hv hYU hUT hball u hu hslab hflat ℓ.val hne
      exact ⟨z, e, fun i hi => he i (Finset.mem_filter.mp hi).2⟩
    · exact ⟨0, LinearIsometryEquiv.refl ℝ V, fun i hi => (hne ⟨i, (Finset.mem_filter.mp hi).2⟩).elim⟩
  choose z e hbox using hbox
  have hZT i : Z i ⊆ T r₀ (s i) (v i) := (hZW i).trans (hUT i)
  have hZball i : Z i ⊆ ball (0 : V) 1 := (hZW i).trans (hball i)
  obtain ⟨_, _, _, _, hover, _, hmassW⟩ := href.finite_clusters hθ hr₀θ hv hZT hZball
  have hdup : (∑ ℓ, ((S ℓ).card : ℝ)) ≤ (2 * 6 ^ 3 * 22 ^ 3 : ℝ) * n := by
    have hh := href.piece_card_sum hθ hr₀θ hv hZT
    have he : (∑ ℓ, ((S ℓ).card : ℝ)) =
        ∑ ℓ ∈ Λ, ({i | (packetPiece θ v Z packets center ℓ i).Nonempty}.ncard : ℝ) := by
      rw [← Finset.sum_coe_sort Λ]
      apply Finset.sum_congr rfl
      intro ℓ _
      simp only [S, W, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    rw [he]
    exact hh
  have hfin : μ (⋃ i, Y i) ≠ ⊤ := ne_top_of_le_ne_top (measure_ball_lt_top.ne)
    (measure_mono (iUnion_subset fun i => (hYU i).trans (hball i)))
  have hdr4 : d ≤ r / 4 := hdr.trans (by linarith)
  have hdrB : d ≤ r / (8192 * a') := by
    apply hdr.trans
    apply div_le_div_of_nonneg_left hr.le (by positivity : 0 < 8192 * a')
    have hh := hab'.trans hb'4
    linarith
  apply H d hd hdd n U x a' b' r w m p hnmax ha' hab' hb'4 hr hdr4 hw hdrB hm hp
    hcompact hconvex hinter hlong hvol hcount hpack {ℓ // ℓ ∈ Λ} W S z e (⋃ i, Y i)
    lam (2 * 6 ^ 3 * 22 ^ 3) (2 * θ ^ (-β)) hlam (by positivity) hfin
    (fun ℓ i => href.measurable_piece ℓ.val i) hWT hWV
    (fun ℓ i hi => Set.not_nonempty_iff_eq_empty.mp (by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hi))
    hbox (by simpa only [W, μ] using hmass.trans_eq hmassW.symm) hdup hbudget
  intro q _
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, W] using hover q

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
