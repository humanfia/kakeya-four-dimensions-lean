-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.NonemptyGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.DenseCut
import Submission.WZ.Obl.wz_coarse_subtube_selection.Reindex

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open wz_coarse_subtube_selection (reindex reindex_mem reindex_injective exists_reindex_eq sum_reindex)

/-- Empty grains can be removed without changing any fine shading, fibre or
geometric scale. A count bound on the nonempty grains suffices. -/
theorem grains_of_nonempty_count
    {δ h ρ a c b g g' m : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {G : Fin L → Set V} {γ : Fin L → Fin N}
    (hδ : 0 < δ)
    (hH : HB δ h n x v S Z ρ N y w f a c b g L z e G γ m)
    (hcount : ∀ j W, Convex ℝ W →
      O (q L {j' | G j' ≠ ∅ ∧
        P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O g' * μ W) :
    H δ h n x v S Z ρ N y w f a c b g' := by
  classical
  obtain ⟨hda, hab, hbc, hc1, hgeom, hdisj, hunion, hmass, hmult, hcross, hb, _⟩ := hH
  let Q₀ := Finset.univ.filter (fun j => G j ≠ ∅)
  let τ := reindex Q₀
  have hτ (j : Fin Q₀.card) : G (τ j) ≠ ∅ := (Finset.mem_filter.mp (reindex_mem Q₀ j)).2
  have ha : 0 ≤ a := hδ.le.trans hda
  have hrc : 0 ≤ ρ * c := ha.trans hab
  have hc : 0 ≤ c := hrc.trans hbc
  refine ⟨Q₀.card, z ∘ τ, e ∘ τ, G ∘ τ, γ ∘ τ, m,
    hda, hab, hbc, hc1, fun j => hgeom (τ j), ?_, ?_, ?_, hmult,
    fun i hi j => hcross i hi (τ j), hb, ?_⟩
  · intro j j' hjj hγ
    exact hdisj _ _ (fun he => hjj (reindex_injective Q₀ he)) hγ
  · intro k
    rw [← hunion k]
    ext p
    constructor
    · rintro ⟨j, hj, hp⟩
      exact ⟨τ j, hj, hp⟩
    · rintro ⟨j, hj, hp⟩
      have hjQ : j ∈ Q₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Set.nonempty_iff_ne_empty.mp ⟨p, hp⟩⟩
      obtain ⟨j', hj'⟩ := exists_reindex_eq hjQ
      exact ⟨j', by simpa [Function.comp_def, τ, hj'], by simpa [Function.comp_def, τ, hj']⟩
  · have hcard : (Q₀.card : ℝ) ≤ L := by
      exact_mod_cast (show Q₀.card ≤ L by simpa using Finset.card_le_univ Q₀)
    have hsum : ∑ j : Fin Q₀.card, μ ((G ∘ τ) j) = ∑ j, μ (G j) := by
      change (∑ j, μ (G (reindex Q₀ j))) = ∑ j, μ (G j)
      rw [sum_reindex Q₀ (fun j => μ (G j))]
      apply Finset.sum_subset (Finset.subset_univ Q₀)
      intro j _ hj
      have hG : G j = ∅ := by simpa [Q₀] using hj
      simp [hG]
    rw [hsum]
    apply le_trans (b := O (δ ^ h * L * a * (ρ * c) * c)) ?_ hmass
    apply ENNReal.ofReal_le_ofReal
    gcongr
  · intro j W hW
    have hcard : q Q₀.card {j' |
        P (a / ρ) c c ((z ∘ τ) j') ((e ∘ τ) j') ⊆
          P (2 * a / ρ) (2 * c) (2 * c) ((z ∘ τ) j) ((e ∘ τ) j) ∧
        P a (ρ * c) c ((z ∘ τ) j') ((e ∘ τ) j') ⊆ W} ≤
        q L {j' | G j' ≠ ∅ ∧
          P (a / ρ) c c (z j') (e j') ⊆
            P (2 * a / ρ) (2 * c) (2 * c) (z (τ j)) (e (τ j)) ∧
          P a (ρ * c) c (z j') (e j') ⊆ W} := by
      exact_mod_cast Set.ncard_le_ncard_of_injOn τ
        (t := {j' | G j' ≠ ∅ ∧
          P (a / ρ) c c (z j') (e j') ⊆
            P (2 * a / ρ) (2 * c) (2 * c) (z (τ j)) (e (τ j)) ∧
          P a (ρ * c) c (z j') (e j') ⊆ W})
        (fun j' hj' => ⟨hτ j', hj'⟩) (reindex_injective Q₀).injOn (Set.toFinite _)
    apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard
      (show 0 ≤ a * (ρ * c) * c by positivity))).trans
    exact hcount (τ j) W hW

end WangZahlLot.Obl.wz_broad_grains_improvement
