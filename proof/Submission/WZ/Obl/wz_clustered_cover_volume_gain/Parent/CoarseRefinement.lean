-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarseRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseCore
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseUniform
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.DyadicMultiplicity

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

namespace Interfaces

/-- Coarse E upgrades a bound within each assigned packet to a bound on global
fine multiplicity, after an arbitrarily small power loss of shading mass. -/
theorem coarse_refinement_from_packet_bound {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2)
    (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    {τ χ D : ℝ} (hτ : 0 < τ) (hχ : 0 < χ) (hD : 0 < D) :
    ∃ Cc H d0 : ℝ, 0 < Cc ∧ 0 < H ∧ 0 < d0 ∧
    ∀ {δ η h ρ ν ξ t m a b r B : ℝ} {n N L : ℕ}
      {x v : Fin n → V} {Y Z W : Fin n → Set V} {S : Finset (Fin n)}
      {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
      {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L},
      0 < δ → δ ≤ d0 → δ ≤ ρ →
      0 ≤ h → 0 ≤ η → 0 ≤ ν → 0 ≤ ξ →
      h ≤ τ / 100 → η ≤ τ / 100 → ν ≤ τ / 100 → ξ ≤ τ / 100 → t ≤ τ / 100 → r ≤ H →
      U.Nonempty → A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → C δ h n x v Y S Z ρ N y w f →
      Factor.AssignedCover 4 ρ (δ ^ (-ν)) y w U m a b L z e g → δ ^ t * b ≤ a →
      (n : ℝ) ≤ δ ^ (-D) → (n : ℝ) ≤ δ ^ (-ξ) * (S.filter fun i => f i ∈ U).card →
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) →
      (∀ i, (W i).Nonempty → i ∈ S ∧ f i ∈ U) →
      o (δ ^ r * n * δ ^ 2) ≤ ∑ i, μ (W i) →
      0 < B → (∀ p j, fiberMultiplicity (g ∘ f) W j p ≤ o B) →
      ∃ W' : Fin n → Set V, (∀ i, MeasurableSet (W' i) ∧ W' i ⊆ W i) ∧
        o (δ ^ χ) * (∑ i, μ (W i)) ≤ ∑ i, μ (W' i) ∧
        (∀ p, multiplicity W' p ≤ o (Cc * B * δ ^ (-τ) * (b ^ (-ω) * (L * b) ^ σ))) := by
  obtain ⟨Cc, H0, d0, hCc, hH0, hd0, hcoarse⟩ := uniform_coarse_multiplicity hσ hσ2 hω hω1 hE hτ
  let β := min χ (H0 / 4)
  have hβ : 0 < β := lt_min hχ (by positivity)
  obtain ⟨d1, hd1, hdyadic⟩ := dyadic_refinement_multiplicity hD hβ
  obtain ⟨d2, hd2, hsmall⟩ := fixed_constant_power_bound (C := 4) (ν := H0 / 2)
    (by norm_num) (by positivity)
  refine ⟨8 * Cc, H0 / 4, min 1 (min d0 (min d1 d2)), by positivity, by positivity,
    lt_min zero_lt_one (lt_min hd0 (lt_min hd1 hd2)), ?_⟩
  intro δ η h ρ ν ξ t m a b r B n N L x v Y Z W S y w f U z e g
    hδ hδd hδρ hh hη hν hξ hhsmall hηsmall hνsmall hξsmall htsmall hr
    hU hA hC hcover hround hn hcard hW hsupport hdense hB hpacket
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hδd0 : δ ≤ d0 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd1 : δ ≤ d1 := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd2 : δ ≤ d2 := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hb : 0 < b := hδ.trans_le (hδρ.trans (hcover.width.trans hcover.ordered))
  obtain ⟨M, W', hM, hW', hmass, hlower, hupper⟩ := hdyadic δ hδ hδd1 n hn W (fun i => (hW i).1)
  have hW'sub (i) : W' i ⊆ Z i := (hW' i).2.trans (hW i).2
  have hW'fin (i) : volume (W' i) ≠ ⊤ := ne_of_lt ((measure_mono
    ((hW'sub i).trans ((hC.1 i).2.1.trans ((hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1)))).trans_lt measure_ball_lt_top)
  have hW'support (i) (hi : (W' i).Nonempty) : i ∈ S ∧ f i ∈ U :=
    hsupport i (hi.mono (hW' i).2)
  have hW'dense : o (δ ^ (r + β) * n * δ ^ 2) ≤ ∑ i, μ (W' i) := by
    calc
      _ = o (δ ^ β) * o (δ ^ r * n * δ ^ 2) := by
        dsimp only [o]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ o (δ ^ β) * ∑ i, μ (W i) := mul_le_mul_right hdense _
      _ ≤ _ := hmass
  have hW'pos : 0 < ∑ i, μ (W' i) := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
    positivity)) hW'dense
  have hbudget : 4 * δ ^ (H0 - (r + β)) ≤ 1 := by
    have he : H0 / 2 ≤ H0 - (r + β) := by have := min_le_right χ (H0 / 4); dsimp [β] at *; linarith
    calc
      _ ≤ δ ^ (-(H0 / 2)) * δ ^ (H0 / 2) :=
        mul_le_mul (hsmall δ hδ hδd2)
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 he)
          (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hδ.le _)
      _ = 1 := by rw [← Real.rpow_add hδ]; simp
  have hW'packet (p) (j) : fiberMultiplicity (g ∘ f) W' j p ≤ o B :=
    (fiberMultiplicity_mono (g ∘ f) (fun i => (hW' i).2) j p).trans (hpacket p j)
  have hbound := global_level_bound_of_packet_estimate (Cc := Cc * δ ^ (-τ) *
    (b ^ (-ω) * (L * b) ^ σ)) hδ hb hM.le hB S f U g W' (fun i => (hW' i).1)
    hW'fin hW'support hW'pos hW'dense hbudget hlower hupper hW'packet
  have hout : ∀ p, multiplicity W' p ≤ o (8 * B * (Cc * δ ^ (-τ) * (b ^ (-ω) * (L * b) ^ σ))) := by
    apply hbound
    intro W'' hsub hocc hdens hlevel
    apply hcoarse hδ hδd0 hδρ hh hη hν hξ hhsmall hηsmall hνsmall hξsmall htsmall
      le_rfl hU hA hC hcover hround (fun i => (hsub i).trans (hW'sub i)) hocc hcard
    · intro k hk hocc
      convert hdens k hk hocc using 1
      · simp only [o, q, Set.ncard_eq_toFinset_card']
        congr 5
        ext i
        simp
      · congr 1
    · positivity
    · exact hlevel
  refine ⟨W', hW', ?_, ?_⟩
  · exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _))) _).trans hmass
  · intro p
    convert hout p using 1
    congr 1
    ring

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
