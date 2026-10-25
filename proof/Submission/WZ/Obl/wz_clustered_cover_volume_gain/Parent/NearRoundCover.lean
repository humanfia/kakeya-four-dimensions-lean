-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.NearRoundCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FlatSelected
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FlatGain
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.AssignedRichness
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SelectedFactorization

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces

open MeasureTheory Finset

/-- Steps 1--2 of the large-coefficient argument, with uniform parameters and
all selection losses paid: either the volume gains, or the factored boxes have
comparable transverse widths and their coarse cover satisfies (9.6). -/
theorem near_round_factored_cover {σ ω ζ t νmax : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hω : 0 < ω) (hζ : 0 < ζ)
    (ht : 0 < t) (hνmax : 0 < νmax) (hJ : Jb σ ω) :
    ∃ κ ν h d : ℝ, 0 < κ ∧ 0 < ν ∧ ν ≤ νmax ∧ 6 * ν ≤ ζ ∧
      0 < h ∧ h ≤ ν / 20 ∧ 0 < d ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d → ∀ η : ℝ, η ≤ h →
    ∀ (n N : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
      (ρ : ℝ) (y w : Fin N → V) (f : Fin n → Fin N),
      δ ≤ ρ → ρ ≤ 1 → A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      C δ h n x v Y S Z ρ N y w f →
      (∀ U : Finset (Fin N),
        o (δ ^ (ζ / 2)) * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S with f i ∈ U, μ (Z i) →
        ¬ ∀ W, Convex ℝ W →
          o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ o (δ ^ (-ζ)) * μ W) →
      o (κ * δ ^ (ω - ω * t / 4) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
      ∃ (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → V)
        (e : Fin L → V ≃ₗᵢ[ℝ] V) (g : Fin N → Fin L),
        U.Nonempty ∧ δ ^ (-ζ) < m ∧
        Factor.AssignedCover 4 ρ (δ ^ (-ν)) y w U m a b L z e g ∧
        δ ^ t * b ≤ a ∧ δ ^ (t + ν - ζ) * (b / ρ) ^ 2 * L ≤ N ∧
        o (δ ^ (h + 2 * ν + ν / 10)) * ∑ i, μ (Y i) ≤
          ∑ i ∈ S with f i ∈ U, μ (Z i) ∧
        (∀ j ∈ U, ∀ k ∈ U,
          coarseWeight S Z f j ≤ δ ^ (-(ν / 20)) * coarseWeight S Z f k) ∧
        ∀ k ∈ U,
          o (δ ^ (2 * h + η + ν + ν / 10) * q {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤
            ∑ i ∈ S with f i = k, μ (Z i) := by
  have hε : 0 < ω * t / 4 := by positivity
  obtain ⟨κ, hκ, η₀, hη₀, hflat⟩ := flat_estimate_selected_cover hσ1 hJ (ω * t / 4) hε
  let ν := min νmax (min (ζ / 6) (min (η₀ / 8) (ω * t / 16)))
  have hν : 0 < ν := lt_min hνmax (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hνζ : 6 * ν ≤ ζ := by
    have : ν ≤ ζ / 6 := (min_le_right νmax _).trans (min_le_left (ζ / 6) _)
    linarith
  have hνη : ν ≤ η₀ / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνt : ν ≤ ω * t / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨h, d₁, hh, hhν, hd₁, hfactor⟩ := large_factored_coarse_cover hν hνζ
  obtain ⟨d₂, hd₂, hconstant⟩ := fixed_constant_power_bound (C := 384) (by norm_num) hν
  refine ⟨κ, ν, h, min d₁ d₂, hκ, hν, min_le_left _ _, hνζ,
    hh, hhν, lt_min hd₁ hd₂, ?_⟩
  intro δ hδ hδ100 hδd η hη n N x v Y Z S ρ y w f hδρ hρ1 hA hC hno
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨U, m, a, b, L, z, e, g, hU, hm, hbox, hkeep, hcmp, hdensity⟩ :=
    hfactor δ hδ (hδd.trans (min_le_left _ _)) η hη n N x v Y Z S ρ y w f
      hδρ hρ1 hA hC hno
  have hbudget : 384 * δ ^ (-((h + 2 * ν + ν / 10) + η + 2 * h)) ≤ δ ^ (-η₀) := by
    calc
      _ ≤ δ ^ (-ν) * δ ^ (-((h + 2 * ν + ν / 10) + η + 2 * h)) :=
        mul_le_mul_of_nonneg_right (hconstant δ hδ (hδd.trans (min_le_right _ _)))
          (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-ν + -((h + 2 * ν + ν / 10) + η + 2 * h)) := (Real.rpow_add hδ _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hvol := hflat δ ρ η h (h + 2 * ν + ν / 10) ν hδ hδ100 hδρ hρ1
    hh.le hη (by linarith) (by linarith) (by linarith)
    n N x v Y Z S y w f hA hC U m a b L z e g hbox hkeep hbudget
  have hloss : ((h + 2 * ν + ν / 10) + η) * (1 - σ) ≤ 4 * ν := by
    calc
      _ ≤ (4 * ν) * 1 := mul_le_mul (by linarith) (by linarith)
        (by linarith) (by positivity)
      _ = _ := mul_one _
  have hbudget' : (ω * t / 4 + ((h + 2 * ν + ν / 10) + η) * (1 - σ)) +
      ω * t / 4 ≤ t * ω := by nlinarith
  have hvol' : o (κ * δ ^ (ω + (ω * t / 4 + ((h + 2 * ν + ν / 10) + η) * (1 - σ))) *
      (b / a) ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) := by
    simpa only [add_assoc] using hvol
  rcases flat_prism_gain_or_almost_tube hδ hδ1 (hδ.trans_le (hδρ.trans hbox.width))
      hω.le hκ.le hbudget' hvol' with hgain | hshape
  · exact Or.inl hgain
  · exact Or.inr ⟨U, m, a, b, L, z, e, g, hU, hm, hbox, hshape,
      hbox.rich_scale_count_original hδ (hδ.trans_le hδρ) (by norm_num) hm.le hshape,
      hkeep, hcmp, hdensity⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces
