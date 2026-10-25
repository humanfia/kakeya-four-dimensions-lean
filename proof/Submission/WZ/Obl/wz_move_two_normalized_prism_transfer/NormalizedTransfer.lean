-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.NormalizedTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.NormalizedRefinement
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.DyadicPower

noncomputable section
namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
open Set MeasureTheory

/-- A uniform transfer using per-prism normalized incidence density instead of
assuming that all prism multiplicities have already been made comparable. -/
theorem normalized_prism_transfer {ω ζ ε : ℝ} (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
          A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
          ∀ (ρ c : ℝ) (D : PrismData ω ζ δ η ρ c n x v Y) (M : Fin D.L → ℝ),
            (∀ j, 0 < M j) →
            (∀ j p, q n {i | p ∈ D.W i j} ≤ M j) →
            (∀ j, O (δ ^ η * M j) * μ (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
              ∑ i, μ (D.W i j)) →
            (∀ i j j', j ≠ j' → D.γ j = D.γ j' → (D.W i j).Nonempty →
              Disjoint (D.W i j') (P D.a (ρ * c) c (D.z j) (D.e j))) →
            ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ)
              (y w : Fin N → V) (f : Fin n → Fin N) (g : ℝ),
              C δ ε n x v Y S Z ρ N y w f True ∧ 0 < g ∧
              Broad ω ζ δ ε ρ n N v S Z f ∧ H δ ε n x v S Z ρ N y w f D.a c 0 g := by
  obtain ⟨u, d, hu, huε, hd, htransfer⟩ := regular_prism_transfer (ω := ω) (ζ := ζ) hε
  let s := u / 10
  have hs : 0 < s := by dsimp [s]; positivity
  have hsu : 10 * s = u := by dsimp [s]; ring
  obtain ⟨d₁, hd₁, hlog⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.logarithmic_count_power
      (by norm_num : (0 : ℝ) < 7) hs
  obtain ⟨d₂, hd₂, hconstant⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.uniform_small_power_comparison
      (by norm_num : (0 : ℝ) < 1000000000000) (by norm_num : (0 : ℝ) < 3)
  refine ⟨s, min d (min d₁ (min d₂ 1)), hs, by linarith, by positivity, ?_⟩
  intro δ hδ hδ0 n x v Y hA ρ c D M hM hcap hnormal havoid
  have hcut : δ ≤ d ∧ δ ≤ d₁ ∧ δ ≤ d₂ ∧ δ ≤ 1 := by
    simpa only [le_min_iff] using hδ0
  have hconst : (1000000000000 : ℝ) ≤ δ ^ (-3 : ℝ) := by
    simpa only [Real.rpow_zero, mul_one] using
      hconstant δ hδ hcut.2.2.2 hcut.2.2.1 1000000000000 0 (-3) le_rfl (by norm_num)
  have hn := WangZahlLot.Obl.wz_coarse_grains_assembly.fine_count_power_seven hδ hconst
    (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.1) hA.2.2.1
  have hlog' : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ δ ^ (-s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlog δ hδ hcut.2.1 n hn
  have hmass : ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ 2 * δ ^ u ≤ δ ^ s := by
    calc
      _ ≤ (δ ^ (-s)) ^ 2 * δ ^ u := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hlog' 2) (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (u - 2 * s) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hcut.2.2.2 (by linarith)
  have hdense : ((Nat.log 2 n + 1 : ℕ) : ℝ) * δ ^ u ≤ δ ^ s := by
    calc
      _ ≤ δ ^ (-s) * δ ^ u := mul_le_mul_of_nonneg_right hlog' (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (u - s) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hcut.2.2.2 (by linarith)
  obtain ⟨D', m, ha, _, hmult, havoid'⟩ := normalized_prism_refinement hδ hcut.2.2.2
    (by linarith : s ≤ u) D M hM hcap hnormal havoid hmass hdense
  have hA' : A δ u (δ ^ (-u)) (δ ^ (-u)) n x v Y := by
    have hh : WangZahlLot.Obl.wz_multiscale_finite_tower.Admissible
      δ s (δ ^ (-s)) (δ ^ (-s)) n x v Y := hA
    exact hh.mono_error hδ hcut.2.2.2 (by linarith : s ≤ u)
  obtain ⟨S, Z, N, y, w, f, g, hC, hg, hbr, hH⟩ :=
    htransfer δ hδ hcut.1 n x v Y hA' ρ c D' m hmult havoid'
  exact ⟨S, Z, N, y, w, f, g, hC, hg, hbr, by simpa only [ha] using hH⟩

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
