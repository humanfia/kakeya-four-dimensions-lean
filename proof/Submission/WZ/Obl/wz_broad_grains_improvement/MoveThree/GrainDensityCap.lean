-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainDensityCap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainDensityCap.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FiniteUpperDensity
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GridDensity

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)
open WangZahlLot.Obl.wz_move_three_thick_grains_gain (scalar_eta scalar_nmax)

noncomputable section

/-- Unless there is already a gain, all ball densities can be capped on a
common measurable set with a uniformly small loss of grain incidence mass. -/
theorem gain_or_grain_density_cap {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω) :
    ∀ t : ℝ, 0 < t → ∃ u κ θ d₀ : ℝ,
      0 < u ∧ u ≤ t / 64 ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ u / 4 ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n N L : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
        (y w : Fin N → V) (f : Fin n → Fin N) (ρ a c b g : ℝ)
        (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (Hg : Fin L → Set V)
        (γ : Fin L → Fin N) (m : ℝ),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      C δ h n x v Y S Z ρ N y w f True →
      GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m →
      Gain σ ω κ (t / 4) δ n Y ∨
        ∃ Γ : Set V, MeasurableSet Γ ∧
          (∑ j, μ (Hg j \ Γ)) ≤ O (δ ^ u) * ∑ j, μ (Hg j) ∧
          ∀ p ∈ Γ, ∀ r : ℝ, 0 < r → r ≤ 1 →
            μ ((⋃ i, Y i) ∩ ball p r) ≤ O (δ ^ (-t) * (δ / r) ^ (ω + σ) * r ^ 3) := by
  intro t ht
  obtain ⟨κ, η, d₁, hκ, hη, hd₁, hd₁small, Hgain⟩ :=
    single_scale_density_gain hσ hσhalf hω hE (t / 64) (by positivity)
  let ν := min η (t / 16)
  have hν : 0 < ν := lt_min hη (by positivity)
  have hνη : ν ≤ η := min_le_left _ _
  have hνt : ν ≤ t / 16 := min_le_right _ _
  obtain ⟨K, hK⟩ := exists_nat_gt (12 / t)
  have hKpos : 0 < K := by exact_mod_cast (lt_trans (by positivity : (0 : ℝ) < 12 / t) hK)
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
  have hKt : 3 / (K : ℝ) ≤ t / 2 := by
    have hh := (div_lt_iff₀ ht).mp hK
    apply (div_le_iff₀ hKr).mpr
    nlinarith
  obtain ⟨C₀, hC₀, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  obtain ⟨dq, hdq, Hq⟩ := exists_rpow_cutoff (by positivity : 0 < 1 / (K : ℝ))
    (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨db, hdb, Hb⟩ := exists_rpow_cutoff ht (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨de, hde, He⟩ := exists_rpow_cutoff hη (by norm_num : (0 : ℝ) < 1 / 128)
  obtain ⟨dn, hdn, Hn⟩ := exists_rpow_cutoff (by norm_num : (0 : ℝ) < 196)
    (by positivity : 0 < 1 / C₀)
  obtain ⟨dm, hdm, Hm⟩ := exists_rpow_cutoff (by positivity : 0 < ν / 2)
    (by positivity : 0 < 1 / (2 * (K : ℝ)))
  let d₀ := min (1 / 100) (min d₁ (min dq (min db (min de (min dn dm)))))
  refine ⟨ν / 4, κ, ν / 16, d₀, by positivity, by linarith,
    hκ, by positivity, by ring_nf; exact le_rfl,
    by dsimp [d₀]; positivity, min_le_left _ _, ?_⟩
  intro δ h hδ hδd hh hhθ n N L x v Y Z S y w f ρ a c b g z e Hg γ m hA hC hG
  have hd := hδd
  dsimp only [d₀] at hd
  simp only [le_min_iff] at hd
  obtain ⟨hδsmall, hδd₁, hδq, hδb, hδe, hδn, hδm⟩ := hd
  have hδ1 : δ ≤ 1 := by linarith
  have hδ2 : δ ^ (2 : ℕ) ≤ δ := by nlinarith
  let q := δ ^ (1 / (K : ℝ))
  have hq : 0 < q := Real.rpow_pos_of_pos hδ _
  have hqsmall : q ≤ 1 / 3 := Hq δ hδ hδq
  have hscale : q ^ K = δ := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hδ.le, one_div_mul_cancel hKr.ne', Real.rpow_one]
  have hbase : 8 ≤ δ ^ (-t) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hδ t) (Hb δ hδ hδb)
    simpa only [one_div, inv_inv, ← Real.rpow_neg hδ.le] using hi
  have hmesh : δ ^ (-(t / 2)) ≤ δ ^ (-t) * q ^ 3 := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    have hh : (1 / (K : ℝ)) * 3 ≤ t / 2 := by convert hKt using 1 <;> ring
    norm_num only [Nat.cast_ofNat]
    linarith
  have hmassbudget : δ ^ ν ≤ δ ^ (ν / 4) / (2 * K) * δ ^ (2 * h) := by
    calc
      _ ≤ δ ^ (ν / 2) * δ ^ (ν / 4 + 2 * h) := by
        rw [← Real.rpow_add hδ]
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ ≤ (1 / (2 * K)) * δ ^ (ν / 4 + 2 * h) :=
        mul_le_mul_of_nonneg_right (Hm δ hδ hδm) (Real.rpow_nonneg hδ.le _)
      _ = _ := by rw [Real.rpow_add hδ]; ring
  have hnmax : (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) :=
    scalar_nmax hδ hC₀ (Nat.cast_pos.mpr hA.1)
      (hpack δ hδ hδsmall n x v (fun i => (hA.2.1 i).1)
        (fun i => (hA.2.1 i).2.1) hA.2.2.1) (Hn δ hδ hδn)
  rcases grain_finite_density_cut (t := t / 2) (ν := ν) (κ := κ) hδ
      (Real.rpow_nonneg hδ.le _) hKpos (fun j : Fin K => q ^ j.val)
      (fun j => pow_pos hq _) hA hC hG hmassbudget (by
        intro j W hW hmass hdense
        obtain ⟨hr, hr1, hδR⟩ := power_grid_radii hq hqsmall hscale j
        apply Hgain δ h ν (t / 2) (q ^ j.val) hδ hδ1 hh hr hr1
          (hδ2.trans hδd₁) hδR ?_ ?_ ?_ n x v Y W hnmax hA hW hmass hdense
        · nlinarith [mul_nonneg hδ.le (show 0 ≤ 1 / 8 - δ by linarith)]
        · exact scalar_eta hδ hδ1 hνη (He δ hδ hδe)
        · linarith) with hgain | hcap
  · left
    simpa only [show t / 2 / 2 = t / 4 by ring] using hgain
  · right
    obtain ⟨Γ, hΓ, hloss, hcap⟩ := hcap
    refine ⟨Γ, hΓ, hloss, ?_⟩
    intro p hp
    exact density_upper_of_power_grid hδ hq hKpos hscale (by linarith) hbase hmesh
      (⋃ i, Y i) p (hcap p hp)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
