-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Planiness.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Planiness.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.LowDensity
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.DenseCut
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NarrowState
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PlanePackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinementPowers

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (assignedFiber confinement_density_power_lower)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

noncomputable section

def grainPlaneScale (δ b a ρ c : ℝ) : ℝ := min 1 (δ ^ (-b) * a / (ρ * c))

/-- Step 2 of Move 3. Either there is a power volume gain, or the frozen
grains have a refinement whose incident normal directions lie in the
prescribed small angular range. All dimensions and coarse tubes are retained. -/
theorem gain_or_plane_narrow_grains {σ ω b ε : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hb : 0 < b) (hb1 : b ≤ 1) (hε : 0 < ε) :
    ∃ κ θ d₀ : ℝ, 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ (ζ ρ a c g : ℝ) (N L : ℕ) (S : Finset (Fin n)) (Z : Fin n → Set V)
        (y w : Fin N → V) (f : Fin n → Fin N) (z : Fin L → V)
        (e : Fin L → V ≃ₗᵢ[ℝ] V) (Hg : Fin L → Set V) (γ : Fin L → Fin N) (m : ℝ),
      C δ h n x v Y S Z ρ N y w f True → Broad ω ζ δ h ρ n N v S Z f →
      GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m →
      Gain σ ω κ (b * ω / 2) δ n Y ∨
      ∃ (h' : ℝ) (Z' : Fin n → Set V) (H' : Fin L → Set V),
        h ≤ h' ∧ h' ≤ ε ∧ (∀ i, Z' i ⊆ Z i) ∧ (∀ j, H' j ⊆ Hg j) ∧
        C δ h' n x v Y S Z' ρ N y w f True ∧ Broad ω ζ δ h' ρ n N v S Z' f ∧
        GrainWitnesses δ h' n x v S Z' ρ N y w f a c 0 g L z e H' γ m ∧
        ∀ i j p, p ∈ H' i → p ∈ H' j → grainPlaneScale δ b a ρ c = 1 ∨
          pd (boxAxis (e i) 0) (boxAxis (e j) 0) ≤ grainPlaneScale δ b a ρ c := by
  obtain ⟨ν, κ, θ, d₁, hν, hνε, hκ, hθ, hd₁, hd₁small, Hlow⟩ :=
    gain_or_low_ball_density hσ hσhalf hω hE hb hb1 (by positivity : 0 < ε / 8)
  obtain ⟨dc, hdc, Hconf⟩ := confinement_density_power_lower hν
  obtain ⟨dd, hdd, Hd⟩ := exists_rpow_cutoff (by positivity : 0 < ν / 2)
    (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨de, hde, He⟩ := exists_rpow_cutoff (by positivity : 0 < ε / 4)
    (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨dt, hdt, Ht⟩ := exists_rpow_cutoff hν (by norm_num : (0 : ℝ) < 1 / 92160)
  let θ' := min θ (min (ε / 4) (ν / 2))
  let d₀ := min d₁ (min dc (min dd (min de dt)))
  refine ⟨κ, θ', d₀, hκ, by dsimp [θ']; positivity, ?_,
    by dsimp [d₀]; positivity, (min_le_left _ _).trans hd₁small, ?_⟩
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans (by linarith)
  intro δ h hδ hδd hh hhθ n x v Y hA ζ ρ a c g N L S Z y w f z e Hg γ m hC hB hG
  have hd := hδd
  dsimp only [d₀] at hd
  simp only [le_min_iff] at hd
  obtain ⟨hδd₁, hδc, hδd, hδe, hδt⟩ := hd
  have hδ1 : δ ≤ 1 := (hδd₁.trans hd₁small).trans (by norm_num)
  have hhθ₀ : h ≤ θ := hhθ.trans (min_le_left _ _)
  have hhε : h ≤ ε / 4 := hhθ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhν : h ≤ ν / 2 := hhθ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ha : 0 < a := hδ.trans_le hG.1
  have hrc : 0 < ρ * c := ha.trans_le hG.2.1
  have hc : 0 < c := hrc.trans_le hG.2.2.1
  have hρ : 0 < ρ := (mul_pos_iff_of_pos_right hc).mp hrc
  have hrc1 : ρ * c ≤ 1 := hG.2.2.1.trans hG.2.2.2.1
  let s : ℝ := δ ^ (-b) * a / (ρ * c)
  by_cases hlarge : 1 ≤ s
  · refine Or.inr ⟨h, Z, Hg, le_rfl, by linarith, fun _ => Subset.rfl,
      fun _ => Subset.rfl, hC, hB, hG, ?_⟩
    intro i j p hi hj
    exact Or.inl (min_eq_left hlarge)
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := le_of_not_ge hlarge
  have hscale : grainPlaneScale δ b a ρ c = s := min_eq_right hs1
  have hpow : 1 ≤ δ ^ (-b) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hseq : s * ρ * c = δ ^ (-b) * a := by dsimp [s]; field_simp
  have has : a ≤ s * ρ * c := by rw [hseq]; nlinarith
  have hδs : δ ≤ s := by
    apply (le_div_iff₀ hrc).mpr
    nlinarith [hG.1, mul_le_mul_of_nonneg_left hrc1 hδ.le]
  have hR : 0 < δ ^ (1 - b) / 2 := by positivity
  have hRs : δ ^ (1 - b) / 2 ≤ (s / 2) * ρ * c := by
    have hp : δ ^ (1 - b) = δ ^ (-b) * δ := by
      calc
        _ = δ ^ (-b + 1) := by congr 1; ring
        _ = δ ^ (-b) * δ := by rw [Real.rpow_add hδ, Real.rpow_one]
    rw [hp]
    nlinarith [mul_le_mul_of_nonneg_left hG.1 (Real.rpow_nonneg hδ.le (-b))]
  have hZmass : O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i, μ (Z i) :=
    hC.2.1.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ S))
  rcases Hlow δ h hδ hδd₁ hh hhθ₀ n x v Y Z hA
    (fun i => ⟨(hC.1 i).1, (hC.1 i).2.1⟩) hZmass with hgain | hlow
  · exact Or.inl hgain
  obtain ⟨cut, hcut, hcutmass, hupper⟩ := hlow
  have hbudget1R : δ ^ (ε / 2) ≤ (1 / 16) * δ ^ h := by
    calc
      _ ≤ δ ^ (ε / 4 + h) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ (ε / 4) * δ ^ h := Real.rpow_add hδ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (He δ hδ hδe) (Real.rpow_nonneg hδ.le _)
  have hbudget1 : O (δ ^ (ε / 2)) ≤ O ((1 / 2 : ℝ) / 8) * O (δ ^ h) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by convert hbudget1R using 1 <;> norm_num)
  obtain ⟨H₁, hH₁, hmass₁, hdense₁, hC₁, hB₁, hG₁⟩ :=
    dense_grain_state_of_common_cut hδ hδ1 (by linarith : h ≤ ε / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by positivity : 0 ≤ δ ^ h / 8)
      hA hC hB hG (fun _ => cut) (fun _ => hcut)
      (by simpa [O, ENNReal.ofReal_div_of_pos] using hcutmass)
      (by linarith : δ ^ h / 8 ≤ (1 / 2 : ℝ) / 4 * δ ^ h) hbudget1
  have hD : δ ^ ν ≤ δ ^ h / 8 := by
    calc
      _ = δ ^ (ν / 2) * δ ^ (ν / 2) := by rw [← Real.rpow_add hδ]; congr 1 <;> ring
      _ ≤ (1 / 8) * δ ^ h := mul_le_mul (Hd δ hδ hδd)
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhν) (by positivity) (by norm_num)
      _ = _ := by ring
  have hbudget2R : δ ^ ε ≤ (1 / 8) * δ ^ (ε / 2) := by
    calc
      _ = δ ^ (ε / 2) * δ ^ (ε / 2) := by rw [← Real.rpow_add hδ]; congr 1 <;> ring
      _ ≤ δ ^ (ε / 4) * δ ^ (ε / 2) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right ((He δ hδ hδe).trans (by norm_num)) (by positivity)
  have hbudget2 : O (δ ^ ε) ≤ O (1 / 8 : ℝ) * O (δ ^ (ε / 2)) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hbudget2R
  rcases density_or_narrow_grain_state hδ hδ1 (by linarith : ε / 2 ≤ ε)
    hs hs1 has hR hRs (by positivity : 0 < δ ^ h / 8)
    (Real.rpow_nonneg hδ.le (6 * ν))
    (fun i => (hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1) hC₁ hB₁ hG₁ hdense₁
    (fun j p hp => hupper p ((hH₁ j).2 hp).2) hbudget2 with hden | hnarrow
  · have hlower := Hconf δ hδ hδ1 hδc a ρ c (δ ^ h / 8) s hG.1 hG.2.1 hrc1 hD hδs
    have hp : δ ^ (6 * ν) = δ ^ ν * δ ^ (5 * ν) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    have hsmall : 46080 * δ ^ (6 * ν) < δ ^ (5 * ν) := by
      rw [hp]
      have hh := mul_le_mul_of_nonneg_right (Ht δ hδ hδt)
        (Real.rpow_nonneg hδ.le (5 * ν))
      nlinarith [Real.rpow_pos_of_pos hδ (5 * ν)]
    exact (not_lt_of_ge (hlower.trans hden) hsmall).elim
  obtain ⟨H₂, hH₂, hnormal, hC₂, hB₂, hG₂⟩ := hnarrow
  refine Or.inr ⟨ε,
    (fun i => (Z i ∩ assignedFiber γ H₁ (f i)) ∩ assignedFiber γ H₂ (f i)), H₂,
    by linarith, le_rfl, fun _ => inter_subset_left.trans inter_subset_left,
    fun j => (hH₂ j).2.1.trans ((hH₁ j).2.trans inter_subset_left), hC₂, hB₂, hG₂, ?_⟩
  intro i j p hi hj
  exact Or.inr (by rw [hscale]; exact hnormal i j p hi hj)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
