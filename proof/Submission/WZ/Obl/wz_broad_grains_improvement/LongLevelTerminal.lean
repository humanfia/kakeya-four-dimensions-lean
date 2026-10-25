-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.LongLevelTerminal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.LargeLevelPower

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory

/-- Positive retained mass forces the common fibre level to be at least one half. -/
theorem half_le_grain_level
    {δ h ρ a c b g m mK l : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {G : Fin L → Set V} {γ : Fin L → Fin N} {B : Prop}
    (hδ : 0 < δ) (hA : A δ h mK l n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f B)
    (hH : HB δ h n x v S Z ρ N y w f a c b g L z e G γ m) :
    1 / 2 ≤ m := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
  have hmassY : 0 < ∑ i, μ (Y i) :=
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < δ ^ h * n * δ ^ 2)).trans_le
      hA.2.2.2.1
  have hmassZ : 0 < ∑ i, μ (Z i) :=
    (by positivity : 0 < O (δ ^ h) * ∑ i, μ (Y i)).trans_le
      (hC.2.1.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ S)))
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
    (f := fun _ => (0 : ENNReal)) (g := fun i => μ (Z i)) (by simpa using hmassZ)
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hi.ne'
  have hiS : i ∈ S := by
    by_contra hnot
    simp [(hC.1 i).2.2 hnot] at hp
  have hlevel := hH.2.2.2.2.2.2.2.2.1 (f i) p ⟨i, hiS, rfl, hp⟩
  have hone : (1 : ℝ) ≤ q n {j | j ∈ S ∧ f j = f i ∧ p ∈ Z j} := by
    have hc : 0 < ({j | j ∈ S ∧ f j = f i ∧ p ∈ Z j} : Set (Fin n)).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨i, hiS, rfl, hp⟩
    exact_mod_cast hc
  linarith [hlevel.2]

/-- Once both geometric stopping conditions hold, grains longer than this
fixed power already satisfy the local-count stop after dense pruning. -/
theorem stage_three_of_long_grain_length
    {ω ζ ε : ℝ} (hω : 0 < ω) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ {δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < δ → δ ≤ d₀ → h ≤ η →
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      J ω ζ δ h ρ c n x v Y 2 →
      δ ^ (ζ / 8) ≤ c → J ω ζ δ ε ρ c n x v Y 3 := by
  obtain ⟨d₁, hd₁, hd₁small, H⟩ := stage_three_of_power_large_grain_level hω hζ hε
  obtain ⟨d₂, hd₂, hsmall⟩ := wz_coarse_tube_grains.exists_small_mul_rpow
    (C := 2) (a := ζ / 4) (by norm_num) (by positivity)
  let η := min (ε / 2) (ζ / 8)
  refine ⟨η, min d₁ d₂, by dsimp [η]; positivity,
    (min_le_left _ _).trans (by linarith), by positivity,
    (min_le_left _ _).trans hd₁small, ?_⟩
  intro δ h ρ c n x v Y hδ hδd hh hA hJ hc
  obtain ⟨S, Z, N, y, w, f, a, g, hC, hρlow, hg, hbr, hH, hstop⟩ := hJ
  obtain ⟨L, z, e, G, γ, m, hHB⟩ := H_iff.mp hH
  have hm := half_le_grain_level hδ hA hC hHB
  have hp : 0 < δ ^ (ζ / 8) := Real.rpow_pos_of_pos hδ _
  have hc2 : δ ^ (ζ / 4) ≤ c ^ 2 := by
    calc
      _ = δ ^ (ζ / 8) * δ ^ (ζ / 8) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ c * c := mul_le_mul hc hc hp.le (hp.le.trans hc)
      _ = c ^ 2 := by ring
  have hs : δ ^ (ζ / 4) ≤ 1 / 2 := by
    linarith [hsmall δ hδ (hδd.trans (min_le_right _ _))]
  have hlarge : δ ^ (ζ / 2) ≤ m * c ^ 2 := by
    calc
      _ = δ ^ (ζ / 4) * δ ^ (ζ / 4) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ (1 / 2) * δ ^ (ζ / 4) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ m * c ^ 2 := mul_le_mul hm hc2 (by positivity) (by linarith)
  exact H hδ (hδd.trans (min_le_left _ _))
    (hh.trans (min_le_left _ _)) (hh.trans (min_le_right _ _))
    hA hC hHB hρlow (hstop.2.1 (by decide)) (hstop.1 (by decide)) hbr hlarge

end WangZahlLot.Obl.wz_broad_grains_improvement
