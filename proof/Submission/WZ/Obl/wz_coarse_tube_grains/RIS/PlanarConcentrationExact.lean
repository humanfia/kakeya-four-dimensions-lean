-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PlanarConcentrationExact.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PlanarConcentrationPower
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.SlabNarrowing

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

/-- Broadness and near-minimal union volume give planar concentration at the
actual tube radius, with arbitrarily small power loss in the original mass. -/
theorem planar_concentration_tube_scale {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
        (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
        (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
        ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i) →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (1 - η)) →
        (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ 1 →
          ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s}.ncard : ℝ) ≤
            (δ ^ (-η) * s ^ β) * incidence Y p) →
        ∃ (e : Space) (t : ℝ) (F : Finset (Fin n)), ‖e‖ = 1 ∧
          (∀ i ∈ F, Tube δ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ 2 * δ}) ∧
          ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i ∈ F, volume (Y i) := by
  let τ := min (ε / 16) (1 / 4)
  have hτ : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτε : τ ≤ ε / 16 := min_le_left _ _
  have hτ1 : τ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨η, hη, hη1, d₁, hd₁, hplane⟩ := planar_concentration_power hτ hβ
  obtain ⟨d₂, hd₂, hcut₂⟩ := exists_power_cutoff (a := 1 - τ) (by linarith)
    (c := 1 / 4) (by norm_num)
  obtain ⟨d₃, hd₃, hcut₃⟩ := exists_power_cutoff (a := ε - 7 * τ) (by linarith)
    (c := 1 / 100 ^ 6) (by norm_num)
  refine ⟨η, hη, hη1, min d₁ (min d₂ d₃), lt_min hd₁ (lt_min hd₂ hd₃), ?_⟩
  intro δ hδ hδ100 hδd n x v Y hn hv hT hY hYT hdense hvol hbroad
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨e, t, F, he, hslab, hkeep⟩ := hplane δ hδ hδ100
    (hδd.trans (min_le_left _ _)) n x v Y hn hv hT hY hYT hdense hvol hbroad
  have hwidth := hcut₂ δ hδ (hδd.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc := hcut₃ δ hδ (hδd.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let w := δ ^ (1 - τ)
  have hδw : δ ≤ w := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hw : w < 1 / 2 := by dsimp [w]; linarith
  obtain ⟨u, s, G, hGF, hu, hGslab, hGmass⟩ := narrow_slab_weighted hδ hδw hw x v
    (fun i => (volume (Y i)).toReal) F he (fun _ _ => ENNReal.toReal_nonneg)
    (fun i _ => hv i) (fun i _ => hT i) hslab
  have hratio : w / δ = δ ^ (-τ) := by
    dsimp [w]
    rw [show 1 - τ = -τ + 1 by ring, Real.rpow_add hδ, Real.rpow_one,
      mul_div_cancel_right₀ _ hδ.ne']
  have hCpow : (100 * w / δ) ^ 6 = 100 ^ 6 * δ ^ (-6 * τ) := by
    rw [mul_div_assoc, mul_pow, hratio, ← Real.rpow_natCast (δ ^ (-τ)),
      ← Real.rpow_mul hδ.le]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  have hC : 0 < (100 * w / δ) ^ 6 := by dsimp [w]; positivity
  have hcoef : (100 * w / δ) ^ 6 * δ ^ ε ≤ δ ^ τ := by
    rw [hCpow]
    have heq : δ ^ (-6 * τ) * δ ^ ε = δ ^ (ε - 7 * τ) * δ ^ τ := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1
      ring
    calc
      _ = (100 ^ 6 * δ ^ (ε - 7 * τ)) * δ ^ τ := by rw [mul_assoc, heq]; ring
      _ ≤ 1 * δ ^ τ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hδ.le _)
        nlinarith only [hc]
      _ = _ := one_mul _
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono ((hYT i).trans (hT i)))
  have hFfin : (∑ i ∈ F, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  have hGfin : (∑ i ∈ G, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  have hYsumfin : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  have hkeepR : δ ^ τ * shadingMass Y ≤ ∑ i ∈ F, (volume (Y i)).toReal := by
    have hh := ENNReal.toReal_mono hFfin hkeep
    simpa only [shadingMass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
      ENNReal.toReal_sum (fun i _ => hYfin i)] using hh
  have hfinal : δ ^ ε * shadingMass Y ≤ ∑ i ∈ G, (volume (Y i)).toReal := by
    apply (mul_le_mul_iff_right₀ hC).mp
    calc
      _ = ((100 * w / δ) ^ 6 * δ ^ ε) * shadingMass Y := by ring
      _ ≤ δ ^ τ * shadingMass Y := mul_le_mul_of_nonneg_right hcoef
        (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      _ ≤ _ := hkeepR
      _ ≤ _ := hGmass
  refine ⟨u, s, G, hu, hGslab, ?_⟩
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYsumfin) hGfin).mp
  simpa only [shadingMass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
    ENNReal.toReal_sum (fun i _ => hYfin i)] using hfinal

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
