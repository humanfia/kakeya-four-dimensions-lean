-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.Regularize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Incidence

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

theorem exists_power_cutoff {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ^ a ≤ c := by
  refine ⟨c ^ (1 / a), Real.rpow_pos_of_pos hc _, ?_⟩
  intro δ hδ hδd
  calc
    δ ^ a ≤ (c ^ (1 / a)) ^ a := Real.rpow_le_rpow hδ.le hδd ha.le
    _ = c := by rw [← Real.rpow_mul hc.le, one_div_mul_cancel ha.ne', Real.rpow_one]

/-- A near-extremal family can be refined, without changing its tubes, so that
all nonzero pointwise multiplicities have the extremal exponent. -/
theorem uniform_incidence_refinement {σ : ℝ}
    (habove : ∀ t : ℝ, σ < t → ¬ Examples t) (ε : ℝ) (hε : 0 < ε) :
    ∃ η d : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → Separated η δ n x v →
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
      ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧ Family ε δ n x v Z ∧
        Separated ε δ n x v ∧ shadingMass Y / 2 ≤ shadingMass Z ∧
        volume (⋃ i, Z i) ≤ ENNReal.ofReal (δ ^ (σ - ε)) ∧
        (∀ p, incidence Z p ≤ (n : ℝ) * δ ^ (2 - σ - ε)) ∧
        (∀ p ∈ ⋃ i, Z i, (n : ℝ) * δ ^ (2 - σ + ε) < incidence Z p) := by
  obtain ⟨θ, d0, hθ, hd0, hlow⟩ :=
    (not_examples_iff (σ + ε / 2)).mp (habove _ (by linarith))
  let η := min (ε / 4) (θ / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : 4 * η ≤ ε := by have := min_le_left (ε / 4) (θ / 2); dsimp [η]; linarith
  have hηθ : 2 * η ≤ θ := by have := min_le_right (ε / 4) (θ / 2); dsimp [η]; linarith
  obtain ⟨d1, hd1, hpower1⟩ := exists_power_cutoff hη (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨d2, hd2, hpower2⟩ :=
    exists_power_cutoff (by positivity : 0 < ε / 2) (by norm_num : (0 : ℝ) < 1 / 384)
  refine ⟨η, min d0 (min d1 d2), hη, by linarith, lt_min hd0 (lt_min hd1 hd2), ?_⟩
  intro δ hδ hδd hδmax n x v Y hH hS hV
  have hδ1 : δ ≤ 1 := by linarith
  have hδ0 : δ ≤ d0 := hδd.trans (min_le_left _ _)
  have hδd1 : δ ≤ d1 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd2 : δ ≤ d2 := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp1 := hpower1 δ hδ hδd1
  have hp2 := hpower2 δ hδ hδd2
  have hn : (0 : ℝ) < n := by exact_mod_cast hH.1
  have hSθ := hS.mono_error hδ hδ1 (by linarith : η ≤ θ)
  have hglobal : ∀ Z : Fin n → Set Space, Family θ δ n x v Z →
      ENNReal.ofReal (δ ^ (σ + ε / 2)) < volume (⋃ i, Z i) :=
    fun Z hZ => hlow δ hδ hδ0 hδmax n x v Z hZ hSθ
  let M : ℝ := (n : ℝ) * δ ^ (2 - σ - ε)
  have hM : 0 < M := by dsimp [M]; positivity
  have hcap : shadingMass Y ≤ M * δ ^ (σ + ε / 2) := by
    apply (hH.mass_upper hδ hδ1).trans
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hδ (ε / 2))).mp
    have heq : (M * δ ^ (σ + ε / 2)) * δ ^ (ε / 2) = (n : ℝ) * δ ^ 2 := by
      dsimp [M]
      rw [mul_assoc (n : ℝ), mul_assoc (n : ℝ), ← Real.rpow_add hδ,
        ← Real.rpow_add hδ]
      have he : 2 - σ - ε + (σ + ε / 2) + ε / 2 = (2 : ℝ) := by ring
      rw [he, Real.rpow_two]
    rw [heq]
    have hcoef : 384 * δ ^ (ε / 2) ≤ 1 := by linarith
    nlinarith [mul_nonneg (mul_nonneg hn.le (sq_nonneg δ)) (sub_nonneg.mpr hcoef)]
  obtain ⟨Y1, hY1Y, hY1m, hY1mass, hY1upper⟩ :=
    hH.trim_high_incidence hM hcap hglobal
  have hY1U : (⋃ i, Y1 i) ⊆ ⋃ i, Y i := iUnion_mono hY1Y
  have hY1fin : volume (⋃ i, Y1 i) ≠ ∞ :=
    ne_top_of_le_ne_top hH.volume_union_ne_top (measure_mono hY1U)
  let L : ℝ := (n : ℝ) * δ ^ (2 - σ + ε)
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨Z, hZY1, hZm, hZmass, hZupper, hZlower⟩ :=
    trim_low_incidence hY1m hY1fin hL.le hM.le hY1upper
  have hZY : ∀ i, Z i ⊆ Y i := fun i => (hZY1 i).trans (hY1Y i)
  have hY1vol : (volume (⋃ i, Y1 i)).toReal ≤ δ ^ (σ - η) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hY1U).trans hV)
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _)] at h
  have hpow : ∀ a : ℝ, 2 * η ≤ a → δ ^ a ≤ δ ^ η / 4 := by
    intro a ha
    calc
      δ ^ a ≤ δ ^ (2 * η) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ha
      _ = δ ^ η * δ ^ η := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ η * (1 / 4) := mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ = _ := by ring
  have hhighloss : δ ^ θ * (n : ℝ) * δ ^ 2 ≤
      (δ ^ η * (n : ℝ) * δ ^ 2) / 4 := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpow θ hηθ) hn.le) (sq_nonneg δ)
    nlinarith only [h]
  have hlowloss : L * (volume (⋃ i, Y1 i)).toReal ≤
      (δ ^ η * (n : ℝ) * δ ^ 2) / 4 := by
    apply (mul_le_mul_of_nonneg_left hY1vol hL.le).trans
    have heq : L * δ ^ (σ - η) = δ ^ (ε - η) * (n : ℝ) * δ ^ 2 := by
      dsimp [L]
      calc
        _ = (n : ℝ) * δ ^ ((2 - σ + ε) + (σ - η)) := by
          rw [Real.rpow_add hδ (2 - σ + ε) (σ - η)]; ring
        _ = (n : ℝ) * δ ^ ((ε - η) + 2) := by congr 2; ring
        _ = _ := by rw [Real.rpow_add hδ (ε - η) 2, Real.rpow_two]; ring
    rw [heq]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpow (ε - η) (by linarith)) hn.le) (sq_nonneg δ)
    nlinarith only [h]
  have hHmass := hH.mass_lower hδ
  have hretained : shadingMass Y / 2 ≤ shadingMass Z := by linarith
  have hnewmass : δ ^ ε * (n : ℝ) * δ ^ 2 ≤ shadingMass Z := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpow ε (by linarith)) hn.le) (sq_nonneg δ)
    have hbase : 0 ≤ δ ^ η * (n : ℝ) * δ ^ 2 := by positivity
    linarith
  refine ⟨Z, hZY, hH.of_subsets_mass hZY hZm hnewmass,
    hS.mono_error hδ hδ1 (by linarith), hretained, ?_, hZupper, hZlower⟩
  apply ((measure_mono (iUnion_mono hZY)).trans hV).trans
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : σ - ε ≤ σ - η))

/-- Both exponent hypotheses yield arbitrarily small examples with uniform incidence bounds. -/
theorem incidence_extremal_examples {σ : ℝ}
    (hbelow : ∀ t : ℝ, t < σ → Examples t)
    (habove : ∀ t : ℝ, σ < t → ¬ Examples t)
    (ε d0 : ℝ) (hε : 0 < ε) (hd0 : 0 < d0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
      ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family ε δ n x v Y ∧ Separated ε δ n x v ∧
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - ε)) ∧
        (∀ p, incidence Y p ≤ (n : ℝ) * δ ^ (2 - σ - ε)) ∧
        (∀ p ∈ ⋃ i, Y i, (n : ℝ) * δ ^ (2 - σ + ε) < incidence Y p) := by
  obtain ⟨η, d, hη, hηε, hd, href⟩ := uniform_incidence_refinement habove ε hε
  obtain ⟨δ, hδ, hδ0, hδmax, n, x, v, Y, hH, hS, hV⟩ :=
    hbelow (σ - η) (by linarith) η (min d0 d) hη (lt_min hd0 hd)
  obtain ⟨Z, hZY, hHZ, hSZ, hmass, hVZ, hupper, hlower⟩ :=
    href δ hδ (hδ0.trans (min_le_right _ _)) hδmax n x v Y hH hS hV
  exact ⟨δ, hδ, hδ0.trans (min_le_left _ _), hδmax, n, x, v, Z,
    hHZ, hSZ, hVZ, hupper, hlower⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
