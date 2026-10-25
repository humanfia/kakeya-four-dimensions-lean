-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PlanarConcentrationPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PlanarConcentration
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Regularize

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

set_option maxHeartbeats 800000 in
/-- Power-scale broadness and near-minimal union volume force a subfamily of
full tubes into one thin slab, with arbitrarily small power loss of mass. -/
theorem planar_concentration_power {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
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
          (∀ i ∈ F, Tube δ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ δ ^ (1 - ε)}) ∧
          ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i ∈ F, volume (Y i) := by
  obtain ⟨a, ha, ha1, hnumeric⟩ := planar_concentration_numeric
  let R := 2 + 2 / β
  let G := 4 + 2 / β
  let B := (G + 2) / β
  let K := B + 3 * G + 1
  let J := K + R + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hJ1 : 1 < J := by dsimp [J]; linarith
  let η := min ε 1 / (4 * J)
  have hη : 0 < η := by dsimp [η]; positivity
  have hJη : J * η = min ε 1 / 4 := by dsimp [η]; field_simp
  have hJηε : J * η ≤ ε / 4 := by rw [hJη]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hJη1 : J * η ≤ 1 / 4 := by rw [hJη]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hη1 : η ≤ 1 := by nlinarith
  have hKJ : K < J := by dsimp [J]; linarith
  have hRJ : R < J := by dsimp [J]; linarith
  have hBJ : B < J := by dsimp [J, K]; linarith
  have hRη1 : R * η ≤ 1 := by nlinarith
  have hBη1 : B * η ≤ 1 := by nlinarith
  have hKηε : K * η < ε := by nlinarith
  have hRηε : R * η < ε := by nlinarith
  have h0η1 : 2 * η / β ≤ 1 := by
    have he : R * η = 2 * η + 2 * η / β := by dsimp [R]; ring
    linarith
  obtain ⟨d₁, hd₁, hcut₁⟩ := exists_power_cutoff hη
    (c := min (1 / 2) (min (a / 4352) (a ^ 2 / 6144))) (by positivity)
  obtain ⟨d₂, hd₂, hcut₂⟩ := exists_power_cutoff (sub_pos.mpr hKηε)
    (c := a ^ 6 / 1610612736) (by positivity)
  obtain ⟨d₃, hd₃, hcut₃⟩ := exists_power_cutoff (sub_pos.mpr hRηε)
    (c := 1 / 15) (by norm_num)
  refine ⟨η, hη, hη1, min d₁ (min d₂ d₃), lt_min hd₁ (lt_min hd₂ hd₃), ?_⟩
  intro δ hδ hδ100 hδd n x v Y hn hv hT hY hYT hdense hvol hbroad
  have hδ1 : δ ≤ 1 := by linarith
  have hc₁ := hcut₁ δ hδ (hδd.trans (min_le_left _ _))
  have hc₂ := hcut₂ δ hδ (hδd.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc₃ := hcut₃ δ hδ (hδd.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hc_half : δ ^ η ≤ (1 / 2 : ℝ) := hc₁.trans (min_le_left _ _)
  have hc_stem : δ ^ η ≤ a / 4352 := hc₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc_broad : δ ^ η ≤ a ^ 2 / 6144 := hc₁.trans ((min_le_right _ _).trans (min_le_right _ _))
  let b₀ := δ ^ (2 * η / β)
  let b₁ := δ ^ (B * η)
  let lam := δ ^ η
  let U := δ ^ (-η)
  let r := δ ^ (R * η)
  have hb₀ : 0 < b₀ := by dsimp [b₀]; positivity
  have hb₁ : 0 < b₁ := by dsimp [b₁]; positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hb₀1 : b₀ ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hb₁1 : b₁ ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hlam1 : lam ≤ 1 := Real.rpow_le_one hδ.le hδ1 hη.le
  have hr1 : r ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hδb₀ : δ ≤ b₀ := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 h0η1
  have hδb₁ : δ ≤ b₁ := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hBη1
  have hδr : δ ≤ r := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hRη1
  have hratio : r / b₀ = δ ^ (2 * η) := by
    dsimp [r, b₀]
    rw [← Real.rpow_sub hδ]
    congr 1
    dsimp [R]
    ring
  have hpow2 : δ ^ (2 * η) = lam ^ 2 := by
    dsimp [lam]
    rw [← Real.rpow_natCast (δ ^ η), ← Real.rpow_mul hδ.le]
    congr 1
    norm_num
    ring
  have hbudget : 128 * (8 * (δ + r) / b₀ + δ) ≤ a * lam / 2 := by
    have hδratio : δ ≤ r / b₀ := by
      apply (le_div_iff₀ hb₀).mpr
      exact (mul_le_mul_of_nonneg_left hb₀1 hδ.le).trans (by simpa using hδr)
    calc
      _ ≤ 128 * (8 * (r + r) / b₀ + r / b₀) := by gcongr
      _ = 2176 * lam ^ 2 := by rw [show 128 * (8 * (r + r) / b₀ + r / b₀) = 2176 * (r / b₀) by ring, hratio, hpow2]
      _ ≤ _ := by dsimp [lam] at *; nlinarith [mul_le_mul_of_nonneg_right hc_stem hlam.le]
  have hLpow : a ^ 2 * b₀ * lam ^ 3 / (4 * U) =
      (a ^ 2 / 4) * δ ^ (G * η) := by
    dsimp [b₀, lam, U]
    rw [← Real.rpow_natCast (δ ^ η), ← Real.rpow_mul hδ.le]
    norm_num only [Nat.cast_ofNat]
    have he : a ^ 2 * δ ^ (2 * η / β) * δ ^ (η * (3 : ℝ)) / (4 * δ ^ (-η)) =
        a ^ 2 / 4 * (δ ^ (2 * η / β) * δ ^ (η * (3 : ℝ)) / δ ^ (-η)) := by ring
    rw [he, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
    congr 2
    dsimp [G]
    ring
  have hcap₀ : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b₀}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ) := by
    intro p u hu
    rw [← incidence_eq_ncard]
    have he : δ ^ (-η) * b₀ ^ β = lam := by
      dsimp [b₀, lam]
      rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
      congr 1
      field_simp
      ring
    calc
      _ ≤ (δ ^ (-η) * b₀ ^ β) * incidence Y p := hbroad p u b₀ hu hδb₀ hb₀1
      _ = lam * incidence Y p := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc_half (incidence_nonneg Y p)
  have hcap₁ : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b₁}.ncard : ℝ) ≤
        (a ^ 2 * b₀ * lam ^ 3 / (4 * U) / 1536) * incidence Y p := by
    intro p u hu
    have he : δ ^ (-η) * b₁ ^ β = δ ^ η * δ ^ (G * η) := by
      dsimp [b₁]
      rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1
      dsimp [B]
      field_simp
      ring
    calc
      _ ≤ (δ ^ (-η) * b₁ ^ β) * incidence Y p := hbroad p u b₁ hu hδb₁ hb₁1
      _ = (δ ^ η * δ ^ (G * η)) * incidence Y p := by rw [he]
      _ ≤ (a ^ 2 / 6144 * δ ^ (G * η)) * incidence Y p :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc_broad (Real.rpow_nonneg hδ.le _)) (incidence_nonneg Y p)
      _ = _ := by rw [hLpow]; ring
  have hvol' : volume (⋃ i, Y i) ≤ ENNReal.ofReal (U * δ) := by
    have he : U * δ = δ ^ (1 - η) := by
      rw [show 1 - η = -η + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
    simpa only [he] using hvol
  obtain ⟨e, t, F, he, hslab, hmass⟩ := hnumeric b₀ b₁ δ lam U r
    hb₀ hb₀1 hb₁ hb₁1 hδ hδ100 hlam hlam1 hU hr hr1 hbudget n x v Y
    hn hv hT hY hYT hdense hvol' hcap₀ hcap₁
  have hwidth : 15 * δ / r ≤ δ ^ (1 - ε) := by
    apply (div_le_iff₀ hr).mpr
    have he : δ ^ (1 - ε) * r = δ / δ ^ (ε - R * η) := by
      dsimp [r]
      rw [← Real.rpow_add hδ, show 1 - ε + R * η = 1 - (ε - R * η) by ring,
        Real.rpow_sub hδ, Real.rpow_one]
    rw [he]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc₃ hδ.le]
  have hcoefficient : δ ^ ε ≤
      b₁ * (a ^ 2 * b₀ * lam ^ 3 / (4 * U)) ^ 3 / (25165824 * U) := by
    have he : b₁ * (a ^ 2 * b₀ * lam ^ 3 / (4 * U)) ^ 3 / (25165824 * U) =
        (a ^ 6 / 1610612736) * δ ^ (K * η) := by
      rw [hLpow, mul_pow]
      dsimp [b₁, U]
      rw [← Real.rpow_natCast (δ ^ (G * η)), ← Real.rpow_mul hδ.le]
      norm_num only [Nat.cast_ofNat]
      have hh : δ ^ (B * η) * ((a ^ 2 / 4) ^ 3 * δ ^ (G * η * (3 : ℝ))) /
          (25165824 * δ ^ (-η)) = a ^ 6 / 1610612736 *
          (δ ^ (B * η) * δ ^ (G * η * (3 : ℝ)) / δ ^ (-η)) := by ring
      rw [hh, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
      congr 2
      dsimp [K]
      ring
    rw [he]
    calc
      δ ^ ε = δ ^ (ε - K * η) * δ ^ (K * η) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc₂ (Real.rpow_nonneg hδ.le _)
  refine ⟨e, t, F, he, fun i hi p hp => (hslab i hi hp).trans hwidth, ?_⟩
  exact (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcoefficient) (by positivity)).trans hmass

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
