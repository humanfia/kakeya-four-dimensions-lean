-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.Main.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.Post
import Submission.WZ.Obl.wz_coarse_tube_grains.X48.BroadCount
import Submission.WZ.Obl.wz_coarse_tube_grains.Numeric

/-!
# The single-tube grains theorem for a fibre indexed by `Fin m`

Chaining: carrier selection (`carrier_selection`), prisms in the thin carrier
(`prism_in_carrier`), and the frozen grains (`grains_of_family`). The Córdoba count of
x0448 (`X48.card_lower_power_broad`) bounds the prescribed length `c` by a power of `δ`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains

open Set Metric MeasureTheory
open scoped Classical

local notation "V" => LeanEval.Analysis.WangZahlKakeya.Space

theorem exists_small_mul_rpow {C a : ℝ} (hC : 0 < C) (ha : 0 < a) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C * δ ^ a ≤ 1 := by
  obtain ⟨d, hd, h⟩ := exists_small_rpow ha (by positivity : (0 : ℝ) < 1 / C)
  refine ⟨d, hd, fun δ hδ hδd => ?_⟩
  have := h δ hδ hδd
  rw [le_div_iff₀ hC] at this
  linarith

/-- `δ^a ≤ δ^b` for `b ≤ a` and `0 < δ ≤ 1`. -/
theorem rpow_le_of_le {δ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hab : b ≤ a) :
    δ ^ a ≤ δ ^ b :=
  Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hab

set_option maxHeartbeats 3200000 in
theorem tube_grains_fin {β τ₀ ε C₀ : ℝ} (hβ : 0 < β) (hτ₀ : 0 < τ₀) (hε : 0 < ε)
    (hC₀ : 0 < C₀) :
    ∃ η d₀ : ℝ, 0 < η ∧ 0 < d₀ ∧ ∀ δ ρ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ ρ → ρ ≤ 1 →
    ∀ (m : ℕ) (x v : Fin m → V) (Z : Fin m → Set V) (y w : V), 0 < m → ‖w‖ = 1 →
    (∀ i, ‖v i‖ = 1 ∧ Tb δ (x i) (v i) ⊆ Tb (ρ / 2) y w ∧ MeasurableSet (Z i) ∧
      Z i ⊆ Tb δ (x i) (v i)) →
    (m : ℝ) * δ ^ 6 ≤ C₀ →
    ENNReal.ofReal (δ ^ η * m * δ ^ 2) ≤ ∑ i, volume (Z i) →
    (∀ (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      (({i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : Set (Fin m)).ncard : ℝ) ≤
        δ ^ (-η) * (r / ρ) ^ β * (({i | p ∈ Z i} : Set (Fin m)).ncard : ℝ)) →
    ∀ c : ℝ, δ ^ (1 - τ₀) / ρ ≤ c → c ≤ δ ^ ε * (ρ / δ) / m →
    ∃ (Z' : Fin m → Set V) (mm : ℝ) (L : ℕ) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V)
      (G : Fin L → Set V),
      (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i) ∧
      ENNReal.ofReal (δ ^ ε) * ∑ i, volume (Z i) ≤ ∑ i, volume (Z' i) ∧
      (∀ (p u : V) (s : ℝ), ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        (({i | p ∈ Z' i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s} : Set (Fin m)).ncard : ℝ) ≤
          δ ^ (-ε) * (s / ρ) ^ β * (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ)) ∧
      (∀ p, (∃ i, p ∈ Z' i) →
        (({i | p ∈ Z' i} : Set (Fin m)).ncard : ℝ) ∈ Set.Icc mm (2 * mm)) ∧
      (∀ j, MeasurableSet (G j) ∧ G j ⊆ Geom.box (16 * δ) (ρ * c) c (z j) (e j) ∧
        Geom.box (16 * δ) (ρ * c) c (z j) (e j) ⊆ Tb ρ y w ∧
        e j w 0 ^ 2 + e j w 1 ^ 2 ≤ (10 * ρ) ^ 2) ∧
      (∀ j j', j ≠ j' → Disjoint (G j) (G j')) ∧
      {p | ∃ j, p ∈ G j} = {p | ∃ i, p ∈ Z' i} ∧
      ENNReal.ofReal (δ ^ ε * L * (16 * δ) * (ρ * c) * c) ≤ ∑ j, volume (G j) ∧
      ∀ i j, (Z' i ∩ G j).Nonempty →
        Z' i ∩ Geom.box (16 * δ) (ρ * c) c (z j) (e j) ⊆ G j ∧
        (∀ p ∈ Tb δ (x i) (v i) ∩ frontier (Geom.box (16 * δ) (ρ * c) c (z j) (e j)),
          |e j (p - z j) 2| = c / 2) ∧
        ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
          ∃ p ∈ Tb δ (x i) (v i) ∩ Geom.box (16 * δ) (ρ * c) c (z j) (e j),
            e j (p - z j) 2 = t := by
  -- a capped `τ`
  set τ : ℝ := min τ₀ 1 with hτ_def
  have hτ : 0 < τ := lt_min hτ₀ one_pos
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hττ₀ : τ ≤ τ₀ := min_le_left _ _
  set ζ : ℝ := ε / 4 with hζ_def
  have hζ : 0 < ζ := by positivity
  set D : ℝ := 16 / τ with hD_def
  have hD : 0 < D := by positivity
  have hτD : τ * D = 16 := by rw [hD_def]; field_simp
  obtain ⟨ηx, hηx, hηx1, hηxζ, dx, hdx, Kx, hKx, hprism⟩ := prism_in_carrier hζ hβ hD
  obtain ⟨K₁, hK₁, hsel⟩ := carrier_selection
  have hK₁r : (1 : ℝ) ≤ K₁ := by exact_mod_cast hK₁
  set ν : ℝ := τ * ηx / 32 with hν_def
  have hν : 0 < ν := by positivity
  obtain ⟨dl, hdl, hlog⟩ := RIS.logarithmic_count_power (D := 7) (ν := ν) (by norm_num) hν
  set η : ℝ := min (ε * β / (4 * (β + 2))) (τ * ηx / 64) with hη_def
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : η + 2 * η / β ≤ ε / 4 := by
    have h1 : η ≤ ε * β / (4 * (β + 2)) := min_le_left _ _
    have h2 : η + 2 * η / β = η * (β + 2) / β := by field_simp
    rw [h2, div_le_iff₀ hβ]
    calc η * (β + 2) ≤ ε * β / (4 * (β + 2)) * (β + 2) := by gcongr
      _ = ε / 4 * β := by field_simp
  have hητ : η ≤ τ * ηx / 64 := min_le_right _ _
  -- smallness of `δ`
  obtain ⟨d1, hd1, s1⟩ := exists_small_mul_rpow (C := 16384) (by norm_num) (by positivity :
    0 < 3 * ε / 4)
  obtain ⟨d2, hd2, s2⟩ := exists_small_mul_rpow (C := 2097152) (by norm_num) hτ
  obtain ⟨d3, hd3, s3⟩ := exists_small_mul_rpow (C := 10486 / dx) (by positivity) hτ
  obtain ⟨d4, hd4, s4⟩ := exists_small_mul_rpow (C := 2560 * 4096) (by norm_num)
    (by positivity : 0 < 7 * ε / 10)
  obtain ⟨d5, hd5, s5⟩ := exists_small_mul_rpow (C := C₀ * 10486 ^ D) (by positivity)
    (by norm_num : (0 : ℝ) < 10)
  obtain ⟨d6, hd6, s6⟩ := exists_small_mul_rpow (C := 256) (by norm_num)
    (by positivity : 0 < 19 * ε / 20)
  obtain ⟨d7, hd7, s7⟩ := exists_small_mul_rpow (C := 10486 * K₁ ^ 2) (by positivity)
    (by positivity : 0 < 13 * τ * ηx / 64)
  obtain ⟨d8, hd8, s8⟩ := exists_small_mul_rpow (C := 10486 * K₁) (by positivity)
    (by positivity : 0 < 63 * τ * ηx / 64)
  obtain ⟨d9, hd9, s9⟩ := exists_small_mul_rpow (C := 4 * K₁ ^ 2 * Kx) (by positivity)
    (by positivity : 0 < ε / 5)
  set d₀ : ℝ := min (min (min (min d1 d2) (min d3 d4)) (min (min d5 d6) (min d7 d8)))
    (min (min d9 dl) (min (1 / 2) (1 / C₀))) with hd₀_def
  refine ⟨η, d₀, hη, by positivity, ?_⟩
  intro δ ρ hδ hδd hδρ hρ1 m x v Z y w hm hw hZ hmδ hdens hbroad c hc1 hc2
  simp only [hd₀_def, le_min_iff] at hδd
  obtain ⟨⟨⟨⟨hδ1, hδ2⟩, hδ3, hδ4⟩, ⟨hδ5, hδ6⟩, hδ7, hδ8⟩, ⟨hδ9, hδl⟩, hδh, hδ80⟩ := hδd
  have hδ1' : δ < 1 := lt_of_le_of_lt hδh (by norm_num)
  have hδle1 : δ ≤ 1 := hδ1'.le
  have hρ : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- Córdoba count
  have hcord : δ ^ (η + 2 * η / β) * ρ ≤ 4096 * m * δ := by
    have h := X48.card_lower_power_broad (S := Finset.univ) (Y := Z) (x := x) (v := v) hδ hδ1'
      hρ hρ1 hβ hη ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i _ => (hZ i).1)
      (fun i _ => (hZ i).2.2.2) (by simpa using hdens) (by simpa using hbroad)
    simpa using h
  have hc1' : δ ^ (1 - τ) / ρ ≤ c :=
    le_trans (div_le_div_of_nonneg_right (Num.rpow_le_of_le hδ hδle1 (by linarith)) hρ.le) hc1
  obtain ⟨hcpos, hc_pow, hc4, hδρτ, h512, hP3⟩ :=
    Num.c_facts hδ hδle1 hρ hm1 hηε hε hcord hc1' hc2 (s1 δ hδ hδ1) (s2 δ hδ hδ2)
  -- the carrier selection
  obtain ⟨k, Y, y', w', hw', hww, hseg, hY, hYcar, hmassY, hlev, hfrac⟩ :=
    hsel δ ρ hδ h512 m x v Z y w hw hZ
  -- the normalized radius of the thin carrier
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℝ, ξ = δ / (100 * (ρ / 256)) := ⟨_, rfl⟩
  obtain ⟨hξ0, hξup, hξlow⟩ := Num.xi_facts hδ hρ hρ1 hξdef hδρτ
  have hP4 : ξ ≤ dx := by
    have h := s3 δ hδ hδ3
    rw [div_mul_eq_mul_div, div_le_one hdx] at h
    linarith
  have hP5 := Num.P5_fact hδ hξlow hζ_def hε hc_pow (s4 δ hδ hδ4)
  have hP6 := Num.P6_fact hδ hξ0 hξup hτD hD (Nat.cast_nonneg m) hmδ (s5 δ hδ hδ5)
  have hP7 := Num.P7_fact hδ hρ (by positivity) hξlow hζ_def hε hc2 (s6 δ hδ hδ6)
  -- logarithmic loss
  have hm7 : (m : ℝ) ≤ δ ^ (-(7 : ℝ)) := by
    have h80 : C₀ * δ ≤ 1 := by
      rw [le_div_iff₀ hC₀] at hδ80
      linarith
    rw [Real.rpow_neg hδ.le, show ((7 : ℝ)) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← one_div, le_div_iff₀ (by positivity)]
    calc (m : ℝ) * δ ^ 7 = m * δ ^ 6 * δ := by ring
      _ ≤ C₀ * δ := by gcongr
      _ ≤ 1 := h80
  have hlogm := hlog δ hδ hδl m hm7
  obtain ⟨lg, hlg_def⟩ : ∃ lg : ℝ, lg = (Nat.log 2 m : ℝ) + 1 := ⟨_, rfl⟩
  have hlg0 : 0 ≤ lg := by rw [hlg_def]; positivity
  have hlg : lg ≤ δ ^ (-ν) := by rw [hlg_def]; exact_mod_cast hlogm
  have hKc : (((K₁ ^ 2 * (Nat.log 2 m + 1) : ℕ)) : ENNReal) = ENNReal.ofReal (K₁ ^ 2 * lg) := by
    rw [← ENNReal.ofReal_natCast, hlg_def]
    congr 1
    push_cast
    ring
  rw [hKc] at hmassY
  -- finiteness of the shadings
  have hYfin : ∑ i, volume (Y i) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ =>
    ne_top_of_le_ne_top (RIS.tube_volume_ne_top δ (x i) (v i))
      (measure_mono ((hY i).2.trans (hZ i).2.2.2))
  -- density of `Y`
  have hP8 : ENNReal.ofReal (ξ ^ (ηx / 4) * m * δ ^ 2) ≤ ∑ i, volume (Y i) := by
    have hcoef := Num.dens_coef (K₁ := (K₁ : ℝ)) hδ hδle1 hξ0 hξup hηx hηx1 hτ hητ hν_def hlg hlg0
      (s7 δ hδ hδ7)
    have h1 := hdens.trans hmassY
    rw [← ENNReal.ofReal_toReal hYfin, ← ENNReal.ofReal_mul (by positivity)] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    rw [← ENNReal.ofReal_toReal hYfin]
    apply ENNReal.ofReal_le_ofReal
    have hKpos : 0 < (K₁ : ℝ) ^ 2 * lg := by
      have : (1 : ℝ) ≤ lg := by rw [hlg_def]; linarith [(Nat.cast_nonneg (Nat.log 2 m) : (0 : ℝ) ≤ _)]
      positivity
    have hmd : 0 ≤ (m : ℝ) * δ ^ 2 := by positivity
    have h3 : ξ ^ (ηx / 4) * m * δ ^ 2 * ((K₁ : ℝ) ^ 2 * lg) ≤
        (∑ i, volume (Y i)).toReal * ((K₁ : ℝ) ^ 2 * lg) := by
      calc ξ ^ (ηx / 4) * m * δ ^ 2 * ((K₁ : ℝ) ^ 2 * lg)
          = (ξ ^ (ηx / 4) * ((K₁ : ℝ) ^ 2 * lg)) * (m * δ ^ 2) := by ring
        _ ≤ δ ^ η * (m * δ ^ 2) := by gcongr
        _ = δ ^ η * m * δ ^ 2 := by ring
        _ ≤ (K₁ : ℝ) ^ 2 * lg * (∑ i, volume (Y i)).toReal := h2
        _ = (∑ i, volume (Y i)).toReal * ((K₁ : ℝ) ^ 2 * lg) := by ring
    exact le_of_mul_le_mul_right h3 hKpos
  -- broadness of `Y` relative to the thin carrier
  have hbroadY := X48.broad_of_pointwise_fraction (δ := δ) (l := δ ^ (-η)) (K := (K₁ : ℝ))
    hδ.le hρ (Real.rpow_nonneg hδ.le _) (fun i => (hY i).2) hfrac hbroad
  have hcoefB := Num.broad_coef (K₁ := (K₁ : ℝ)) hδ hδle1 hξ0 hξup hηx hηx1 hτ hητ
    (by positivity) (s8 δ hδ hδ8)
  have hP9 : ∀ (p u : V) (s : ℝ), ‖u‖ = 1 → δ ≤ s → s ≤ ρ / 256 →
      (({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s} : Set (Fin m)).ncard : ℝ) ≤
        ξ ^ (-ηx) * (s / (ρ / 256)) ^ β * (({i | p ∈ Y i} : Set (Fin m)).ncard : ℝ) := by
    intro p u s hu hs hsρ
    have hsρ' : s ≤ ρ := hsρ.trans (by linarith)
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hb := hbroadY p u s hu hs hsρ'
    have hsρ1 : (s / ρ) ^ β ≤ (s / (ρ / 256)) ^ β := by
      apply Real.rpow_le_rpow (div_nonneg hs0 hρ.le) _ hβ.le
      exact div_le_div_of_nonneg_left hs0 (by positivity) (by linarith)
    have hc0 : (0 : ℝ) ≤ (({i | p ∈ Y i} : Set (Fin m)).ncard : ℝ) := Nat.cast_nonneg _
    have hq0 : 0 ≤ (s / ρ) ^ β := Real.rpow_nonneg (div_nonneg hs0 hρ.le) _
    have hξ0' : 0 ≤ ξ ^ (-ηx) := Real.rpow_nonneg hξ0.le _
    calc (({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s} : Set (Fin m)).ncard : ℝ)
        ≤ (K₁ : ℝ) * δ ^ (-η) * (s / ρ) ^ β * (({i | p ∈ Y i} : Set (Fin m)).ncard : ℝ) := hb
      _ ≤ ξ ^ (-ηx) * (s / ρ) ^ β * (({i | p ∈ Y i} : Set (Fin m)).ncard : ℝ) := by gcongr
      _ ≤ ξ ^ (-ηx) * (s / (ρ / 256)) ^ β * (({i | p ∈ Y i} : Set (Fin m)).ncard : ℝ) := by
          gcongr
  -- prisms in the thin carrier
  have hρ₁ : 0 < ρ / 256 := by positivity
  have hρ₁1 : ρ / 256 ≤ 1 / 256 := by linarith
  rw [hξdef] at hP4 hP5 hP6 hP7 hP8 hP9
  obtain ⟨Y', r, N, C, q, hY', hmassY', ⟨F⟩⟩ := hprism δ (ρ / 256) c hδ hρ₁ hρ₁1 hcpos hP3 hP4
    hP5 m x v Y y' w' k hP6 hP7 hw' (fun i => (hZ i).1) (fun i => (hY i).1)
    (fun i => (hY i).2.trans (hZ i).2.2.2) hYcar hlev hP8 hP9
  rw [← hξdef] at hmassY'
  -- the total mass loss
  have hYY' : ∑ i, volume (Y' i) ≤ ENNReal.ofReal (δ ^ (-ζ)) * ∑ i, volume (F.shading i) := by
    have h' : ENNReal.ofReal (δ ^ ζ) * ∑ i, volume (Y' i) ≤ ∑ i, volume (F.shading i) := F.retains
    calc ∑ i, volume (Y' i)
        = ENNReal.ofReal (δ ^ (-ζ)) * (ENNReal.ofReal (δ ^ ζ) * ∑ i, volume (Y' i)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hδ,
            neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (δ ^ (-ζ)) * ∑ i, volume (F.shading i) := by gcongr
  obtain ⟨Λ, hΛ_def⟩ : ∃ Λ : ℝ, Λ = (K₁ : ℝ) ^ 2 * lg * (Kx * ξ ^ (-(ηx / 8))) * δ ^ (-ζ) :=
    ⟨_, rfl⟩
  have hΛ : 0 < Λ := by
    have : (1 : ℝ) ≤ lg := by rw [hlg_def]; linarith [(Nat.cast_nonneg (Nat.log 2 m) : (0 : ℝ) ≤ _)]
    rw [hΛ_def]; positivity
  have hmassZW : ∑ i, volume (Z i) ≤ ENNReal.ofReal Λ * ∑ i, volume (F.shading i) := by
    calc ∑ i, volume (Z i) ≤ ENNReal.ofReal ((K₁ : ℝ) ^ 2 * lg) * ∑ i, volume (Y i) := hmassY
      _ ≤ ENNReal.ofReal ((K₁ : ℝ) ^ 2 * lg) * (ENNReal.ofReal (Kx * ξ ^ (-(ηx / 8))) *
            (ENNReal.ofReal (δ ^ (-ζ)) * ∑ i, volume (F.shading i))) := by
          gcongr
          exact hmassY'.trans (by gcongr)
      _ = ENNReal.ofReal Λ * ∑ i, volume (F.shading i) := by
          have hΛsplit : ENNReal.ofReal Λ = ENNReal.ofReal ((K₁ : ℝ) ^ 2 * lg) *
              ENNReal.ofReal (Kx * ξ ^ (-(ηx / 8))) * ENNReal.ofReal (δ ^ (-ζ)) := by
            rw [hΛ_def, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          rw [hΛsplit]
          ring
  -- smallness of `Λ`
  have hΛsmall : 4 * Λ * δ ^ (ε / 2) ≤ 1 := by
    have h := Num.lambda_small (K₁ := (K₁ : ℝ)) hδ hδle1 hξlow hζ_def hν_def hτ hτ1 hηx hηxζ hε
      hlg hlg0 (by linarith) (s9 δ hδ hδ9)
    rw [hΛ_def]
    linarith
  have hδεκ : δ ^ ε ≤ δ ^ (ε / 2) := Num.rpow_le_of_le hδ hδle1 (by linarith)
  have hret : Λ * (δ ^ ε + δ ^ (ε / 2)) ≤ 1 := by nlinarith
  have hden2 : 4 * δ ^ ε ≤ δ ^ ζ := by
    have h1 : δ ^ ε = δ ^ (3 * ε / 4) * δ ^ ζ := by
      rw [← Real.rpow_add hδ]; congr 1; rw [hζ_def]; ring
    have hs1 := s1 δ hδ hδ1
    have h2 : 4 * δ ^ (3 * ε / 4) ≤ 1 := by nlinarith [Real.rpow_nonneg hδ.le (3 * ε / 4)]
    have hz : 0 ≤ δ ^ ζ := Real.rpow_nonneg hδ.le _
    calc 4 * δ ^ ε = (4 * δ ^ (3 * ε / 4)) * δ ^ ζ := by rw [h1]; ring
      _ ≤ 1 * δ ^ ζ := by gcongr
      _ = δ ^ ζ := one_mul _
  have hηκ : η + ε / 2 ≤ ε := by
    have h2 : 0 ≤ 2 * η / β := by positivity
    linarith
  exact grains_of_family (ε := ε) (κ := ε / 2) (η := η) hδ hδle1 hρ hcpos hc4 (by positivity) hΛ
    hηκ hret (by linarith) hden2 (fun i => (hZ i).2.2.1)
    (fun i => (hY' i).2.trans (hY i).2) (fun i => (hZ i).2.2.2) hseg hww F hmassZW hbroad

end WangZahlLot.Obl.wz_coarse_tube_grains
