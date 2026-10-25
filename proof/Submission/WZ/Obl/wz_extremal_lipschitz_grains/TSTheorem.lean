-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TSTheorem.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSAssemble

/-!
# The frozen two-scale theorem

If there are no arbitrarily small examples above `σ`, every sufficiently extremal fine
family decomposes at every intermediate scale (`TwoScaleTheorem σ`). The exponents are
chosen as follows, with `e = min ε (1/10)`:

* the volume lower bound is used at `t = σ + e² / 16`, with its error `ηt`;
* the rescaled families have error `ηs = min ηt e`;
* the input error is `η = e³ ηs / 1000`;
* the fibre and the trimming thresholds have errors `ε2 = e² / 4` and `ε1 = e² / 8`.

All the remaining conditions hold for `δ` small enough.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate exists_rpow_cutoff)

/-- Combining two cutoffs. -/
theorem cutoff_and {P Q : ℝ → Prop} (h1 : ∃ d : ℝ, 0 < d ∧ ∀ δ, 0 < δ → δ ≤ d → P δ)
    (h2 : ∃ d : ℝ, 0 < d ∧ ∀ δ, 0 < δ → δ ≤ d → Q δ) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ, 0 < δ → δ ≤ d → P δ ∧ Q δ := by
  obtain ⟨d1, hd1, h1⟩ := h1
  obtain ⟨d2, hd2, h2⟩ := h2
  exact ⟨min d1 d2, lt_min hd1 hd2, fun δ hδ hδd =>
    ⟨h1 δ hδ (hδd.trans (min_le_left _ _)), h2 δ hδ (hδd.trans (min_le_right _ _))⟩⟩

/-- Splitting a power. -/
theorem rpow_split {δ : ℝ} (hδ : 0 < δ) (p q : ℝ) : δ ^ q = δ ^ p * δ ^ (q - p) := by
  rw [← Real.rpow_add hδ]; congr 1; ring

/-- A small power gives a large negative power. -/
theorem inv_le_rpow_neg {δ p c : ℝ} (hδ : 0 < δ) (h : δ ^ p ≤ c) :
    c⁻¹ ≤ δ ^ (-p) := by
  rw [Real.rpow_neg hδ.le]
  exact inv_anti₀ (by positivity) h

/-- A power of a quantity bounded by a power of `δ`. -/
theorem rpow_le_of_le_rpow {δ x a p : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) (hxa : x ≤ δ ^ a)
    (hp : 0 ≤ p) : x ^ p ≤ δ ^ (a * p) := by
  rw [Real.rpow_mul hδ.le]
  exact Real.rpow_le_rpow hx hxa hp

/-- The conditions of the fibre rescaling. -/
theorem cond_fibre {δ δ' e ηs η : ℝ} (hδ : 0 < δ) (hδ'pos : 0 < δ') (hδ'e : δ' ≤ δ ^ e)
    (hηs : 0 < ηs) (hc : δ ^ (e * ηs - 2 * η) ≤ 1 / (34 * 10 ^ 7)) :
    34 * δ ^ (-(2 * η)) ≤ δ' ^ (-ηs) ∧ δ' ^ ηs ≤ δ ^ (2 * η) / (34 * 10 ^ 7) := by
  have hδ'ηs : δ' ^ ηs ≤ δ ^ (e * ηs) := rpow_le_of_le_rpow hδ hδ'pos.le hδ'e hηs.le
  constructor
  · have h1 : (δ ^ e) ^ (-ηs) ≤ δ' ^ (-ηs) :=
      Real.rpow_le_rpow_of_nonpos hδ'pos hδ'e (by linarith)
    have h2 : (δ ^ e) ^ (-ηs) = δ ^ (-(2 * η)) * δ ^ (-(e * ηs - 2 * η)) := by
      rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]; congr 1; ring
    have h3 : (1 / (34 * 10 ^ 7))⁻¹ ≤ δ ^ (-(e * ηs - 2 * η)) := inv_le_rpow_neg hδ hc
    have h4 : (34 : ℝ) ≤ δ ^ (-(e * ηs - 2 * η)) := le_trans (by norm_num) h3
    calc 34 * δ ^ (-(2 * η)) ≤ δ ^ (-(e * ηs - 2 * η)) * δ ^ (-(2 * η)) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (δ ^ e) ^ (-ηs) := by rw [h2]; ring
      _ ≤ δ' ^ (-ηs) := h1
  · calc δ' ^ ηs ≤ δ ^ (e * ηs) := hδ'ηs
      _ = δ ^ (2 * η) * δ ^ (e * ηs - 2 * η) := rpow_split hδ _ _
      _ ≤ δ ^ (2 * η) * (1 / (34 * 10 ^ 7)) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring

/-- The union condition of the fibre deletion. -/
theorem cond_unionf {σ ε2 t e η δ ρ b c : ℝ} (hδ : 0 < δ) (_hρ : 0 < ρ) (hb : 0 < b)
    (hue : δ / (8 * ρ) ≤ δ ^ e) (hexp : 0 ≤ σ + ε2 - t)
    (hc : δ ^ (e * (σ + ε2 - t) - η) ≤ c)
    (hcdef : c = (8 / 100 * b) ^ t / (384 * (8 / 100) ^ 2 * b ^ 3)) :
    b ^ 3 * ((1 / 100) / ρ) ^ 2 * (384 * δ ^ 2 / ((δ / (8 * ρ)) ^ (2 - σ - ε2) * δ ^ η)) ≤
      (b * ((1 / 100) / ρ) * δ) ^ t := by
  set u : ℝ := δ / (8 * ρ) with hu_def
  have hupos : 0 < u := by positivity
  set K : ℝ := 384 * (8 / 100) ^ 2 * b ^ 3 with hK_def
  have hKpos : 0 < K := by positivity
  have ha' : (1 / 100) / ρ = 8 / 100 * u / δ := by
    rw [hu_def]; field_simp
  have hu2 : u ^ 2 / u ^ (2 - σ - ε2) = u ^ t * u ^ (σ + ε2 - t) := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_sub hupos, ← Real.rpow_add hupos]
    congr 1; push_cast; ring
  have hsmall : u ^ (σ + ε2 - t) ≤ δ ^ η * c := by
    have h1 : u ^ (σ + ε2 - t) ≤ δ ^ (e * (σ + ε2 - t)) :=
      rpow_le_of_le_rpow hδ hupos.le hue hexp
    rw [rpow_split hδ η] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  have hδ'u : b * ((1 / 100) / ρ) * δ = 8 / 100 * b * u := by
    rw [hu_def]; field_simp
  have hδ't : (b * ((1 / 100) / ρ) * δ) ^ t = (8 / 100 * b) ^ t * u ^ t := by
    rw [hδ'u, Real.mul_rpow (by positivity) hupos.le]
  have hU : 0 < u ^ (2 - σ - ε2) := by positivity
  have hD : 0 < δ ^ η := by positivity
  calc b ^ 3 * ((1 / 100) / ρ) ^ 2 * (384 * δ ^ 2 / (u ^ (2 - σ - ε2) * δ ^ η))
      = K * (u ^ 2 / u ^ (2 - σ - ε2)) / δ ^ η := by
        rw [hK_def, ha']
        field_simp
    _ = K * u ^ t * u ^ (σ + ε2 - t) / δ ^ η := by rw [hu2]; ring
    _ ≤ K * u ^ t * (δ ^ η * c) / δ ^ η := by gcongr
    _ = K * c * u ^ t := by field_simp
    _ = (b * ((1 / 100) / ρ) * δ) ^ t := by rw [hδ't, hcdef, hK_def]; field_simp

/-- The conditions of the coarse selection. -/
theorem cond_coarse {δ ρ g ηs η : ℝ} (hδ : 0 < δ) (_hρ : 0 < ρ) (h8ρ : 8 * ρ ≤ δ ^ g)
    (hηs : 0 < ηs) (hc : δ ^ (g * ηs - 2 * η) ≤ 1 / (4 * 10 ^ 9)) :
    8 * δ ^ (-(2 * η)) ≤ (8 * ρ) ^ (-ηs) ∧ (8 * ρ) ^ ηs ≤ δ ^ (2 * η) / (4 * 10 ^ 9) := by
  have h8ρpos : 0 < 8 * ρ := by positivity
  constructor
  · have h1 : (δ ^ g) ^ (-ηs) ≤ (8 * ρ) ^ (-ηs) :=
      Real.rpow_le_rpow_of_nonpos h8ρpos h8ρ (by linarith)
    have h2 : (δ ^ g) ^ (-ηs) = δ ^ (-(2 * η)) * δ ^ (-(g * ηs - 2 * η)) := by
      rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]; congr 1; ring
    have h3 : (1 / (4 * 10 ^ 9))⁻¹ ≤ δ ^ (-(g * ηs - 2 * η)) := inv_le_rpow_neg hδ hc
    have h4 : (8 : ℝ) ≤ δ ^ (-(g * ηs - 2 * η)) := le_trans (by norm_num) h3
    calc 8 * δ ^ (-(2 * η)) ≤ δ ^ (-(g * ηs - 2 * η)) * δ ^ (-(2 * η)) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (δ ^ g) ^ (-ηs) := by rw [h2]; ring
      _ ≤ (8 * ρ) ^ (-ηs) := h1
  · calc (8 * ρ) ^ ηs ≤ δ ^ (g * ηs) := rpow_le_of_le_rpow hδ h8ρpos.le h8ρ hηs.le
      _ = δ ^ (2 * η) * δ ^ (g * ηs - 2 * η) := rpow_split hδ _ _
      _ ≤ δ ^ (2 * η) * (1 / (4 * 10 ^ 9)) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring

/-- The union condition of the coarse deletion. -/
theorem cond_unionc {σ ε t e g δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (h8ρ1 : 8 * ρ ≤ 1)
    (h8ρ : 8 * ρ ≤ δ ^ g) (he : 0 < e) (hx : e / 2 ≤ σ + ε - t)
    (hc : δ ^ (g * e / 2) ≤ 1 / 384) :
    24576 * ρ ^ 2 / (8 * ρ) ^ (2 - σ - ε) ≤ (8 * ρ) ^ t := by
  have h8ρpos : 0 < 8 * ρ := by positivity
  have h2 : (8 * ρ) ^ 2 / (8 * ρ) ^ (2 - σ - ε) = (8 * ρ) ^ t * (8 * ρ) ^ (σ + ε - t) := by
    rw [← Real.rpow_natCast (8 * ρ) 2, ← Real.rpow_sub h8ρpos, ← Real.rpow_add h8ρpos]
    congr 1; push_cast; ring
  have h3 : (8 * ρ) ^ (σ + ε - t) ≤ 1 / 384 := by
    calc (8 * ρ) ^ (σ + ε - t) ≤ (8 * ρ) ^ (e / 2) :=
          Real.rpow_le_rpow_of_exponent_ge h8ρpos h8ρ1 hx
      _ ≤ δ ^ (g * (e / 2)) := rpow_le_of_le_rpow hδ h8ρpos.le h8ρ (by positivity)
      _ = δ ^ (g * e / 2) := by congr 1; ring
      _ ≤ 1 / 384 := hc
  calc 24576 * ρ ^ 2 / (8 * ρ) ^ (2 - σ - ε) =
        384 * ((8 * ρ) ^ 2 / (8 * ρ) ^ (2 - σ - ε)) := by ring
    _ = 384 * ((8 * ρ) ^ t * (8 * ρ) ^ (σ + ε - t)) := by rw [h2]
    _ ≤ 384 * ((8 * ρ) ^ t * (1 / 384)) := by gcongr
    _ = (8 * ρ) ^ t := by ring

/-- The final volume and multiplicity exponents. -/
theorem cond_exponents {σ ε ε1 ε2 e g δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (h8ρ1 : 8 * ρ ≤ 1)
    (h8ρ : 8 * ρ ≤ δ ^ g) (heε : e ≤ ε) (_hg : 0 < g) (he : 0 < e) (hε2 : 0 ≤ ε2)
    (hc : δ ^ (g * (e + ε2) - ε1 - ε2) ≤ 1 / 384) :
    24576 * ρ ^ 2 / ((8 * ρ) ^ (2 - σ - ε2) * δ ^ (ε1 + ε2)) ≤ (8 * ρ) ^ (σ - ε) ∧
      (8 * ρ) ^ (2 - σ + ε) ≤ (8 * ρ) ^ (2 - σ - ε2) * δ ^ (ε1 + ε2) := by
  have h8ρpos : 0 < 8 * ρ := by positivity
  have hV : (8 * ρ) ^ (ε + ε2) ≤ δ ^ (ε1 + ε2) / 384 := by
    calc (8 * ρ) ^ (ε + ε2) ≤ (8 * ρ) ^ (e + ε2) :=
          Real.rpow_le_rpow_of_exponent_ge h8ρpos h8ρ1 (by linarith)
      _ ≤ δ ^ (g * (e + ε2)) := rpow_le_of_le_rpow hδ h8ρpos.le h8ρ (by positivity)
      _ = δ ^ (ε1 + ε2) * δ ^ (g * (e + ε2) - ε1 - ε2) := by
          rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (ε1 + ε2) * (1 / 384) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = δ ^ (ε1 + ε2) / 384 := by ring
  have hD : 0 < δ ^ (ε1 + ε2) := by positivity
  constructor
  · have h2 : (8 * ρ) ^ 2 / (8 * ρ) ^ (2 - σ - ε2) =
        (8 * ρ) ^ (σ - ε) * (8 * ρ) ^ (ε + ε2) := by
      rw [← Real.rpow_natCast (8 * ρ) 2, ← Real.rpow_sub h8ρpos, ← Real.rpow_add h8ρpos]
      congr 1; push_cast; ring
    calc 24576 * ρ ^ 2 / ((8 * ρ) ^ (2 - σ - ε2) * δ ^ (ε1 + ε2))
        = 384 * ((8 * ρ) ^ 2 / (8 * ρ) ^ (2 - σ - ε2)) / δ ^ (ε1 + ε2) := by
          field_simp; ring
      _ = 384 * ((8 * ρ) ^ (σ - ε) * (8 * ρ) ^ (ε + ε2)) / δ ^ (ε1 + ε2) := by rw [h2]
      _ ≤ 384 * ((8 * ρ) ^ (σ - ε) * (δ ^ (ε1 + ε2) / 384)) / δ ^ (ε1 + ε2) := by gcongr
      _ = (8 * ρ) ^ (σ - ε) := by field_simp
  · have h2 : (8 * ρ) ^ (2 - σ + ε) = (8 * ρ) ^ (2 - σ - ε2) * (8 * ρ) ^ (ε + ε2) := by
      rw [← Real.rpow_add h8ρpos]; congr 1; ring
    rw [h2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith

/-- A power above `δ ^ η` by a small power. -/
theorem rpow_le_mul_of_small {δ η q c : ℝ} (hδ : 0 < δ) (hc : δ ^ (q - η) ≤ c) :
    δ ^ q ≤ δ ^ η * c := by
  rw [rpow_split hδ η q]
  exact mul_le_mul_of_nonneg_left hc (by positivity)

/-- The mass lost in the fibre deletion. -/
theorem bound_tau {δ δ' e ηs η C1 N0r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hC1 : 0 < C1) (hN0 : 0 < N0r) (hδ'pos : 0 < δ') (hδ'ηs : δ' ^ ηs ≤ δ ^ (e * ηs))
    (hc : δ ^ (e * ηs - 2 * η) ≤ 1 / (10 * C1 * (2 + 384 * 2312 * 10 ^ 4 * N0r))) :
    C1 * (2 * δ' ^ ηs + 384 * (2312 * δ ^ (-η) / (1 / 100) ^ 2 * δ' ^ ηs) * N0r) ≤
      δ ^ η / 10 := by
  set D : ℝ := δ ^ η with hD_def
  have hDpos : 0 < D := by positivity
  have hDinv : δ ^ (-η) * D = 1 := by
    rw [hD_def, ← Real.rpow_add hδ]; simp
  have hDinv1 : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  set K : ℝ := C1 * (2 + 384 * 2312 * 10 ^ 4 * N0r) with hK_def
  have hK0 : 0 < K := by positivity
  have h1 : δ' ^ ηs ≤ D * D * (1 / (10 * K)) := by
    calc δ' ^ ηs ≤ δ ^ (e * ηs) := hδ'ηs
      _ = δ ^ (2 * η) * δ ^ (e * ηs - 2 * η) := rpow_split hδ _ _
      _ ≤ δ ^ (2 * η) * (1 / (10 * K)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hK_def, ← mul_assoc]; exact hc
      _ = _ := by
          rw [hD_def, ← Real.rpow_add hδ]; congr 2; ring
  have h0 : 0 ≤ δ' ^ ηs := by positivity
  have h2 : C1 * (2 * δ' ^ ηs + 384 * (2312 * δ ^ (-η) / (1 / 100) ^ 2 * δ' ^ ηs) * N0r) ≤
      K * δ ^ (-η) * δ' ^ ηs := by
    have h3 : 2 * δ' ^ ηs ≤ 2 * δ ^ (-η) * δ' ^ ηs := by
      have := mul_le_mul_of_nonneg_right hDinv1 h0
      linarith only [this]
    have h4 : 384 * (2312 * δ ^ (-η) / (1 / 100) ^ 2 * δ' ^ ηs) * N0r =
        384 * 2312 * 10 ^ 4 * N0r * δ ^ (-η) * δ' ^ ηs := by ring
    rw [h4, hK_def]
    have := mul_le_mul_of_nonneg_left h3 hC1.le
    linarith only [this]
  calc _ ≤ K * δ ^ (-η) * δ' ^ ηs := h2
    _ ≤ K * δ ^ (-η) * (D * D * (1 / (10 * K))) := by gcongr
    _ = (δ ^ (-η) * D) * D / 10 := by field_simp
    _ = D / 10 := by rw [hDinv]; ring

/-- The mass lost in the coarse selection. -/
theorem bound_tcc {δ ρ g ηs η B2 N0r : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hB2 : 0 < B2)
    (hN0 : 0 < N0r) (h8ρηs : (8 * ρ) ^ ηs ≤ δ ^ (g * ηs))
    (hc : δ ^ (g * ηs - 5 * η) ≤ 1 / (10 * B2 * 12288 * N0r)) :
    384 * δ ^ (-η) * (32 * (δ ^ (-η)) ^ 3 * (8 * ρ) ^ ηs) * N0r ≤ δ ^ η / (10 * B2) := by
  have h1 : (δ ^ (-η)) ^ 4 * δ ^ (g * ηs) ≤ δ ^ η * (1 / (10 * B2 * 12288 * N0r)) := by
    have he : (δ ^ (-η)) ^ 4 * δ ^ (g * ηs) = δ ^ η * δ ^ (g * ηs - 5 * η) := by
      rw [← Real.rpow_natCast (δ ^ (-η)) 4, ← Real.rpow_mul hδ.le,
        ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1; push_cast; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  calc 384 * δ ^ (-η) * (32 * (δ ^ (-η)) ^ 3 * (8 * ρ) ^ ηs) * N0r =
        12288 * N0r * ((δ ^ (-η)) ^ 4 * (8 * ρ) ^ ηs) := by ring
    _ ≤ 12288 * N0r * ((δ ^ (-η)) ^ 4 * δ ^ (g * ηs)) := by gcongr
    _ ≤ 12288 * N0r * (δ ^ η * (1 / (10 * B2 * 12288 * N0r))) := by gcongr
    _ = δ ^ η / (10 * B2) := by field_simp

/-- The mass lost in the coarse cube deletion. -/
theorem bound_coarse_del {δ ρ g ηs η B2 : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hB2 : 0 < B2) (h8ρηs : (8 * ρ) ^ ηs ≤ δ ^ (g * ηs))
    (hc : δ ^ (g * ηs - 5 * η) ≤ 1 / (10 * B2 * 172032)) :
    172032 * (8 * ρ) ^ ηs * δ ^ (-η) ≤ δ ^ η / (10 * B2) := by
  have h1 : δ ^ (g * ηs) * δ ^ (-η) ≤ δ ^ η * (1 / (10 * B2 * 172032)) := by
    have he : δ ^ (g * ηs) * δ ^ (-η) = δ ^ η * δ ^ (g * ηs - 2 * η) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans hc
  calc 172032 * (8 * ρ) ^ ηs * δ ^ (-η) ≤ 172032 * δ ^ (g * ηs) * δ ^ (-η) := by gcongr
    _ = 172032 * (δ ^ (g * ηs) * δ ^ (-η)) := by ring
    _ ≤ 172032 * (δ ^ η * (1 / (10 * B2 * 172032))) := by gcongr
    _ = δ ^ η / (10 * B2) := by field_simp

/-- The mass lost in the balancing. -/
theorem bound_levels {δ ε η B2 : ℝ} {Lb : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB2 : 0 < B2)
    (hLb3 : 3 ≤ ε * ((Lb : ℝ) + 1)) (hc : δ ^ (1 - η) ≤ 1 / (10 ^ 4 * B2)) :
    1000 * (δ ^ ε) ^ (Lb + 1) / δ ^ 2 ≤ δ ^ η / (10 * B2) := by
  have h1 : (δ ^ ε) ^ (Lb + 1) ≤ δ ^ 3 := by
    rw [← Real.rpow_natCast (δ ^ ε), ← Real.rpow_mul hδ.le, ← Real.rpow_natCast δ 3]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    push_cast; linarith
  have h2 : δ = δ ^ η * δ ^ (1 - η) := by
    rw [← Real.rpow_add hδ]; simp
  have hδ2 : 0 < δ ^ 2 := by positivity
  calc 1000 * (δ ^ ε) ^ (Lb + 1) / δ ^ 2 ≤ 1000 * δ ^ 3 / δ ^ 2 := by gcongr
    _ = 1000 * δ := by field_simp
    _ = 1000 * (δ ^ η * δ ^ (1 - η)) := by rw [← h2]
    _ ≤ 1000 * (δ ^ η * (1 / (10 ^ 4 * B2))) := by gcongr
    _ = δ ^ η / (10 * B2) := by field_simp; ring

/-- The mass budget from the individual losses. -/
theorem mass_budget {D τ B2 X2 X3 X4 X5 Y1 Y2 L1 : ℝ} (hD : 0 < D) (hB2 : 0 < B2)
    (hL1 : 0 < L1) (hτ : τ ≤ D / 10) (h2 : X2 ≤ D / (10 * B2)) (h3 : X3 ≤ D / (10 * B2))
    (h4 : X4 ≤ D / (10 * B2)) (h5 : X5 ≤ D / (10 * B2)) (h6 : Y1 ≤ D / (2 * B2) / L1)
    (h7 : Y2 ≤ D / (2 * B2) / L1) :
    max Y1 Y2 ≤ ((((D - τ) / B2 - X2) - X3 - X4) - X5) / L1 := by
  have hnum : D / (2 * B2) ≤ ((((D - τ) / B2 - X2) - X3 - X4) - X5) := by
    have h1 : (D - D / 10) / B2 ≤ (D - τ) / B2 := by gcongr
    have e2 : (D - D / 10) / B2 = 9 * (D / (10 * B2)) := by field_simp; ring
    have e3 : D / (2 * B2) = 5 * (D / (10 * B2)) := by field_simp; ring
    linarith
  apply max_le
  · exact h6.trans (div_le_div_of_nonneg_right hnum hL1.le)
  · exact h7.trans (div_le_div_of_nonneg_right hnum hL1.le)

/-- Frozen sticky Prop. 3.2 from the absence of examples above `σ`. -/
theorem two_scale_theorem {σ : ℝ} (habove : ∀ t, σ < t → ¬Examples t) : TwoScaleTheorem σ := by
  intro ε hε
  -- the exponents
  set e : ℝ := min ε (1 / 10) with he_def
  have he : 0 < e := lt_min hε (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  have he10 : e ≤ 1 / 10 := min_le_right _ _
  set ε1 : ℝ := e ^ 2 / 8 with hε1_def
  set ε2 : ℝ := e ^ 2 / 4 with hε2_def
  set t : ℝ := σ + e ^ 2 / 16 with ht_def
  obtain ⟨ηt, dt, hηt, hdt, hlow⟩ :=
    (not_examples_iff t).mp (habove t (lt_add_of_pos_right σ (by positivity)))
  set ηs : ℝ := min ηt e with hηs_def
  have hηs : 0 < ηs := lt_min hηt he
  have hηse : ηs ≤ e := min_le_right _ _
  have hηst : ηs ≤ ηt := min_le_left _ _
  set η : ℝ := e ^ 3 * ηs / 1000 with hη_def
  have hη : 0 < η := by positivity
  have he3 : 0 < e ^ 3 := by positivity
  have hηle : η ≤ e ^ 4 / 1000 := by
    rw [hη_def]
    have : e ^ 3 * ηs ≤ e ^ 3 * e := mul_le_mul_of_nonneg_left hηse he3.le
    nlinarith
  have he4 : e ^ 4 ≤ e / 1000 := by
    have h1 : e ^ 3 ≤ 1 / 1000 := by
      calc e ^ 3 ≤ (1 / 10) ^ 3 := pow_le_pow_left₀ he.le he10 3
        _ = 1 / 1000 := by norm_num
    nlinarith
  have hηe : η ≤ e / 10 ^ 6 := by nlinarith
  have hηε : η ≤ ε := by nlinarith
  set g : ℝ := e - 2 * η with hg_def
  have hg : 0 < g := by rw [hg_def]; nlinarith
  have hge : g ≤ e := by rw [hg_def]; linarith
  set N0r : ℝ := ((⌈η⁻¹⌉₊ + 3 : ℕ) : ℝ) with hN0r
  set B2 : ℝ := ((bigBound + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) with hB2
  set C1 : ℝ := ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) with hC1
  set Lb : ℕ := ⌈3 / ε⌉₊ with hLb
  set b : ℝ := 1 / (1 + 144 * (1 / 100) ^ 2) with hb
  have hN0pos : 0 < N0r := by positivity
  have hB2pos : 0 < B2 := by positivity
  have hB2one : 1 ≤ B2 := by
    rw [hB2]; apply one_le_pow₀; exact_mod_cast Nat.le_add_left 1 bigBound
  have hC1pos : 0 < C1 := by positivity
  have hbpos : 0 < b := by positivity
  have hb1 : b ≤ 1 := by rw [hb]; rw [div_le_one (by positivity)]; norm_num
  -- the exponents of the cutoffs
  have p2 : 0 < e - η := by linarith
  have p5 : 0 < e * ηs - 2 * η := by
    rw [hη_def]
    have : e ^ 3 ≤ e / 100 := by nlinarith
    nlinarith [mul_pos he hηs]
  have p6 : 0 < 3 * e ^ 3 / 16 - η := by
    rw [hη_def]
    have : ηs ≤ 1 / 10 := hηse.trans he10
    nlinarith
  have p7 : 0 < g * ηs - 5 * η := by
    rw [hg_def, hη_def]
    have h1 : e ^ 3 ≤ e / 100 := by nlinarith
    have h2 : e ^ 3 * ηs ≤ e / 100 * ηs := mul_le_mul_of_nonneg_right h1 hηs.le
    nlinarith [mul_pos he hηs]
  have p8 : 0 < g * e / 2 := by positivity
  have p9 : 0 < g * (e + ε2) - ε1 - ε2 := by
    rw [hε1_def, hε2_def]
    have h1 : g * (e + e ^ 2 / 4) ≥ g * e := by
      apply mul_le_mul_of_nonneg_left _ hg.le; nlinarith
    have h2 : g ≥ e - e / 500000 := by rw [hg_def]; linarith
    nlinarith
  have p10 : 0 < ε1 - 2 * η := by
    rw [hε1_def]
    have : e ^ 4 / 1000 ≤ e ^ 2 / 100000 := by nlinarith
    nlinarith
  have p11 : 0 < 1 - η := by linarith
  have p12 : 0 < ε - η := by linarith
  have p13 : 0 < g * e - 2 * η := by
    have h2 : g ≥ e - e / 500000 := by rw [hg_def]; linarith
    have : e ^ 4 / 1000 ≤ e ^ 2 / 100000 := by nlinarith
    nlinarith
  -- the cutoffs
  set c3 : ℝ := min (1 / 10 ^ 5) (100 * dt) with hc3
  set c4 : ℝ := min dt (1 / 100) with hc4
  set c5 : ℝ := min (1 / (34 * 10 ^ 7)) (1 / (10 * C1 * (2 + 384 * 2312 * 10 ^ 4 * N0r)))
    with hc5
  set c6 : ℝ := (8 / 100 * b) ^ t / (384 * (8 / 100) ^ 2 * b ^ 3) with hc6
  set c7 : ℝ := min (1 / (4 * 10 ^ 9))
    (min (1 / (10 * B2 * 12288 * N0r)) (1 / (10 * B2 * 172032))) with hc7
  set c12 : ℝ := min (1 / 8) (1 / (2 * B2 * (Lb + 1))) with hc12
  set c13 : ℝ := 1 / (2 * B2 * (Lb + 1) * 172032) with hc13
  obtain ⟨d0, hd0, hcut⟩ :=
    cutoff_and (exists_rpow_cutoff hη (by norm_num : (0 : ℝ) < 1 / 8))
    (cutoff_and (exists_rpow_cutoff p2 (by norm_num : (0 : ℝ) < 1 / 10 ^ 12))
    (cutoff_and (exists_rpow_cutoff he (by positivity : (0 : ℝ) < c3))
    (cutoff_and (exists_rpow_cutoff hg (by positivity : (0 : ℝ) < c4))
    (cutoff_and (exists_rpow_cutoff p5 (by positivity : (0 : ℝ) < c5))
    (cutoff_and (exists_rpow_cutoff p6 (by positivity : (0 : ℝ) < c6))
    (cutoff_and (exists_rpow_cutoff p7 (by positivity : (0 : ℝ) < c7))
    (cutoff_and (exists_rpow_cutoff p8 (by norm_num : (0 : ℝ) < 1 / 384))
    (cutoff_and (exists_rpow_cutoff p9 (by norm_num : (0 : ℝ) < 1 / 384))
    (cutoff_and (exists_rpow_cutoff p10 (by positivity : (0 : ℝ) < 1 / (10 * B2)))
    (cutoff_and (exists_rpow_cutoff p11 (by positivity : (0 : ℝ) < 1 / (10 ^ 4 * B2)))
    (cutoff_and (exists_rpow_cutoff p12 (by positivity : (0 : ℝ) < c12))
      (exists_rpow_cutoff p13 (by positivity : (0 : ℝ) < c13)))))))))))))
  refine ⟨η, d0, hη, hd0, ?_⟩
  intro δ hδ hδd0 hδ1 n x v Y hF hS hvol r hr1 hr2
  obtain ⟨c1, c2, c3', c4', c5', c6', c7', c8, c9, c10, c11, c12', c13'⟩ := hcut δ hδ hδd0
  have hδ1' : δ ≤ 1 := hδ1.trans (by norm_num)
  have hδr : δ ≤ r := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith only [hε])
      _ ≤ r := hr1
  have hr1' : r ≤ 1 := hr2.trans (Real.rpow_le_one hδ.le hδ1' hε.le)
  obtain ⟨ρ, hrρ, -, hρr, k, -, z, w, hw, hsepρ, huniq, hfull, hbalρ, hfrostρ, hdilρ⟩ :=
    hS r hδr hr1'
  have hδρ : δ ≤ ρ := hδr.trans hrρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hδρ
  -- the scale `ρ` against powers of `δ`
  have hρlo : δ ^ (1 - e) ≤ ρ :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith only [heε] : 1 - ε ≤ 1 - e)).trans
      (hr1.trans hrρ)
  have hρhi : ρ ≤ δ ^ (e - η) := by
    calc ρ ≤ δ ^ (-η) * r := hρr
      _ ≤ δ ^ (-η) * δ ^ e := mul_le_mul_of_nonneg_left
          (hr2.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1' heε)) (by positivity)
      _ = δ ^ (e - η) := by rw [← Real.rpow_add hδ]; congr 1; ring
  have h8ρ : 8 * ρ ≤ δ ^ g := by
    have hs : δ ^ (e - η) = δ ^ η * δ ^ g := by
      rw [← Real.rpow_add hδ]; congr 1; rw [hg_def]; ring
    have h1 : 8 * δ ^ η ≤ 1 := by linarith only [c1]
    calc 8 * ρ ≤ 8 * δ ^ (e - η) := by linarith only [hρhi]
      _ = (8 * δ ^ η) * δ ^ g := by rw [hs]; ring
      _ ≤ 1 * δ ^ g := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = δ ^ g := one_mul _
  have h8ρ1 : 8 * ρ ≤ 1 := h8ρ.trans (c4'.trans ((min_le_right _ _).trans (by norm_num)))
  have h8ρpos : 0 < 8 * ρ := by positivity
  have hρ : ρ ≤ 1 / 10 ^ 12 := hρhi.trans c2
  have hδρe : δ / ρ ≤ δ ^ e := by
    calc δ / ρ ≤ δ / δ ^ (1 - e) := div_le_div_of_nonneg_left hδ.le (by positivity) hρlo
      _ = δ ^ e := by
        have : 0 < δ ^ e := by positivity
        rw [Real.rpow_sub hδ, Real.rpow_one]
        field_simp
  have hue : δ / (8 * ρ) ≤ δ ^ e := by
    refine le_trans ?_ hδρe
    apply div_le_div_of_nonneg_left hδ.le hρ0
    linarith only [hρ0]
  -- the rescaled fibre scale
  have hδ'pos : 0 < b * ((1 / 100) / ρ) * δ := by positivity
  have hδ'le : b * ((1 / 100) / ρ) * δ ≤ δ ^ e / 100 := by
    have h1 : b * ((1 / 100) / ρ) * δ = b / 100 * (δ / ρ) := by field_simp
    rw [h1]
    have : b * (δ / ρ) ≤ 1 * δ ^ e := mul_le_mul hb1 hδρe (by positivity) zero_le_one
    linarith only [this]
  have hδ'e : b * ((1 / 100) / ρ) * δ ≤ δ ^ e := by
    have : 0 < δ ^ e := by positivity
    linarith only [hδ'le, this]
  have hδ'small : b * ((1 / 100) / ρ) * δ ≤ 1 / 10000000 := by
    have : δ ^ e ≤ 1 / 10 ^ 5 := c3'.trans (min_le_left _ _)
    linarith only [hδ'le, this]
  have hδ'dt : b * ((1 / 100) / ρ) * δ ≤ dt := by
    have : δ ^ e ≤ 100 * dt := c3'.trans (min_le_right _ _)
    linarith only [hδ'le, this]
  -- the conditions of the steps
  obtain ⟨hC2a, hC2b⟩ := cond_fibre hδ hδ'pos hδ'e hηs (c5'.trans (min_le_left _ _))
  have hexp6 : e * (σ + ε2 - t) - η = 3 * e ^ 3 / 16 - η := by
    rw [hε2_def, ht_def]; ring
  have hunionf := cond_unionf (σ := σ) (ε2 := ε2) (t := t) (e := e) (η := η) hδ hρ0 hbpos hue
    (by rw [hε2_def, ht_def]; linarith only [sq_nonneg e]) (by rw [hexp6]; exact c6') hc6
  obtain ⟨hP1a, hP1b⟩ := cond_coarse (η := η) hδ hρ0 h8ρ hηs
    ((Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith only [hη])).trans
      (c7'.trans (min_le_left _ _)))
  have hunionc := cond_unionc (σ := σ) (ε := ε) (t := t) hδ hρ0 h8ρ1 h8ρ he
    (by rw [ht_def]; nlinarith only [heε, he, he10]) c8
  obtain ⟨hcvol, hclow⟩ := cond_exponents (σ := σ) (ε1 := ε1) hδ hρ0 h8ρ1 h8ρ heε hg he
    (by positivity) c9
  -- the volume lower bounds at the rescaled and at the coarse scale
  have hlowf : ∀ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family ηs (b * ((1 / 100) / ρ) * δ) m x' v' Y' →
        Separated ηs (b * ((1 / 100) / ρ) * δ) m x' v' →
        ENNReal.ofReal ((b * ((1 / 100) / ρ) * δ) ^ t) < volume (⋃ q, Y' q) :=
    fun m x' v' Y' hF' hS' =>
      hlow _ hδ'pos hδ'dt (hδ'small.trans (by norm_num)) m x' v' Y'
        (hF'.mono_error hδ'pos (hδ'small.trans (by norm_num)) hηst)
        (hS'.mono_error hδ'pos (hδ'small.trans (by norm_num)) hηst)
  have h8ρdt : 8 * ρ ≤ dt := h8ρ.trans (c4'.trans (min_le_left _ _))
  have h8ρ100 : 8 * ρ ≤ 1 / 100 := h8ρ.trans (c4'.trans (min_le_right _ _))
  have hlowc : ∀ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family ηs (8 * ρ) m x' v' Y' → Separated ηs (8 * ρ) m x' v' →
        ENNReal.ofReal ((8 * ρ) ^ t) < volume (⋃ q, Y' q) := fun m x' v' Y' hF' hS' =>
    hlow (8 * ρ) h8ρpos h8ρdt h8ρ100 m x' v' Y' (hF'.mono_error h8ρpos h8ρ1 hηst)
      (hS'.mono_error h8ρpos h8ρ1 hηst)
  -- the mass budget
  have hδ'ηs : (b * ((1 / 100) / ρ) * δ) ^ ηs ≤ δ ^ (e * ηs) :=
    rpow_le_of_le_rpow hδ hδ'pos.le hδ'e hηs.le
  have h8ρηs : (8 * ρ) ^ ηs ≤ δ ^ (g * ηs) := rpow_le_of_le_rpow hδ h8ρpos.le h8ρ hηs.le
  have hm1 := bound_tau hδ hδ1' hη hC1pos hN0pos hδ'pos hδ'ηs (c5'.trans (min_le_right _ _))
  have hm2 := bound_tcc hδ hρ0 hB2pos hN0pos h8ρηs
    (c7'.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm3 := bound_coarse_del hδ hδ1' hη hB2pos h8ρηs
    (c7'.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hm4 : δ ^ (ε1 - η) ≤ δ ^ η / (10 * B2) := by
    have := rpow_le_mul_of_small (q := ε1 - η) hδ
      (show δ ^ (ε1 - η - η) ≤ 1 / (10 * B2) by
        have : ε1 - η - η = ε1 - 2 * η := by ring
        rw [this]; exact c10)
    rw [div_eq_mul_one_div (δ ^ η)]
    exact this
  have hLb3 : 3 ≤ ε * ((Lb : ℝ) + 1) := by
    have h1 : 3 / ε ≤ (Lb : ℝ) := Nat.le_ceil _
    have h2 : 3 ≤ ε * Lb := by rwa [div_le_iff₀ hε, mul_comm] at h1
    linarith only [h2, hε]
  have hm5 := bound_levels (η := η) hδ hδ1' hB2pos hLb3 c11
  have hLbpos : (0 : ℝ) < Lb + 1 := by positivity
  have hm6 : δ ^ ε ≤ δ ^ η / (2 * B2) / (Lb + 1) := by
    have := rpow_le_mul_of_small (q := ε) hδ (c12'.trans (min_le_right _ _))
    refine this.trans (le_of_eq ?_)
    field_simp
  have hm7 : 172032 * (8 * ρ) ^ ε * δ ^ (-η) ≤ δ ^ η / (2 * B2) / (Lb + 1) := by
    have h1 : (8 * ρ) ^ ε ≤ δ ^ (g * e) :=
      (Real.rpow_le_rpow_of_exponent_ge h8ρpos h8ρ1 heε).trans
        (rpow_le_of_le_rpow hδ h8ρpos.le h8ρ he.le)
    have h2 : δ ^ (g * e) * δ ^ (-η) = δ ^ η * δ ^ (g * e - 2 * η) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
    calc 172032 * (8 * ρ) ^ ε * δ ^ (-η) ≤ 172032 * δ ^ (g * e) * δ ^ (-η) := by gcongr
      _ = 172032 * (δ ^ η * δ ^ (g * e - 2 * η)) := by rw [← h2]; ring
      _ ≤ 172032 * (δ ^ η * c13) := by gcongr
      _ = δ ^ η / (2 * B2) / (Lb + 1) := by rw [hc13]; field_simp
  have hmass := mass_budget (by positivity) hB2pos hLbpos hm1 hm2 hm3 hm4 hm5 hm6 hm7
  -- the coarse scale is comparable to `r`
  have hρc : 8 * ρ ≤ δ ^ (-ε) * r := by
    have h1 : (1 / 8 : ℝ)⁻¹ ≤ δ ^ (-(ε - η)) :=
      inv_le_rpow_neg hδ (c12'.trans (min_le_left _ _))
    have h2 : δ ^ (-ε) = δ ^ (-(ε - η)) * δ ^ (-η) := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    have h3 : (8 : ℝ) ≤ δ ^ (-(ε - η)) := le_trans (by norm_num) h1
    have hr0 : 0 ≤ r := hδ.le.trans hδr
    calc 8 * ρ ≤ 8 * (δ ^ (-η) * r) := by linarith only [hρr]
      _ ≤ δ ^ (-(ε - η)) * (δ ^ (-η) * r) :=
          mul_le_mul_of_nonneg_right h3 (mul_nonneg (by positivity) hr0)
      _ = δ ^ (-ε) * r := by rw [h2]; ring
  refine ⟨8 * ρ, by linarith only [hrρ, hρ0], hρc, ?_⟩
  exact two_scale_core (ε1 := ε1) (ε2 := ε2) (ηs := ηs) (t := t) (a := (1 / 100) / ρ) (b := b)
    (δ' := b * ((1 / 100) / ρ) * δ) (β := δ ^ ε) (Lb := Lb) hδ hδ1 hη hηε
    (by rw [hε1_def]; nlinarith only [he, he10, heε]) (by rw [hε2_def]; nlinarith only [he, he10, heε])
    (hηse.trans heε) hF hS hvol hw hsepρ huniq hfull hbalρ hfrostρ hdilρ hδρ hρ hlowf hlowc rfl
    rfl rfl hδ'small hC2a hC2b rfl rfl rfl hunionf hP1a hP1b rfl hunionc rfl hmass hcvol hclow

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
