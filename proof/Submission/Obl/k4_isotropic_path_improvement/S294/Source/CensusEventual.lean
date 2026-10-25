-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.CensusEventual, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The census constants below powers of `N` (session x1088).

* `censusFixedPowerOf R J = 3R + 93 + (3R+66) J + (2R+32) ⌈coreRowC₀⌉` and
  `censusSlack = 64 (censusFixedPowerOf coreRadius jet + 1)`: the fixed power of `Kgeom` in the
  census constant, and the tuning slack that pays it.
* `strip_pow_le`, `gap_pow_le`, `censusK_le`: `Kgeom^w ≤ Kgeom^6 N^(ub L)`,
  `Kgeom^gap ≤ Kgeom^3 N^(L/m)`, hence `censusKOf … ≤ Kgeom^Fc N^((ub + 1/m) L)`;
  `listTarget_le`: the list target `2 Kgeom^(gp+10)/fine ≤ 2 Kgeom^Fc N^(ub L)/fine`.
* `eventually_geom_le`: `geomOf (envelope κ source N (2τ)) N δ₀ L ≤ N^(3 δ₀ L)` eventually,
  uniformly in `κ, source ≤ N^σ`, `τ ≤ δ₀ L`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.CensusChoices
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.FixedSourcePowers

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

/-- The fixed power of `Kgeom` in the census constant. -/
def censusFixedPowerOf (R J : ℕ) : ℕ :=
  3 * R + 93 + (3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊

/-- The tuning slack paying the census powers. -/
def censusSlack : ℝ :=
  64 * ((censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + 1)

theorem one_le_censusSlack : 1 ≤ censusSlack := by
  unfold censusSlack
  have : (0 : ℝ) ≤ (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) :=
    Nat.cast_nonneg _
  linarith

/-- The strip power. -/
theorem strip_pow_le {Kgeom κ N δ₀ L ub : ℝ} (hK : 24 ≤ Kgeom) (hκ : 1 ≤ κ) (hκK : κ ≤ Kgeom)
    (hN : 1 ≤ N) (hNK : N ^ (2 * δ₀ * L) ≤ Kgeom) (hδL : 0 ≤ 2 * δ₀ * L) (hub : 0 ≤ ub * L) :
    Kgeom ^ stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L))) ≤ Kgeom ^ 6 * N ^ (ub * L) := by
  have hNp : 0 < N := by linarith
  have hK1 : 1 < Kgeom := by linarith
  have hrF : 0 < N ^ (-(ub * L)) := Real.rpow_pos_of_pos hNp _
  have hrF1 : N ^ (-(ub * L)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have h1 : 1 ≤ N ^ (2 * δ₀ * L) := Real.one_le_rpow hN hδL
  have h2 : 1 ≤ κ ^ 3 := one_le_pow₀ hκ
  have hnum : 1 ≤ 6 * κ ^ 3 * N ^ (2 * δ₀ * L) := by
    have : 1 ≤ κ ^ 3 * N ^ (2 * δ₀ * L) := one_le_mul_of_one_le_of_one_le h2 h1
    linarith
  have hA1 : 1 ≤ 6 * κ ^ 3 * N ^ (2 * δ₀ * L) / N ^ (-(ub * L)) := by
    rw [le_div_iff₀ hrF]; linarith
  have h := (logCeil_spec hK1 hA1).2
  unfold stripExpOf
  have hdiv : 6 * κ ^ 3 * N ^ (2 * δ₀ * L) / N ^ (-(ub * L)) =
      6 * κ ^ 3 * N ^ (2 * δ₀ * L) * N ^ (ub * L) := by
    rw [Real.rpow_neg hNp.le, div_inv_eq_mul]
  have hκ3 : κ ^ 3 ≤ Kgeom ^ 3 := pow_le_pow_left₀ (by linarith) hκK 3
  have hNu : 0 ≤ N ^ (ub * L) := (Real.rpow_pos_of_pos hNp _).le
  refine h.trans ?_
  rw [hdiv]
  calc Kgeom * (6 * κ ^ 3 * N ^ (2 * δ₀ * L) * N ^ (ub * L))
      ≤ Kgeom * (Kgeom * Kgeom ^ 3 * Kgeom * N ^ (ub * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply mul_le_mul_of_nonneg_right _ hNu
        exact mul_le_mul (mul_le_mul (by linarith) hκ3 (by positivity) (by linarith)) hNK
          (by positivity) (by positivity)
    _ = Kgeom ^ 6 * N ^ (ub * L) := by ring

/-- The gap power. -/
theorem gap_pow_le {Kgeom N δ₀ L : ℝ} {m : ℕ} (hK : 24 ≤ Kgeom) (hN : 1 ≤ N)
    (hNK : N ^ (2 * δ₀ * L) ≤ Kgeom) (hδL : 0 ≤ δ₀ * L) (hL : 0 ≤ L) :
    Kgeom ^ gapExpOf Kgeom N δ₀ L m ≤ Kgeom ^ 3 * N ^ (1 / (m : ℝ) * L) := by
  have hNp : 0 < N := by linarith
  have hK1 : 1 < Kgeom := by linarith
  have hsplit : N ^ ((1 / (m : ℝ) + 2 * δ₀) * L) = N ^ (1 / (m : ℝ) * L) * N ^ (2 * δ₀ * L) := by
    rw [← Real.rpow_add hNp]; ring_nf
  have h1 : 1 ≤ N ^ (1 / (m : ℝ) * L) := Real.one_le_rpow hN (by positivity)
  have h2 : 1 ≤ N ^ (2 * δ₀ * L) := Real.one_le_rpow hN (by nlinarith)
  have hA : 1 ≤ 2 * N ^ ((1 / (m : ℝ) + 2 * δ₀) * L) := by
    rw [hsplit]; nlinarith
  have h := (logCeil_spec hK1 hA).2
  unfold gapExpOf
  refine h.trans ?_
  rw [hsplit]
  calc Kgeom * (2 * (N ^ (1 / (m : ℝ) * L) * N ^ (2 * δ₀ * L)))
      ≤ Kgeom * (Kgeom * (N ^ (1 / (m : ℝ) * L) * Kgeom)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hNK (by linarith))
          (by positivity) (by linarith)
    _ = Kgeom ^ 3 * N ^ (1 / (m : ℝ) * L) := by ring

/-- **The census constant** below `Kgeom^Fc N^((ub + 1/m) L)`. -/
theorem censusK_le {Kgeom κ N δ₀ L ub : ℝ} {m R J : ℕ} (hK : 24 ≤ Kgeom) (hκ : 1 ≤ κ)
    (hκK : κ ≤ Kgeom) (hN : 1 ≤ N) (hNK : N ^ (2 * δ₀ * L) ≤ Kgeom) (hδL : 0 ≤ δ₀ * L)
    (hL : 0 ≤ L) (hub : 0 ≤ ub * L) :
    censusKOf Kgeom R J (stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L)))) (rowExpOf R)
        (gapExpOf Kgeom N δ₀ L m) ≤
      Kgeom ^ censusFixedPowerOf R J * N ^ ((ub + 1 / (m : ℝ)) * L) := by
  have hNp : 0 < N := by linarith
  have hw := strip_pow_le hK hκ hκK hN hNK (by linarith : 0 ≤ 2 * δ₀ * L) hub
  have hg := gap_pow_le hK hN hNK hδL hL (m := m)
  unfold censusKOf censusGp censusFixedPowerOf rowExpOf
  set w := stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L)))
  set gap := gapExpOf Kgeom N δ₀ L m
  have e1 : Kgeom ^ (3 * R + (((3 * R + 58) + 8) * J + w + (2 * R + 32) * ⌈coreRowC₀⌉₊ + 1) +
      gap + 83) = Kgeom ^ (3 * R + 84 + (3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊) *
        Kgeom ^ w * Kgeom ^ gap := by
    rw [← pow_add, ← pow_add]; ring_nf
  have e2 : N ^ ((ub + 1 / (m : ℝ)) * L) = N ^ (ub * L) * N ^ (1 / (m : ℝ) * L) := by
    rw [← Real.rpow_add hNp]; ring_nf
  have e3 : Kgeom ^ (3 * R + 93 + (3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊) =
      Kgeom ^ (3 * R + 84 + (3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊) * Kgeom ^ 6 *
        Kgeom ^ 3 := by
    rw [← pow_add, ← pow_add]; ring_nf
  rw [e1, e2, e3]
  have h0 : 0 ≤ Kgeom ^ (3 * R + 84 + (3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊) := by
    positivity
  calc Kgeom ^ (3 * R + 84 + (3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊) * Kgeom ^ w *
        Kgeom ^ gap
      ≤ Kgeom ^ (3 * R + 84 + (3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊) *
          (Kgeom ^ 6 * N ^ (ub * L)) * (Kgeom ^ 3 * N ^ (1 / (m : ℝ) * L)) := by
        gcongr
    _ = _ := by ring

/-- **The list target** below `2 Kgeom^Fc N^(ub L)/fine`. -/
theorem listTarget_le {Kgeom κ N δ₀ L ub fine : ℝ} {R J : ℕ} (hK : 24 ≤ Kgeom) (hκ : 1 ≤ κ)
    (hκK : κ ≤ Kgeom) (hN : 1 ≤ N) (hNK : N ^ (2 * δ₀ * L) ≤ Kgeom) (hδL : 0 ≤ δ₀ * L)
    (hub : 0 ≤ ub * L) (hfine : 0 < fine) :
    2 * Kgeom ^ (censusGp R J (stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L)))) (rowExpOf R) + 10) /
        fine ≤ 2 * (Kgeom ^ censusFixedPowerOf R J * N ^ (ub * L)) / fine := by
  have hw := strip_pow_le hK hκ hκK hN hNK (by linarith : 0 ≤ 2 * δ₀ * L) hub
  apply div_le_div_of_nonneg_right _ hfine.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  unfold censusGp censusFixedPowerOf rowExpOf
  set w := stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L)))
  have e1 : Kgeom ^ (((3 * R + 58) + 8) * J + w + (2 * R + 32) * ⌈coreRowC₀⌉₊ + 1 + 10) =
      Kgeom ^ ((3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊ + 11) * Kgeom ^ w := by
    rw [← pow_add]; ring_nf
  have hK1 : 1 ≤ Kgeom := by linarith
  have hle : Kgeom ^ ((3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊ + 11) * Kgeom ^ 6 ≤
      Kgeom ^ (3 * R + 93 + (3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hK1 (by omega)
  rw [e1]
  have hNu : 0 ≤ N ^ (ub * L) := (Real.rpow_pos_of_pos (by linarith) _).le
  calc Kgeom ^ ((3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊ + 11) * Kgeom ^ w
      ≤ Kgeom ^ ((3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊ + 11) *
          (Kgeom ^ 6 * N ^ (ub * L)) := by gcongr
    _ = Kgeom ^ ((3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊ + 11) * Kgeom ^ 6 *
          N ^ (ub * L) := by ring
    _ ≤ Kgeom ^ (3 * R + 93 + (3 * R + 66) * J + (2 * R + 32) * ⌈coreRowC₀⌉₊) * N ^ (ub * L) :=
        mul_le_mul_of_nonneg_right hle hNu

/-- **The census constant below a power of `N`.** -/
theorem censusK_le_rpow {Kgeom κ N δ₀ L ub γ : ℝ} {m R J : ℕ} (hK : 24 ≤ Kgeom) (hκ : 1 ≤ κ)
    (hκK : κ ≤ Kgeom) (hN : 1 ≤ N) (hNK : N ^ (2 * δ₀ * L) ≤ Kgeom) (hδL : 0 ≤ δ₀ * L)
    (hL : 0 ≤ L) (hub : 0 ≤ ub * L) (hγ : Kgeom ≤ N ^ (γ * L)) :
    censusKOf Kgeom R J (stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L)))) (rowExpOf R)
        (gapExpOf Kgeom N δ₀ L m) ≤
      N ^ ((γ * (censusFixedPowerOf R J : ℝ) + ub + 1 / (m : ℝ)) * L) := by
  have hNp : 0 < N := by linarith
  have h1 := censusK_le (R := R) (J := J) (m := m) hK hκ hκK hN hNK hδL hL hub
  refine h1.trans ?_
  have h2 : Kgeom ^ censusFixedPowerOf R J ≤ N ^ (γ * L * (censusFixedPowerOf R J : ℝ)) := by
    calc Kgeom ^ censusFixedPowerOf R J ≤ (N ^ (γ * L)) ^ censusFixedPowerOf R J :=
          pow_le_pow_left₀ (by linarith) hγ _
      _ = N ^ (γ * L * (censusFixedPowerOf R J : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
  calc Kgeom ^ censusFixedPowerOf R J * N ^ ((ub + 1 / (m : ℝ)) * L)
      ≤ N ^ (γ * L * (censusFixedPowerOf R J : ℝ)) * N ^ ((ub + 1 / (m : ℝ)) * L) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_pos_of_pos hNp _).le
    _ = N ^ ((γ * (censusFixedPowerOf R J : ℝ) + ub + 1 / (m : ℝ)) * L) := by
        rw [← Real.rpow_add hNp]; ring_nf

/-- **`Kgeom` below `N^(3 δ₀ L)`, eventually.** -/
theorem eventually_geom_le (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) {δ₀ L : ℝ}
    (hδ : 0 < δ₀) (hL : 0 < L) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source τ : ℝ, 1 ≤ κ → κ ≤ N k ^ σ → source ≤ N k ^ σ → 0 ≤ τ → τ ≤ δ₀ * L →
        geomOf (Native.nativePreGeometryEnvelope κ source (N k) (2 * τ)) (N k) δ₀ L ≤
          N k ^ (3 * δ₀ * L) := by
  have hδL : 0 < δ₀ * L := mul_pos hδ hL
  refine ⟨min 1 (δ₀ * L / 2), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  have hN1 : ∀ᶠ k in atTop, 1 ≤ N k := hN.eventually (eventually_ge_atTop 1)
  have hc1 : ∀ᶠ k in atTop, 2304 ≤ N k ^ (δ₀ * L / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < δ₀ * L / 2)).comp hN).eventually
      (eventually_ge_atTop 2304)
  have hc2 : ∀ᶠ k in atTop, 96 * coreRowK₀ ≤ N k ^ (3 * δ₀ * L) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 3 * δ₀ * L)).comp hN).eventually
      (eventually_ge_atTop (96 * coreRowK₀))
  filter_upwards [hN1, hc1, hc2] with k hk h1 h2
  intro κ source τ hκ hκN hsN hτ0 hτ
  have hNp : 0 < N k := by linarith
  have hσ : N k ^ min 1 (δ₀ * L / 2) ≤ N k ^ (δ₀ * L / 2) :=
    Real.rpow_le_rpow_of_exponent_le hk (min_le_right _ _)
  have hmax : max κ source ≤ N k ^ (δ₀ * L / 2) := max_le (hκN.trans hσ) (hsN.trans hσ)
  have hmax0 : 0 ≤ max κ source := (by linarith : (0 : ℝ) ≤ κ).trans (le_max_left _ _)
  have henv : Native.nativePreGeometryEnvelope κ source (N k) (2 * τ) ≤ N k ^ (3 * δ₀ * L) := by
    unfold Native.nativePreGeometryEnvelope
    have hτN : N k ^ (2 * τ) ≤ N k ^ (2 * (δ₀ * L)) :=
      Real.rpow_le_rpow_of_exponent_le hk (by linarith)
    calc 2304 * max κ source * N k ^ (2 * τ)
        ≤ N k ^ (δ₀ * L / 2) * N k ^ (δ₀ * L / 2) * N k ^ (2 * (δ₀ * L)) := by
          gcongr
    _ = N k ^ (3 * δ₀ * L) := by
          rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]; ring_nf
  unfold geomOf
  refine max_le (max_le henv ?_) h2
  exact Real.rpow_le_rpow_of_exponent_le hk (by nlinarith)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
