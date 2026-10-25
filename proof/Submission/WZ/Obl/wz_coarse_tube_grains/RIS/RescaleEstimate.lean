-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaleEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleSubfamily
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleArith
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Interfaces
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FiniteScales
import Submission.WZ.Obl.wz_tube_packing_bound

/-!
# `E(σ,ω)` inside a `ρ`-tube

`Interfaces.local_rescaling_of_estimate` proves the local rescaling statement `Interfaces.R`
from `Interfaces.E`, for every `m, l ≥ 1` and every `δ ≤ ρ ≤ 1`.

* If `δ ≤ δ₀` and `δ/ρ ≤ δ^c`, the rescaled subfamily (`rescaled_subfamily`) is an admissible
  family at scale `δ' = δ/(100ρ)` with density `δ'^{η_E}`, and `E` applies to it.
* Otherwise `δ/ρ` is bounded below by a power of `δ` (or `δ` is bounded below), the packing bound
  (accepted o037) for the rescaled subfamily bounds `n` by `(ρ/δ)⁴` up to `δ^{-η}`, and the
  trivial union bound `δ^η δ²` is already enough.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

namespace Interfaces

/-- The single-fibre below-slab hypothesis of `R` is a reference-body slab count. -/
theorem referenceSlabCount_of_B {δ ρ l : ℝ} {n : ℕ} {x v : Fin n → V} {y w : V}
    (hB : B δ ρ l n 1 x v Finset.univ (fun _ => y) (fun _ => w) (fun _ => 0)) :
    ReferenceSlabCount (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w)) l
      (fun i => Tube δ (x i) (v i)) := by
  intro u t r hu hr
  have h := hB 0 u t r hu hr
  simpa [B, q, o, μ, T] using h

/-- The far case: the bound given by `E` for the rescaled subfamily, transported back. -/
theorem far_case_bound {σ ω ε a η : ℝ} {D : ℕ} (hD : 0 < D) (ha : 0 < a) (hε : 0 < ε)
    (hηε : η ≤ ε / 8) {δ ρ m l : ℝ} {n k : ℕ} {Y : Fin n → Set Space}
    {Y' : Fin k → Set Space} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1) (hm : 1 ≤ m)
    (hl : 1 ≤ l) (hk : 0 < k) (hcount : δ ^ η * n ≤ 384 * D * k)
    (hEk : ENNReal.ofReal (a * ((1 / 100) * ρ⁻¹ * δ) ^ (ω + ε / 2) * (m / (1 / 100))⁻¹ *
      (k * ((1 / 100) * ρ⁻¹ * δ) ^ 2) * ((m / (1 / 100)) ^ (-(3 / 2 : ℝ)) *
        (l / (1 / 100) ^ 3 * n / k) * (k * ((1 / 100) * ρ⁻¹ * δ))) ^ (-σ)) ≤
      volume (⋃ a, Y' a))
    (hunion : volume (⋃ a, Y' a) ≤
      ENNReal.ofReal ((1 / 100) ^ 3 * (ρ⁻¹) ^ 2) * volume (⋃ i, Y i)) :
    ENNReal.ofReal ((a * (1 / 100 : ℝ) ^ (ω + ε / 2) *
        ((1 / 100 : ℝ) / ((1 / 100 : ℝ) ^ (-(3 / 2 : ℝ)) * (1 / 100) ^ 3)) ^ (-σ) /
          (384 * D)) * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have harith := far_arith (a := a) (κ := 1 / 100) (D := D) (δ := δ) (ρ := ρ) (m := m) (l := l)
    (ε₁ := ε / 2) (η := η) (ε := ε) (σ := σ) (ω := ω) (n := n) (k := k)
    ha (by norm_num) hDr hδ hδρ hρ1 hm hl hk hcount (by positivity) (by linarith)
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hJ : 0 < (1 / 100 : ℝ) ^ 3 * (ρ⁻¹) ^ 2 := by positivity
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top).mp
  rw [← ENNReal.ofReal_mul hJ.le, mul_comm ((1 / 100 : ℝ) ^ 3 * (ρ⁻¹) ^ 2)]
  exact ((ENNReal.ofReal_le_ofReal harith).trans hEk).trans hunion

/-- The density exponent of `E` is met by the rescaled subfamily at small scales. -/
theorem far_density {δ δ₀ ρ c ηE η : ℝ} {D : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hρ1 : ρ ≤ 1) (hc : 0 < c) (hηE : 0 < ηE) (hηc : η ≤ c * ηE / 2)
    (hδ₀ : δ₀ = (1 / (100 * D)) ^ (2 / (c * ηE))) (hδδ₀ : δ ≤ δ₀) (hsc : ρ⁻¹ * δ ≤ δ ^ c) :
    ((1 / 100) * ρ⁻¹ * δ) ^ ηE ≤ (1 / (100 * D)) * δ ^ η := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hδ1 : δ ≤ 1 := hδρ.trans hρ1
  have hδ' : 0 < (1 / 100) * ρ⁻¹ * δ := by positivity
  have h1 : (1 / 100) * ρ⁻¹ * δ ≤ δ ^ c := by
    have : 0 < ρ⁻¹ * δ := by positivity
    nlinarith
  have h2 : ((1 / 100) * ρ⁻¹ * δ) ^ ηE ≤ δ ^ (c * ηE) := by
    rw [Real.rpow_mul hδ.le]
    exact Real.rpow_le_rpow hδ'.le h1 hηE.le
  have h3 : δ ^ (c * ηE) = δ ^ (c * ηE / 2) * δ ^ (c * ηE / 2) := by
    rw [← Real.rpow_add hδ]; ring_nf
  have h4 : δ ^ (c * ηE / 2) ≤ 1 / (100 * D) := by
    calc
      δ ^ (c * ηE / 2) ≤ δ₀ ^ (c * ηE / 2) := Real.rpow_le_rpow hδ.le hδδ₀ (by positivity)
      _ = 1 / (100 * D) := by
        rw [hδ₀, ← Real.rpow_mul (by positivity),
          show 2 / (c * ηE) * (c * ηE / 2) = 1 by field_simp, Real.rpow_one]
  have h5 : δ ^ (c * ηE / 2) ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηc
  calc
    ((1 / 100) * ρ⁻¹ * δ) ^ ηE ≤ δ ^ (c * ηE) := h2
    _ = δ ^ (c * ηE / 2) * δ ^ (c * ηE / 2) := h3
    _ ≤ (1 / (100 * D)) * δ ^ η := mul_le_mul h4 h5 (Real.rpow_nonneg hδ.le _) (by positivity)

/-- In the close case the rescaled scale is not small: `(δ/ρ)^(-5)` is bounded. -/
theorem close_scale_bound {δ δ₀ ρ c : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1) (hc : 0 ≤ c)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (hclose : ¬ (δ ≤ δ₀ ∧ ρ⁻¹ * δ ≤ δ ^ c)) :
    (ρ⁻¹ * δ) ^ (-(5 : ℝ)) ≤ δ ^ (-(5 * c)) * δ₀ ^ (-(5 : ℝ)) := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hδ1 : δ ≤ 1 := hδρ.trans hρ1
  have hsδ : δ ≤ ρ⁻¹ * δ := by
    rw [le_inv_mul_iff₀ hρ]; exact mul_le_of_le_one_left hδ.le hρ1
  have hδc1 : 1 ≤ δ ^ (-(5 * c)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hδ₀1' : 1 ≤ δ₀ ^ (-(5 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ₀ hδ₀1 (by norm_num)
  rcases not_and_or.mp hclose with hbig | hbig
  · push Not at hbig
    have h1 : (ρ⁻¹ * δ) ^ (-(5 : ℝ)) ≤ δ₀ ^ (-(5 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hδ₀ (hbig.le.trans hsδ) (by norm_num)
    calc
      (ρ⁻¹ * δ) ^ (-(5 : ℝ)) ≤ δ₀ ^ (-(5 : ℝ)) := h1
      _ = 1 * δ₀ ^ (-(5 : ℝ)) := (one_mul _).symm
      _ ≤ _ := by gcongr
  · push Not at hbig
    have h1 : (ρ⁻¹ * δ) ^ (-(5 : ℝ)) ≤ (δ ^ c) ^ (-(5 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbig.le (by norm_num)
    rw [← Real.rpow_mul hδ.le, show c * -(5 : ℝ) = -(5 * c) by ring] at h1
    calc
      (ρ⁻¹ * δ) ^ (-(5 : ℝ)) ≤ δ ^ (-(5 * c)) := h1
      _ = δ ^ (-(5 * c)) * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr

/-- In the close case the packing bound for the rescaled subfamily bounds `n`. -/
theorem close_count_bound {δ ρ η C₀ : ℝ} {D : ℝ} {n k : ℕ} (hD : 0 ≤ D)
    (hpk : (k : ℝ) * ((1 / 100) * ρ⁻¹ * δ) ^ 4 ≤ C₀) (hcount : δ ^ η * n ≤ 384 * D * k) :
    (n : ℝ) * (ρ⁻¹ * δ) ^ 4 * δ ^ η ≤ 384 * D * (C₀ * 100 ^ 4) := by
  have h1 : (k : ℝ) * (ρ⁻¹ * δ) ^ 4 ≤ C₀ * 100 ^ 4 := by
    have : (k : ℝ) * ((1 / 100) * ρ⁻¹ * δ) ^ 4 = (k * (ρ⁻¹ * δ) ^ 4) * (1 / 100) ^ 4 := by ring
    rw [this] at hpk
    calc
      (k : ℝ) * (ρ⁻¹ * δ) ^ 4 = ((k * (ρ⁻¹ * δ) ^ 4) * (1 / 100) ^ 4) * 100 ^ 4 := by ring
      _ ≤ C₀ * 100 ^ 4 := by gcongr
  calc
    (n : ℝ) * (ρ⁻¹ * δ) ^ 4 * δ ^ η = (δ ^ η * n) * (ρ⁻¹ * δ) ^ 4 := by ring
    _ ≤ (384 * D * k) * (ρ⁻¹ * δ) ^ 4 := by gcongr
    _ = 384 * D * (k * (ρ⁻¹ * δ) ^ 4) := by ring
    _ ≤ 384 * D * (C₀ * 100 ^ 4) := by gcongr

/-- The analytic part of local rescaling depends only on the extracted-family bounds. -/
theorem local_bound_of_rescaled_family {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2)
    (hω : 0 ≤ ω) (hE : E σ ω) (D : ℕ) (hD : 0 < D) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (Y : Fin n → Set Space),
    0 < n → Dense δ η Y → RescaledFamily D δ ρ η m l Y →
    ENNReal.ofReal (κ * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨a, ha, ηE, hηE, hEst⟩ := hE (ε / 2) (half_pos hε)
  obtain ⟨C₀, hC₀, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hc : 0 < ε / 16 := by positivity
  obtain ⟨η, hη, hηc, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ ε / 16 * ηE / 2 ∧ η ≤ ε / 8 :=
    ⟨min (ε / 16 * ηE / 2) (ε / 8), lt_min (by positivity) (by positivity),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δ₀, hδ₀_def⟩ : ∃ δ₀ : ℝ, δ₀ = (1 / (100 * (D : ℝ))) ^ (2 / (ε / 16 * ηE)) := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀_def]; positivity
  have hδ₀1 : δ₀ ≤ 1 := by
    rw [hδ₀_def]
    apply Real.rpow_le_one (by positivity) _ (by positivity)
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  obtain ⟨Q, hQ_def⟩ : ∃ Q : ℝ, Q = 384 * D * (C₀ * 100 ^ 4) := ⟨_, rfl⟩
  have hQ : 0 < Q := by rw [hQ_def]; positivity
  obtain ⟨κfar, hκfar_def⟩ : ∃ κfar : ℝ, κfar = a * (1 / 100 : ℝ) ^ (ω + ε / 2) *
      ((1 / 100 : ℝ) / ((1 / 100 : ℝ) ^ (-(3 / 2 : ℝ)) * (1 / 100) ^ 3)) ^ (-σ) /
        (384 * D) := ⟨_, rfl⟩
  have hκfar : 0 < κfar := by rw [hκfar_def]; positivity
  obtain ⟨κclose, hκclose_def⟩ : ∃ κclose : ℝ, κclose = 1 / (Q * δ₀ ^ (-(5 : ℝ))) := ⟨_, rfl⟩
  have hκclose : 0 < κclose := by rw [hκclose_def]; positivity
  refine ⟨min κfar κclose, lt_min hκfar hκclose, η, hη, ?_⟩
  intro δ ρ hδ _hδ100 hδρ hρ1 m l hm hl n Y hn hdense hfamily
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hδ1 : δ ≤ 1 := hδρ.trans hρ1
  obtain ⟨k, x', v', Y', hkn, hcount, hadm, hdens', hK', hF', hunion⟩ :=
    hfamily
  have hk : 0 < k := hadm.1
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hδ' : 0 < (1 / 100) * ρ⁻¹ * δ := by positivity
  have hδ'le : (1 / 100) * ρ⁻¹ * δ ≤ 1 / 100 := by
    have : ρ⁻¹ * δ ≤ 1 := by rw [inv_mul_le_iff₀ hρ, mul_one]; exact hδρ
    nlinarith
  change ENNReal.ofReal (min κfar κclose * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) *
    (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ)) ≤ volume (⋃ i, Y i)
  by_cases hfar : δ ≤ δ₀ ∧ ρ⁻¹ * δ ≤ δ ^ (ε / 16)
  · obtain ⟨hδδ₀, hsc⟩ := hfar
    have hdensE := far_density hDr hδ hδρ hρ1 hc hηE hηc hδ₀_def hδδ₀ hsc
    have hDense : Dense ((1 / 100) * ρ⁻¹ * δ) ηE Y' := by
      apply le_trans _ hdens'
      apply ENNReal.ofReal_le_ofReal
      have hk2 : 0 ≤ (k : ℝ) * ((1 / 100) * ρ⁻¹ * δ) ^ 2 := by positivity
      calc
        ((1 / 100) * ρ⁻¹ * δ) ^ ηE * k * ((1 / 100) * ρ⁻¹ * δ) ^ 2 =
            ((1 / 100) * ρ⁻¹ * δ) ^ ηE * ((k : ℝ) * ((1 / 100) * ρ⁻¹ * δ) ^ 2) := by ring
        _ ≤ ((1 / (100 * D)) * δ ^ η) * ((k : ℝ) * ((1 / 100) * ρ⁻¹ * δ) ^ 2) :=
          mul_le_mul_of_nonneg_right hdensE hk2
        _ = _ := by ring
    have hm' : 1 ≤ m / (1 / 100) := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    have hl' : 1 ≤ l / (1 / 100) ^ 3 * n / k := by
      have h1 : 1 ≤ l / (1 / 100) ^ 3 := by
        rw [le_div_iff₀ (by norm_num)]; nlinarith
      have h2 : (1 : ℝ) ≤ n / k := by rw [le_div_iff₀ hkr, one_mul]; exact hkn
      calc
        (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ l / (1 / 100) ^ 3 * (n / k) := mul_le_mul h1 h2 zero_le_one (by positivity)
        _ = l / (1 / 100) ^ 3 * n / k := by ring
    have hA : A ((1 / 100) * ρ⁻¹ * δ) ηE (m / (1 / 100)) (l / (1 / 100) ^ 3 * n / k) k
        x' v' Y' := hypotheses_iff.mp ⟨hadm, hDense, hK', hF'⟩
    have hEk := hEst ((1 / 100) * ρ⁻¹ * δ) hδ' hδ'le (m / (1 / 100))
      (l / (1 / 100) ^ 3 * n / k) hm' hl' k x' v' Y' hA
    have hfar' := far_case_bound (σ := σ) (ω := ω) hD ha hε hηε hδ hδρ hρ1 hm hl hk hcount
      hEk hunion
    rw [← hκfar_def] at hfar'
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hfar'
    gcongr
    exact min_le_left _ _
  · have hB5 := close_scale_bound hδ hδρ hρ1 hc.le hδ₀ hδ₀1 hfar
    have hpk := hpack ((1 / 100) * ρ⁻¹ * δ) hδ' hδ'le k x' v' (fun a => (hadm.2.1 a).1)
      (fun a => (hadm.2.1 a).2.1) hadm.2.2
    have hcountQ := close_count_bound (n := n) hDr.le hpk hcount
    rw [← hQ_def] at hcountQ
    have hsmall : κclose * Q * (δ ^ (-(5 * (ε / 16))) * δ₀ ^ (-(5 : ℝ))) *
        δ ^ (ε - 2 * η) ≤ 1 := by
      have h1 : κclose * Q * δ₀ ^ (-(5 : ℝ)) = 1 := by
        rw [hκclose_def]; field_simp
      have h2 : δ ^ (-(5 * (ε / 16))) * δ ^ (ε - 2 * η) ≤ 1 := by
        rw [← Real.rpow_add hδ]
        apply Real.rpow_le_one hδ.le hδ1
        linarith
      calc
        κclose * Q * (δ ^ (-(5 * (ε / 16))) * δ₀ ^ (-(5 : ℝ))) * δ ^ (ε - 2 * η) =
            (κclose * Q * δ₀ ^ (-(5 : ℝ))) * (δ ^ (-(5 * (ε / 16))) * δ ^ (ε - 2 * η)) := by
          ring
        _ ≤ 1 * 1 := by rw [h1]; gcongr
        _ = 1 := by norm_num
    have hclose := close_arith (κR := κclose) (ε := ε) (ω := ω) hκclose.le hδ hδρ hm hl hn
      hσ hσ2 hω hcountQ hB5 hsmall
    calc
      ENNReal.ofReal (min κfar κclose * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) *
          (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ)) ≤
          ENNReal.ofReal (κclose * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) *
          (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ)) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr
        exact min_le_right _ _
      _ ≤ ENNReal.ofReal (δ ^ η * δ ^ 2) := ENNReal.ofReal_le_ofReal hclose
      _ ≤ volume (⋃ i, Y i) := average_bound_of_dense hn hdense

/-- `E(σ,ω)` implies its local version inside a `ρ`-tube, for all `m, l ≥ 1`. -/
theorem local_rescaling_of_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 ≤ ω)
    (hE : E σ ω) : R σ ω := by
  obtain ⟨D, hD, hsubfam⟩ := rescaled_subfamily
  intro ε hε
  obtain ⟨κ, hκ, η, hη, hbound⟩ := local_bound_of_rescaled_family hσ hσ2 hω hE D hD ε hε
  refine ⟨κ, hκ, η, hη, ?_⟩
  intro δ ρ hδ hδ100 hδρ hρ1 m l hm hl n x v Y y w hn hw hfib hX hdense hK hB
  exact hbound δ ρ hδ hδ100 hδρ hρ1 m l hm hl n Y hn hdense
    (hsubfam hδ hδρ hρ1 hn hw hfib hX hdense hK (referenceSlabCount_of_B hB))

end Interfaces

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
