-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceDepth
import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_finite_affine_parent_sources.NativePriorCalibration

/-!
# Rate numerics of a source stage

Time-length increments, thickness ratios and full-prior ratios between two levels of the
supplied path, in powers of `Nk` with explicit errors coming only from the supplied depth,
time and narrowness errors `δ₀ L`, the grid mesh and the profile error.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

theorem delta_two_sided {N : ℝ} (hN : 0 < N) (r : ℝ) :
    N ^ (-r) ≤ δ N r ∧ δ N r ≤ 2 * N ^ (-r) :=
  Submission.Obl.k4_profile_density_bounds.width_bounds hN r

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **Time increment between two levels.** -/
theorem level_time_increment (hNk : 1 ≤ Nk) (hL : 0 ≤ L) {i j : ℕ} (hi : i < m) (hj : j < m)
    (hgap : 2 * δ₀ ≤ κ₁ * (sg j - sg i)) :
    p.T i ≤ p.T j ∧
      Nk ^ ((κ₁ * (sg j - sg i) - 2 * δ₀) * L) ≤ (2 : ℝ) ^ (p.T j - p.T i) ∧
      (2 : ℝ) ^ (p.T j - p.T i) ≤ Nk ^ ((κ₁ * (sg j - sg i) + 2 * δ₀) * L) := by
  obtain ⟨-, -, hilo, hihi, -⟩ := hp.level_bounds i hi
  obtain ⟨-, -, hjlo, hjhi, -⟩ := hp.level_bounds j hj
  have hN0 : 0 < Nk := by linarith
  have hmid : Nk ^ ((κ₁ * sg i + δ₀) * L) ≤ Nk ^ ((κ₁ * sg j - δ₀) * L) :=
    Real.rpow_le_rpow_of_exponent_le hNk (by nlinarith)
  have hTle : (2 : ℝ) ^ p.T i ≤ (2 : ℝ) ^ p.T j := hihi.trans (hmid.trans hjlo)
  have hT : p.T i ≤ p.T j := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hTle
  have hsplit : (2 : ℝ) ^ (p.T j - p.T i) = (2 : ℝ) ^ p.T j / (2 : ℝ) ^ p.T i := by
    rw [pow_sub₀ _ (by norm_num) hT, div_eq_mul_inv]
  have hpi : (0 : ℝ) < (2 : ℝ) ^ p.T i := by positivity
  refine ⟨hT, ?_, ?_⟩
  · rw [hsplit, le_div_iff₀ hpi]
    calc Nk ^ ((κ₁ * (sg j - sg i) - 2 * δ₀) * L) * (2 : ℝ) ^ p.T i
        ≤ Nk ^ ((κ₁ * (sg j - sg i) - 2 * δ₀) * L) * Nk ^ ((κ₁ * sg i + δ₀) * L) :=
          mul_le_mul_of_nonneg_left hihi (by positivity)
      _ = Nk ^ ((κ₁ * sg j - δ₀) * L) := by rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ (2 : ℝ) ^ p.T j := hjlo
  · rw [hsplit, div_le_iff₀ hpi]
    calc (2 : ℝ) ^ p.T j ≤ Nk ^ ((κ₁ * sg j + δ₀) * L) := hjhi
      _ = Nk ^ ((κ₁ * (sg j - sg i) + 2 * δ₀) * L) * Nk ^ ((κ₁ * sg i - δ₀) * L) := by
          rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ Nk ^ ((κ₁ * (sg j - sg i) + 2 * δ₀) * L) * (2 : ℝ) ^ p.T i :=
          mul_le_mul_of_nonneg_left hilo (by positivity)

/-- **Full-prior bounds of a label** from saturation and the counted-in-packet inclusion. -/
theorem assigned_prior_bounds (b : Fin p.C) [IsFiniteMeasure (ν (p.world b))]
    (hNk : 0 < Nk) :
    Nk ^ (-f (p.r (p.lev b))) * |(p.frame b).det| / p.κ ≤ (ν (p.world b) (p.assigned b)).toReal ∧
      (ν (p.world b) (p.assigned b)).toReal ≤ p.κ * Nk ^ (-f (p.r (p.lev b))) *
        |(p.frame b).det| := by
  obtain ⟨hlo, hup⟩ := hp.saturation b
  have hκ := hp.one_le_slack
  have hq : (0 : ℝ) < ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by positivity
  have hfin : ν (p.world b) (p.assigned b) ≠ ⊤ := measure_ne_top _ _
  have hpk : ((ν (p.world b)).prod volume) (p.packet b) =
      ν (p.world b) (p.assigned b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) := by
    rw [PathData.packet, Measure.prod_prod, Real.volume_Icc]
    congr 2
    rw [← sub_div]; ring
  have hsub : p.counted b ⊆ p.packet b := fun z hz =>
    ⟨(hp.counted_support b z hz).2.1, (hp.counted_support b z hz).2.2.1⟩
  have hc := hlo.trans (measure_mono (μ := (ν (p.world b)).prod volume) hsub)
  rw [hpk] at hc
  constructor
  · -- from the counted lower bound
    have hc' : Nk ^ (-f (p.r (p.lev b))) * |(p.frame b).det| / ((2 : ℝ) ^ p.T (p.lev b) * p.κ) ≤
        (ν (p.world b) (p.assigned b)).toReal * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by
      have := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top)).mp hc
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le] at this
    have h2 : (0 : ℝ) < (2 : ℝ) ^ p.T (p.lev b) := by positivity
    have hκ0 : 0 < p.κ := by linarith
    calc Nk ^ (-f (p.r (p.lev b))) * |(p.frame b).det| / p.κ
        = (Nk ^ (-f (p.r (p.lev b))) * |(p.frame b).det| / ((2 : ℝ) ^ p.T (p.lev b) * p.κ)) *
            (2 : ℝ) ^ p.T (p.lev b) := by field_simp
      _ ≤ ((ν (p.world b) (p.assigned b)).toReal * ((2 : ℝ) ^ p.T (p.lev b))⁻¹) *
            (2 : ℝ) ^ p.T (p.lev b) := mul_le_mul_of_nonneg_right hc' h2.le
      _ = (ν (p.world b) (p.assigned b)).toReal := by field_simp
  · have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hup
    rwa [ENNReal.toReal_ofReal (by
      have := hp.one_le_slack
      positivity)] at this

/-- **The `time` field** of the source facts, for the source depth map. -/
theorem time_field (hNk : 1 ≤ Nk) (hL : 0 ≤ L) (hm : 0 < m) {i₀ : ℕ} (hi₀ : i₀ < m)
    {u mesh θ K : ℝ} (hu : 0 ≤ u) (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ i, i + 1 < m → sg (i + 1) - sg i ≤ mesh) (hroom : sg i₀ + u ≤ sg (m - 1))
    (hκ₁ : 0 ≤ κ₁) (herr : κ₁ * mesh + 2 * δ₀ ≤ u * θ)
    (hK : K = (Nk ^ (u * L)) ^ θ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hgap : 2 * δ₀ ≤ κ₁ * (u * x - mesh)) :
    (Nk ^ (u * L)) ^ (κ₁ * x) / K ≤
        (2 : ℝ) ^ (p.T (sourceDepth m sg i₀ u x) - p.T i₀) ∧
      (2 : ℝ) ^ (p.T (sourceDepth m sg i₀ u x) - p.T i₀) ≤
        K * (Nk ^ (u * L)) ^ (κ₁ * x) := by
  obtain ⟨hlo, hhi⟩ := sourceDepth_nominal hm hi₀ hu hmesh0 hmesh hroom hx0 hx1
  set j := sourceDepth m sg i₀ u x
  have hj : j < m := sourceDepth_lt hm sg i₀ u x
  have hgap' : 2 * δ₀ ≤ κ₁ * (sg j - sg i₀) := by nlinarith
  obtain ⟨-, htlo, hthi⟩ := level_time_increment hp hNk hL hi₀ hj hgap'
  have hN0 : 0 < Nk := by linarith
  have hNx : (Nk ^ (u * L)) ^ (κ₁ * x) = Nk ^ (κ₁ * (u * x) * L) := by
    rw [← Real.rpow_mul hN0.le]; congr 1; ring
  have hKe : K = Nk ^ (u * θ * L) := by
    rw [hK, ← Real.rpow_mul hN0.le]; congr 1; ring
  have hK0 : 0 < K := by rw [hKe]; positivity
  rw [hNx]
  constructor
  · rw [div_le_iff₀ hK0]
    calc Nk ^ (κ₁ * (u * x) * L) = Nk ^ ((κ₁ * (u * x) - u * θ) * L) * K := by
          rw [hKe, ← Real.rpow_add hN0]; congr 1; ring
      _ ≤ Nk ^ ((κ₁ * (sg j - sg i₀) - 2 * δ₀) * L) * K := by
          apply mul_le_mul_of_nonneg_right _ hK0.le
          apply Real.rpow_le_rpow_of_exponent_le hNk
          have h1 : κ₁ * (u * x) - κ₁ * mesh ≤ κ₁ * (sg j - sg i₀) := by nlinarith
          nlinarith
      _ ≤ (2 : ℝ) ^ (p.T j - p.T i₀) * K := mul_le_mul_of_nonneg_right htlo hK0.le
  · calc (2 : ℝ) ^ (p.T j - p.T i₀) ≤ Nk ^ ((κ₁ * (sg j - sg i₀) + 2 * δ₀) * L) := hthi
      _ ≤ Nk ^ ((κ₁ * (u * x) + u * θ) * L) := by
          apply Real.rpow_le_rpow_of_exponent_le hNk
          have h1 : κ₁ * (sg j - sg i₀) ≤ κ₁ * (u * x) := by nlinarith
          have h2 : 2 * δ₀ ≤ u * θ := by nlinarith
          nlinarith
      _ = K * Nk ^ (κ₁ * (u * x) * L) := by
          rw [hKe, ← Real.rpow_add hN0]; congr 1; ring

/-- **The `thick` field**: thickness ratios of the source depth map. -/
theorem thick_field (hNk : 1 ≤ Nk) (hL : 0 ≤ L) (hm : 0 < m) {i₀ : ℕ} (hi₀ : i₀ < m)
    {u mesh θ K : ℝ} (hu : 0 ≤ u) (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ i, i + 1 < m → sg (i + 1) - sg i ≤ mesh) (hroom : sg i₀ + u ≤ sg (m - 1))
    (herr : mesh + 2 * δ₀ ≤ u * θ / 2) (hK : K = (Nk ^ (u * L)) ^ θ)
    (hκK : 2 * p.κ * Nk ^ (u * θ * L / 2) ≤ K) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    p.κ * (δ Nk (p.r (sourceDepth m sg i₀ u x)) / δ Nk (p.r i₀)) ≤
        K * (Nk ^ (u * L)) ^ (-x) ∧
      p.κ / (δ Nk (p.r (sourceDepth m sg i₀ u x)) / δ Nk (p.r i₀)) ≤
        K / (Nk ^ (u * L)) ^ (-x) := by
  obtain ⟨hact, -⟩ := sourceDepth_actual hp hm hi₀ hu hmesh0 hmesh hroom hL hx0 hx1
  set j := sourceDepth m sg i₀ u x
  have hN0 : 0 < Nk := by linarith
  have hκ := hp.one_le_slack
  set Δ := p.r j - p.r i₀
  have hΔ : |Δ - u * L * x| ≤ (mesh + 2 * δ₀) * L := hact
  rw [abs_le] at hΔ
  obtain ⟨hj1, hj2⟩ := delta_two_sided hN0 (p.r j)
  obtain ⟨hi1, hi2⟩ := delta_two_sided hN0 (p.r i₀)
  have hδj : 0 < δ Nk (p.r j) := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hj1
  have hδi : 0 < δ Nk (p.r i₀) := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hi1
  have hNx : (Nk ^ (u * L)) ^ (-x) = Nk ^ (-(u * L * x)) := by
    rw [← Real.rpow_mul hN0.le]; congr 1; ring
  have hKe : K = Nk ^ (u * θ * L) := by
    rw [hK, ← Real.rpow_mul hN0.le]; congr 1; ring
  have hEL : (mesh + 2 * δ₀) * L ≤ u * θ * L / 2 := by nlinarith
  rw [hNx]
  constructor
  · -- ratio ≤ 2 N^(-Δ) ≤ 2 N^(-uLx + e)
    have hratio : δ Nk (p.r j) / δ Nk (p.r i₀) ≤ 2 * Nk ^ (-Δ) := by
      rw [div_le_iff₀ hδi]
      calc δ Nk (p.r j) ≤ 2 * Nk ^ (-p.r j) := hj2
        _ = 2 * Nk ^ (-Δ) * Nk ^ (-p.r i₀) := by
            rw [mul_assoc, ← Real.rpow_add hN0]; congr 2; ring
        _ ≤ 2 * Nk ^ (-Δ) * δ Nk (p.r i₀) := by gcongr
    calc p.κ * (δ Nk (p.r j) / δ Nk (p.r i₀)) ≤ p.κ * (2 * Nk ^ (-Δ)) := by gcongr
      _ ≤ p.κ * (2 * Nk ^ (u * θ * L / 2 - u * L * x)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.rpow_le_rpow_of_exponent_le hNk
          linarith
      _ = 2 * p.κ * Nk ^ (u * θ * L / 2) * Nk ^ (-(u * L * x)) := by
          rw [show u * θ * L / 2 - u * L * x = u * θ * L / 2 + (-(u * L * x)) by ring,
            Real.rpow_add hN0]; ring
      _ ≤ K * Nk ^ (-(u * L * x)) := by gcongr
  · have hratio : Nk ^ (-Δ) / 2 ≤ δ Nk (p.r j) / δ Nk (p.r i₀) := by
      rw [le_div_iff₀ hδi]
      calc Nk ^ (-Δ) / 2 * δ Nk (p.r i₀) ≤ Nk ^ (-Δ) / 2 * (2 * Nk ^ (-p.r i₀)) := by gcongr
        _ = Nk ^ (-p.r j) := by
            rw [show Nk ^ (-Δ) / 2 * (2 * Nk ^ (-p.r i₀)) = Nk ^ (-Δ) * Nk ^ (-p.r i₀) by ring,
              ← Real.rpow_add hN0]; congr 1; ring
        _ ≤ δ Nk (p.r j) := hj1
    have hpos : 0 < Nk ^ (-Δ) / 2 := by positivity
    have hNe : 0 < Nk ^ (-(u * L * x)) := by positivity
    rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hratio) hNe]
    calc p.κ * Nk ^ (-(u * L * x)) = p.κ * 2 * Nk ^ (-Δ) / 2 * Nk ^ (Δ - u * L * x) := by
          rw [show p.κ * 2 * Nk ^ (-Δ) / 2 * Nk ^ (Δ - u * L * x) =
            p.κ * (Nk ^ (-Δ) * Nk ^ (Δ - u * L * x)) by ring, ← Real.rpow_add hN0]
          congr 2; ring
      _ ≤ p.κ * 2 * Nk ^ (-Δ) / 2 * Nk ^ (u * θ * L / 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.rpow_le_rpow_of_exponent_le hNk
          linarith
      _ = (2 * p.κ * Nk ^ (u * θ * L / 2)) * (Nk ^ (-Δ) / 2) := by ring
      _ ≤ K * (δ Nk (p.r j) / δ Nk (p.r i₀)) := by
          apply mul_le_mul hκK hratio hpos.le
          rw [hKe]; positivity

/-- Relative narrowness of two labels: the ratio of determinants is `4^(-ΔT)` times a power
of `Nk` within `2 δ₀ L` of the narrowness increment. -/
theorem det_ratio_bounds (hNk : 0 < Nk) (b₀ b : Fin p.C) (hT : p.T (p.lev b₀) ≤ p.T (p.lev b)) :
    (4 : ℝ)⁻¹ ^ (p.T (p.lev b) - p.T (p.lev b₀)) *
        Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) - 2 * δ₀ * L) ≤
      |(p.frame b).det| / |(p.frame b₀).det| ∧
    |(p.frame b).det| / |(p.frame b₀).det| ≤
      (4 : ℝ)⁻¹ ^ (p.T (p.lev b) - p.T (p.lev b₀)) *
        Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) + 2 * δ₀ * L) := by
  obtain ⟨h1, h2⟩ := hp.narrowness b
  obtain ⟨h3, h4⟩ := hp.narrowness b₀
  set D₁ := |(p.frame b).det|
  set D₀ := |(p.frame b₀).det|
  set T₁ := p.T (p.lev b)
  set T₀ := p.T (p.lev b₀)
  have hD₀ : 0 < D₀ := abs_pos.mpr (hp.chart b₀).1
  have h4T : (4 : ℝ) ^ T₁ = (4 : ℝ) ^ (T₁ - T₀) * (4 : ℝ) ^ T₀ := by
    rw [← pow_add, Nat.sub_add_cancel hT]
  have hq : (4 : ℝ)⁻¹ ^ (T₁ - T₀) = ((4 : ℝ) ^ (T₁ - T₀))⁻¹ := inv_pow _ _
  have hA : (0 : ℝ) < (4 : ℝ) ^ (T₁ - T₀) := by positivity
  have hB : (0 : ℝ) < (4 : ℝ) ^ T₀ := by positivity
  rw [hq]
  constructor
  · rw [le_div_iff₀ hD₀]
    -- D₁ 4^T₁ ≥ N^(-(nw₁+δ₀L)), D₀ 4^T₀ ≤ N^(-(nw₀-δ₀L))
    have e1 : Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) - 2 * δ₀ * L) *
        Nk ^ (-(p.nw (p.lev b₀) - δ₀ * L)) = Nk ^ (-(p.nw (p.lev b) + δ₀ * L)) := by
      rw [← Real.rpow_add hNk]; congr 1; ring
    have : ((4 : ℝ) ^ (T₁ - T₀))⁻¹ * Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) - 2 * δ₀ * L) *
        (D₀ * (4 : ℝ) ^ T₀) * (4 : ℝ) ^ (T₁ - T₀) ≤ D₁ * (4 : ℝ) ^ T₁ := by
      calc ((4 : ℝ) ^ (T₁ - T₀))⁻¹ * Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) - 2 * δ₀ * L) *
            (D₀ * (4 : ℝ) ^ T₀) * (4 : ℝ) ^ (T₁ - T₀)
          = Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) - 2 * δ₀ * L) * (D₀ * (4 : ℝ) ^ T₀) := by
            field_simp
        _ ≤ Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) - 2 * δ₀ * L) *
              Nk ^ (-(p.nw (p.lev b₀) - δ₀ * L)) := by gcongr
        _ = Nk ^ (-(p.nw (p.lev b) + δ₀ * L)) := e1
        _ ≤ D₁ * (4 : ℝ) ^ T₁ := h1
    rw [h4T] at this
    have hpos : (0 : ℝ) < (4 : ℝ) ^ (T₁ - T₀) * (4 : ℝ) ^ T₀ := mul_pos hA hB
    refine le_of_mul_le_mul_right ?_ hpos
    calc ((4 : ℝ) ^ (T₁ - T₀))⁻¹ * Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) - 2 * δ₀ * L) * D₀ *
          ((4 : ℝ) ^ (T₁ - T₀) * (4 : ℝ) ^ T₀)
        = ((4 : ℝ) ^ (T₁ - T₀))⁻¹ * Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) - 2 * δ₀ * L) *
            (D₀ * (4 : ℝ) ^ T₀) * (4 : ℝ) ^ (T₁ - T₀) := by ring
      _ ≤ D₁ * ((4 : ℝ) ^ (T₁ - T₀) * (4 : ℝ) ^ T₀) := this
  · rw [div_le_iff₀ hD₀]
    have e1 : Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) + 2 * δ₀ * L) *
        Nk ^ (-(p.nw (p.lev b₀) + δ₀ * L)) = Nk ^ (-(p.nw (p.lev b) - δ₀ * L)) := by
      rw [← Real.rpow_add hNk]; congr 1; ring
    have : D₁ * (4 : ℝ) ^ T₁ ≤ ((4 : ℝ) ^ (T₁ - T₀))⁻¹ *
        Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) + 2 * δ₀ * L) *
        (D₀ * (4 : ℝ) ^ T₀) * (4 : ℝ) ^ (T₁ - T₀) := by
      calc D₁ * (4 : ℝ) ^ T₁ ≤ Nk ^ (-(p.nw (p.lev b) - δ₀ * L)) := h2
        _ = Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) + 2 * δ₀ * L) *
              Nk ^ (-(p.nw (p.lev b₀) + δ₀ * L)) := e1.symm
        _ ≤ Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) + 2 * δ₀ * L) * (D₀ * (4 : ℝ) ^ T₀) := by
            gcongr
        _ = ((4 : ℝ) ^ (T₁ - T₀))⁻¹ * Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) + 2 * δ₀ * L) *
              (D₀ * (4 : ℝ) ^ T₀) * (4 : ℝ) ^ (T₁ - T₀) := by field_simp
    rw [h4T] at this
    have hpos : (0 : ℝ) < (4 : ℝ) ^ (T₁ - T₀) * (4 : ℝ) ^ T₀ := mul_pos hA hB
    refine le_of_mul_le_mul_right ?_ hpos
    calc D₁ * ((4 : ℝ) ^ (T₁ - T₀) * (4 : ℝ) ^ T₀) ≤ ((4 : ℝ) ^ (T₁ - T₀))⁻¹ *
          Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) + 2 * δ₀ * L) *
          (D₀ * (4 : ℝ) ^ T₀) * (4 : ℝ) ^ (T₁ - T₀) := this
      _ = ((4 : ℝ) ^ (T₁ - T₀))⁻¹ * Nk ^ (-(p.nw (p.lev b) - p.nw (p.lev b₀)) + 2 * δ₀ * L) * D₀ *
          ((4 : ℝ) ^ (T₁ - T₀) * (4 : ℝ) ^ T₀) := by ring

/-- **Full-prior ratio of two labels in powers of `Nk`.** With `E` bounding the profile and
narrowness errors, the prior ratio is `4^(-ΔT) Nk^(-(d₁+ℓ)Δ)` up to `κ² Nk^E`. -/
theorem prior_ratio_bounds (hNk : 1 ≤ Nk) (b₀ b : Fin p.C)
    [IsFiniteMeasure (ν (p.world b))] (hw : p.world b₀ = p.world b)
    (hT : p.T (p.lev b₀) ≤ p.T (p.lev b)) {d₁ Δ E : ℝ}
    (hf : |f (p.r (p.lev b)) - f (p.r (p.lev b₀)) - d₁ * Δ| +
      |p.nw (p.lev b) - p.nw (p.lev b₀) - ℓ * Δ| + 2 * δ₀ * L ≤ E) :
    (p.κ ^ 2)⁻¹ * Nk ^ (-E) *
        ((4 : ℝ)⁻¹ ^ (p.T (p.lev b) - p.T (p.lev b₀)) * Nk ^ (-((d₁ + ℓ) * Δ))) ≤
      (ν (p.world b) (p.assigned b)).toReal / (ν (p.world b) (p.assigned b₀)).toReal ∧
    (ν (p.world b) (p.assigned b)).toReal / (ν (p.world b) (p.assigned b₀)).toReal ≤
      p.κ ^ 2 * Nk ^ E *
        ((4 : ℝ)⁻¹ ^ (p.T (p.lev b) - p.T (p.lev b₀)) * Nk ^ (-((d₁ + ℓ) * Δ))) := by
  have hκ := hp.one_le_slack
  have hκ0 : 0 < p.κ := by linarith
  have hN0 : 0 < Nk := by linarith
  have hfin0 : IsFiniteMeasure (ν (p.world b₀)) := by rw [hw]; infer_instance
  obtain ⟨hlo1, hup1⟩ := assigned_prior_bounds hp b hN0
  obtain ⟨hlo0, hup0⟩ := assigned_prior_bounds hp b₀ hN0
  rw [hw] at hlo0 hup0
  have hD₁ : 0 < |(p.frame b).det| := abs_pos.mpr (hp.chart b).1
  have hD₀ : 0 < |(p.frame b₀).det| := abs_pos.mpr (hp.chart b₀).1
  have hA₁ : 0 < (ν (p.world b) (p.assigned b)).toReal :=
    lt_of_lt_of_le (div_pos (mul_pos (Real.rpow_pos_of_pos hN0 _) hD₁) hκ0) hlo1
  have hA₀ : 0 < (ν (p.world b) (p.assigned b₀)).toReal :=
    lt_of_lt_of_le (div_pos (mul_pos (Real.rpow_pos_of_pos hN0 _) hD₀) hκ0) hlo0
  obtain ⟨hr1, hr2⟩ := saturated_prior_ratio
    Nk p.κ |(p.frame b₀).det| |(p.frame b).det| _ _ _ _ hN0 hκ0 hD₀ hD₁ hA₀ hA₁
    hlo0 hup0 hlo1 hup1
  obtain ⟨hd1, hd2⟩ := det_ratio_bounds hp hN0 b₀ b hT
  set fd := f (p.r (p.lev b)) - f (p.r (p.lev b₀))
  set nd := p.nw (p.lev b) - p.nw (p.lev b₀)
  set Q := (4 : ℝ)⁻¹ ^ (p.T (p.lev b) - p.T (p.lev b₀))
  have hQ : 0 < Q := by positivity
  have h1 := abs_nonneg (nd - ℓ * Δ)
  have h2 := abs_nonneg (fd - d₁ * Δ)
  have h3 := le_abs_self (fd - d₁ * Δ)
  have h4 := neg_abs_le (fd - d₁ * Δ)
  have h5 := le_abs_self (nd - ℓ * Δ)
  have h6 := neg_abs_le (nd - ℓ * Δ)
  have hE1 : -E + -((d₁ + ℓ) * Δ) ≤ -fd + (-nd - 2 * δ₀ * L) := by nlinarith
  have hE2 : -fd + (-nd + 2 * δ₀ * L) ≤ E + -((d₁ + ℓ) * Δ) := by nlinarith
  constructor
  · calc (p.κ ^ 2)⁻¹ * Nk ^ (-E) * (Q * Nk ^ (-((d₁ + ℓ) * Δ)))
        = (p.κ ^ 2)⁻¹ * Q * Nk ^ (-E + -((d₁ + ℓ) * Δ)) := by
          rw [Real.rpow_add hN0 (-E)]; ring
      _ ≤ (p.κ ^ 2)⁻¹ * Q * Nk ^ (-fd + (-nd - 2 * δ₀ * L)) := by
          apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNk hE1)
          positivity
      _ = Nk ^ (-fd) * (Q * Nk ^ (-nd - 2 * δ₀ * L)) / p.κ ^ 2 := by
          rw [Real.rpow_add hN0 (-fd)]; field_simp
      _ ≤ Nk ^ (-fd) * (|(p.frame b).det| / |(p.frame b₀).det|) / p.κ ^ 2 := by
          gcongr
      _ ≤ _ := hr1
  · calc (ν (p.world b) (p.assigned b)).toReal / (ν (p.world b) (p.assigned b₀)).toReal
        ≤ p.κ ^ 2 * Nk ^ (-fd) * (|(p.frame b).det| / |(p.frame b₀).det|) := hr2
      _ ≤ p.κ ^ 2 * Nk ^ (-fd) * (Q * Nk ^ (-nd + 2 * δ₀ * L)) := by gcongr
      _ = p.κ ^ 2 * Q * Nk ^ (-fd + (-nd + 2 * δ₀ * L)) := by
          rw [Real.rpow_add hN0 (-fd)]; ring
      _ ≤ p.κ ^ 2 * Q * Nk ^ (E + -((d₁ + ℓ) * Δ)) := by
          apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNk hE2)
          positivity
      _ = p.κ ^ 2 * Nk ^ E * (Q * Nk ^ (-((d₁ + ℓ) * Δ))) := by
          rw [Real.rpow_add hN0 E]; ring

/-- **The model prior field.** For a label `b` of the depth-`x` level below the parent `b₀`,
the conditioned prior is `(Nst^(-x))^d₁ (2^(-ΔT))² Nst^(-ℓ x)` within `K`, once
`κ² Nk^E ≤ K` for the profile and narrowness error `E`. -/
theorem prior_field (hNk : 1 ≤ Nk) {u x K E d₁ : ℝ} (b₀ b : Fin p.C)
    [IsFiniteMeasure (ν (p.world b))] (hw : p.world b₀ = p.world b)
    (hT : p.T (p.lev b₀) ≤ p.T (p.lev b))
    (hAm : MeasurableSet (p.assigned b)) (hsub : p.assigned b ⊆ p.assigned b₀)
    (hf : |f (p.r (p.lev b)) - f (p.r (p.lev b₀)) - d₁ * (u * L * x)| +
      |p.nw (p.lev b) - p.nw (p.lev b₀) - ℓ * (u * L * x)| + 2 * δ₀ * L ≤ E)
    (hK : p.κ ^ 2 * Nk ^ E ≤ K) :
    ENNReal.ofReal (((Nk ^ (u * L)) ^ (-x)) ^ d₁ *
        ((2 : ℝ) ^ (-((p.T (p.lev b) - p.T (p.lev b₀) : ℕ) : ℤ))) ^ 2 *
        (Nk ^ (u * L)) ^ (-ℓ * x) / K) ≤
      nuE (ν (p.world b)) (p.assigned b₀) (p.assigned b) ∧
    nuE (ν (p.world b)) (p.assigned b₀) (p.assigned b) ≤
      ENNReal.ofReal (K * ((Nk ^ (u * L)) ^ (-x)) ^ d₁ *
        ((2 : ℝ) ^ (-((p.T (p.lev b) - p.T (p.lev b₀) : ℕ) : ℤ))) ^ 2 *
        (Nk ^ (u * L)) ^ (-ℓ * x)) := by
  have hN0 : 0 < Nk := by linarith
  have hκ := hp.one_le_slack
  obtain ⟨hlo, hhi⟩ := prior_ratio_bounds hp hNk b₀ b hw hT hf
  -- the target as a power of `Nk`
  set Q := (4 : ℝ)⁻¹ ^ (p.T (p.lev b) - p.T (p.lev b₀))
  have hX : ((Nk ^ (u * L)) ^ (-x)) ^ d₁ *
      ((2 : ℝ) ^ (-((p.T (p.lev b) - p.T (p.lev b₀) : ℕ) : ℤ))) ^ 2 *
      (Nk ^ (u * L)) ^ (-ℓ * x) = Q * Nk ^ (-((d₁ + ℓ) * (u * L * x))) := by
    have h1 : ((Nk ^ (u * L)) ^ (-x)) ^ d₁ = Nk ^ (-(d₁ * (u * L * x))) := by
      rw [← Real.rpow_mul hN0.le, ← Real.rpow_mul hN0.le]; congr 1; ring
    have h2 : (Nk ^ (u * L)) ^ (-ℓ * x) = Nk ^ (-(ℓ * (u * L * x))) := by
      rw [← Real.rpow_mul hN0.le]; congr 1; ring
    have h3 : ((2 : ℝ) ^ (-((p.T (p.lev b) - p.T (p.lev b₀) : ℕ) : ℤ))) ^ 2 = Q := by
      rw [zpow_neg, zpow_natCast, inv_pow, ← pow_mul, mul_comm, pow_mul]
      norm_num [Q]
    rw [h1, h2, h3, mul_comm _ Q, mul_assoc, ← Real.rpow_add hN0]
    congr 2; ring
  have hassoc : K * ((Nk ^ (u * L)) ^ (-x)) ^ d₁ *
      ((2 : ℝ) ^ (-((p.T (p.lev b) - p.T (p.lev b₀) : ℕ) : ℤ))) ^ 2 *
      (Nk ^ (u * L)) ^ (-ℓ * x) = K * (((Nk ^ (u * L)) ^ (-x)) ^ d₁ *
      ((2 : ℝ) ^ (-((p.T (p.lev b) - p.T (p.lev b₀) : ℕ) : ℤ))) ^ 2 *
      (Nk ^ (u * L)) ^ (-ℓ * x)) := by ring
  rw [hassoc, hX]
  set X := Q * Nk ^ (-((d₁ + ℓ) * (u * L * x)))
  have hXpos : 0 < X := by positivity
  have hfin : ν (p.world b) (p.assigned b₀) ≠ ⊤ := measure_ne_top _ _
  have hreal := toReal_nuE_apply_subset (ν (p.world b)) (p.assigned b₀) (p.assigned b) hAm hsub
  have hnuE_fin : nuE (ν (p.world b)) (p.assigned b₀) (p.assigned b) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hreal
    have hA₁ : 0 < (ν (p.world b) (p.assigned b)).toReal := by
      have := (assigned_prior_bounds hp b hN0).1
      exact lt_of_lt_of_le (div_pos (mul_pos (Real.rpow_pos_of_pos hN0 _)
        (abs_pos.mpr (hp.chart b).1)) (by linarith)) this
    have hfin0 : IsFiniteMeasure (ν (p.world b₀)) := by rw [hw]; infer_instance
    have hA₀ : 0 < (ν (p.world b) (p.assigned b₀)).toReal := by
      have := (assigned_prior_bounds hp b₀ hN0).1
      rw [hw] at this
      exact lt_of_lt_of_le (div_pos (mul_pos (Real.rpow_pos_of_pos hN0 _)
        (abs_pos.mpr (hp.chart b₀).1)) (by linarith)) this
    have : (0 : ℝ) < (ν (p.world b) (p.assigned b)).toReal / (ν (p.world b) (p.assigned b₀)).toReal :=
      div_pos hA₁ hA₀
    linarith
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  constructor
  · rw [ENNReal.ofReal_le_iff_le_toReal hnuE_fin, hreal]
    calc X / K ≤ (p.κ ^ 2)⁻¹ * Nk ^ (-E) * X := by
          rw [div_le_iff₀ hK0]
          have hκE : 0 < p.κ ^ 2 * Nk ^ E := by positivity
          calc X = ((p.κ ^ 2)⁻¹ * Nk ^ (-E) * X) * (p.κ ^ 2 * Nk ^ E) := by
                rw [Real.rpow_neg hN0.le]; field_simp
            _ ≤ ((p.κ ^ 2)⁻¹ * Nk ^ (-E) * X) * K := by gcongr
      _ ≤ _ := hlo
  · rw [← ENNReal.ofReal_toReal hnuE_fin]
    apply ENNReal.ofReal_le_ofReal
    rw [hreal]
    calc _ ≤ p.κ ^ 2 * Nk ^ E * X := hhi
      _ ≤ K * X := by gcongr

/-- **Profile and narrowness errors along the source depth map.** -/
theorem prior_error (hm : 0 < m) {i₀ : ℕ} (hi₀ : i₀ < m) {u mesh d₁ : ℝ} (hu : 0 ≤ u)
    (hmesh0 : 0 ≤ mesh) (hmesh : ∀ i, i + 1 < m → sg (i + 1) - sg i ≤ mesh)
    (hroom : sg i₀ + u ≤ sg (m - 1)) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁) (hℓ : 0 ≤ ℓ)
    (hprof : ∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hr0L : p.r i₀ ≤ L) (hrjL : p.r (sourceDepth m sg i₀ u x) ≤ L) :
    |f (p.r (sourceDepth m sg i₀ u x)) - f (p.r i₀) - d₁ * (u * L * x)| +
      |p.nw (sourceDepth m sg i₀ u x) - p.nw i₀ - ℓ * (u * L * x)| + 2 * δ₀ * L ≤
      (6 * δ₀ + d₁ * (mesh + 2 * δ₀) + ℓ * mesh) * L := by
  set j := sourceDepth m sg i₀ u x
  have hj : j < m := sourceDepth_lt hm sg i₀ u x
  obtain ⟨hact, -⟩ := sourceDepth_actual hp hm hi₀ hu hmesh0 hmesh hroom hL hx0 hx1
  obtain ⟨hlo, hhi⟩ := sourceDepth_nominal hm hi₀ hu hmesh0 hmesh hroom hx0 hx1
  obtain ⟨-, hrj0, -, -, hnwj, -⟩ := hp.level_bounds j hj
  obtain ⟨-, hri0, -, -, hnwi, -⟩ := hp.level_bounds i₀ hi₀
  have hfj := hprof (p.r j) hrj0.le hrjL
  have hfi := hprof (p.r i₀) hri0.le hr0L
  -- profile part
  have hF : |f (p.r j) - f (p.r i₀) - d₁ * (u * L * x)| ≤ 2 * δ₀ * L + d₁ * ((mesh + 2 * δ₀) * L) := by
    have e : f (p.r j) - f (p.r i₀) - d₁ * (u * L * x) =
        (f (p.r j) - f 0 - d₁ * p.r j) - (f (p.r i₀) - f 0 - d₁ * p.r i₀) +
          d₁ * (p.r j - p.r i₀ - u * L * x) := by ring
    rw [e]
    calc _ ≤ |(f (p.r j) - f 0 - d₁ * p.r j) - (f (p.r i₀) - f 0 - d₁ * p.r i₀)| +
          |d₁ * (p.r j - p.r i₀ - u * L * x)| := abs_add_le _ _
      _ ≤ (|f (p.r j) - f 0 - d₁ * p.r j| + |f (p.r i₀) - f 0 - d₁ * p.r i₀|) +
          d₁ * |p.r j - p.r i₀ - u * L * x| := by
            gcongr
            · exact abs_sub _ _
            · rw [abs_mul, abs_of_nonneg hd₁]
      _ ≤ (δ₀ * L + δ₀ * L) + d₁ * ((mesh + 2 * δ₀) * L) := by gcongr
      _ = _ := by ring
  -- narrowness part
  have hN : |p.nw j - p.nw i₀ - ℓ * (u * L * x)| ≤ 2 * δ₀ * L + ℓ * (mesh * L) := by
    have e : p.nw j - p.nw i₀ - ℓ * (u * L * x) =
        (p.nw j - ℓ * sg j * L) - (p.nw i₀ - ℓ * sg i₀ * L) + ℓ * L * (sg j - sg i₀ - u * x) := by
      ring
    have hs : |sg j - sg i₀ - u * x| ≤ mesh := by
      rw [abs_le]; constructor <;> linarith
    rw [e]
    calc _ ≤ |(p.nw j - ℓ * sg j * L) - (p.nw i₀ - ℓ * sg i₀ * L)| +
          |ℓ * L * (sg j - sg i₀ - u * x)| := abs_add_le _ _
      _ ≤ (|p.nw j - ℓ * sg j * L| + |p.nw i₀ - ℓ * sg i₀ * L|) +
          ℓ * L * |sg j - sg i₀ - u * x| := by
            gcongr
            · exact abs_sub _ _
            · rw [abs_mul, abs_of_nonneg (mul_nonneg hℓ hL)]
      _ ≤ (δ₀ * L + δ₀ * L) + ℓ * L * mesh := by gcongr
      _ = _ := by ring
  nlinarith

/-- `prior_field` with the world and the two levels named. -/
theorem prior_field_at (hNk : 1 ≤ Nk) {u x K E d₁ : ℝ} (b₀ b : Fin p.C) (w : Fin W)
    (j₀ j : ℕ) [IsFiniteMeasure (ν w)] (hwb : p.world b = w) (hw : p.world b₀ = w)
    (hj₀ : p.lev b₀ = j₀) (hj : p.lev b = j) (hT : p.T j₀ ≤ p.T j)
    (hAm : MeasurableSet (p.assigned b)) (hsub : p.assigned b ⊆ p.assigned b₀)
    (hf : |f (p.r j) - f (p.r j₀) - d₁ * (u * L * x)| +
      |p.nw j - p.nw j₀ - ℓ * (u * L * x)| + 2 * δ₀ * L ≤ E)
    (hK : p.κ ^ 2 * Nk ^ E ≤ K) :
    ENNReal.ofReal (((Nk ^ (u * L)) ^ (-x)) ^ d₁ *
        ((2 : ℝ) ^ (-((p.T j - p.T j₀ : ℕ) : ℤ))) ^ 2 *
        (Nk ^ (u * L)) ^ (-ℓ * x) / K) ≤ nuE (ν w) (p.assigned b₀) (p.assigned b) ∧
    nuE (ν w) (p.assigned b₀) (p.assigned b) ≤
      ENNReal.ofReal (K * ((Nk ^ (u * L)) ^ (-x)) ^ d₁ *
        ((2 : ℝ) ^ (-((p.T j - p.T j₀ : ℕ) : ℤ))) ^ 2 * (Nk ^ (u * L)) ^ (-ℓ * x)) := by
  subst hwb hj₀ hj
  exact prior_field hp hNk b₀ b hw hT hAm hsub hf hK

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
