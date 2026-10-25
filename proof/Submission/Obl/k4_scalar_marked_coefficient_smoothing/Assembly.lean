import Submission.Obl.k4_scalar_marked_coefficient_smoothing.AnalyticClaims
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Sequence

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set
open scoped ENNReal

theorem DensityCeilings.mono {N K K' d s m S U c : ℝ} {angular : Bool}
    {μ : Measure (Traj × ℝ)} (hN : 0 ≤ N) (hc : 0 ≤ c) (hK : K ≤ K')
    (h : DensityCeilings N K d s m S U c angular μ) :
    DensityCeilings N K' d s m S U c angular μ := by
  rcases h with ⟨hpure, hjoint⟩
  constructor
  · intro r hr hrs
    obtain ⟨g, hg, hmap, hden⟩ := hpure r hr hrs
    refine ⟨g, hg, hmap, ?_⟩
    filter_upwards [hden] with z hz
    apply hz.trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
  · intro r u hr hrs hu huV
    obtain ⟨G, hG, hmap, hden, hang⟩ := hjoint r u hr hrs hu huV
    refine ⟨G, hG, hmap, ?_, ?_⟩
    · filter_upwards [hden] with z hz
      apply hz.trans
      apply ENNReal.ofReal_le_ofReal
      gcongr
    · intro hrs' hangular hup huU
      filter_upwards [hang hrs' hangular hup huU] with z hz
      apply hz.trans
      apply ENNReal.ofReal_le_ofReal
      gcongr

/-- The two analytic children combine into the fixed-model interface used by the
already proved finite construction and sequence assembly. -/
theorem local_raw_bound_of_analytic_children
    (hdensity : DensityTransferClaim) (hsupport : SupportTransferClaim) :
    ∃ A : ℝ, 2 ≤ A ∧ ∃ q : ℕ, 2 ≤ q ∧ LocalRawSmoothingBound A q := by
  obtain ⟨A₁, hA₁, q₁, hdensity⟩ := hdensity
  obtain ⟨A₂, hA₂, q₂, hsupport⟩ := hsupport
  let A := 2 + A₁ + A₂
  let q := q₁ + q₂ + 2
  have hA : 2 ≤ A := by dsimp [A]; linarith
  have hq : 2 ≤ q := by dsimp [q]; omega
  refine ⟨A, hA, q, hq, ?_⟩
  intro N K d s m S U c angular hN hK hd hd1 hs hsm hS hU hUm hc
    α inst ν μ b hinput H J tag b₀ w mark hJ hJlow hJhigh hw hsum hb₀
    htag hweight hround hfloor
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hKp : 0 < K := by linarith
  have hm : 0 < m := hs.trans hsm
  have hδ : 0 < N ^ (-10 * (m + s + 1)) := Real.rpow_pos_of_pos hNp _
  have hσ : 0 < N ^ (-m) := Real.rpow_pos_of_pos hNp _
  have hδσ : N ^ (-10 * (m + s + 1)) ≤ N ^ (-m) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have hσ1 : N ^ (-m) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hσa : N ^ (-m) ≤ N ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hAd : A₁ ≤ A := by dsimp [A]; linarith
  have hAs : A₂ ≤ A := by dsimp [A]; linarith
  have hDloss : A₁ * K ^ q₁ ≤ A * K ^ q := by
    calc
      _ ≤ A * K ^ q₁ := mul_le_mul_of_nonneg_right hAd (by positivity)
      _ ≤ A * K ^ q := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hK (by dsimp [q]; omega)) (by linarith)
  have hSloss : A₂ * K ^ q₂ * K ≤ A * K ^ q := by
    calc
      _ = A₂ * K ^ (q₂ + 1) := by rw [pow_succ]; ring
      _ ≤ A * K ^ (q₂ + 1) := mul_le_mul_of_nonneg_right hAs (by positivity)
      _ ≤ A * K ^ q := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hK (by dsimp [q]; omega)) (by linarith)
  have hden := hdensity N K d s m S U c hN hK hd hd1 hs hsm hS hU hUm hc
    α ν μ b angular hinput H J tag b₀ w mark hJ hJlow hJhigh hw hsum hb₀
    ⟨htag, hweight, hround, hfloor⟩
  have hden' := DensityCeilings.mono hNp.le hc.le hDloss hden
  rcases hinput with ⟨hb, hprob, hdom, htimes, hmass, hbound, hcap,
    ⟨F, hFbudget, hFsupport⟩, hangular⟩
  obtain ⟨B, hB, hBvol, hBsupport⟩ := hsupport K (N ^ (-m)) (N ^ (-s))
    (N ^ (-10 * (m + s + 1))) hK hδ hδσ hσ hσ1 hσa
    α μ b hb hbound H J tag b₀ w mark hJ hJlow hJhigh htag hw hround hfloor F hFsupport
  have hpower : (N ^ (-s)) ^ (-d) = N ^ (d * s) := by
    rw [← Real.rpow_mul hNp.le]
    congr 1
    ring
  have hbudget : A₂ * K ^ q₂ * ((F.card : ℝ) * (N ^ (-m)) ^ 2) ≤
      (A * K ^ q) * c⁻¹ * N ^ (d * s) := by
    calc
      _ ≤ A₂ * K ^ q₂ * (K * c⁻¹ * N ^ (d * s)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [hpower] using hFbudget
        · positivity
      _ = (A₂ * K ^ q₂ * K) * c⁻¹ * N ^ (d * s) := by ring
      _ ≤ _ := by gcongr
  exact ⟨hden'.1, hden'.2, B, hB,
    hBvol.trans (ENNReal.ofReal_le_ofReal hbudget), hBsupport⟩

theorem smoothing_of_analytic_children
    (hdensity : DensityTransferClaim) (hsupport : SupportTransferClaim) :
    SmoothingStatement := by
  obtain ⟨A, hA, q, hq, hraw⟩ :=
    local_raw_bound_of_analytic_children hdensity hsupport
  exact smoothing_of_local_raw_bound hA hq hraw

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
