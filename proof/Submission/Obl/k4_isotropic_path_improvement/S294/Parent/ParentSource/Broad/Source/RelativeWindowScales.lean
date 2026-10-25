-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RelativeWindowScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/RelativeWindowScales.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FixedLateClock

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Native MeasureTheory

noncomputable section

/-- Relative physical thickness has only the two path errors and the
single dyadic rounding factor. No absolute ancestor depth occurs. -/
theorem Native.PathData.Valid.relative_parent_width_bounds
    {W : ℕ} {p : PathData W} {N L κ₁ δ₀ σ : ℝ}
    {m Mp Dp : ℕ} {s : ℕ → ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 1 ≤ N) (root old : ℕ) (hroot : root < m) (hold : old < m) :
    N^(-((s old-s root+2*δ₀)*L))/2 ≤ δ N (p.r old)/δ N (p.r root) ∧
    δ N (p.r old)/δ N (p.r root) ≤ 2*N^(-((s old-s root-2*δ₀)*L)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hr := abs_le.mp (hp.2.2.2.2.1 root hroot).1
  have ho := abs_le.mp (hp.2.2.2.2.1 old hold).1
  obtain ⟨hrLo,hrHi⟩ := Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp (p.r root)
  obtain ⟨hoLo,hoHi⟩ := Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp (p.r old)
  have hrootPos : 0 < δ N (p.r root) := by unfold δ; positivity
  have holdPos : 0 < δ N (p.r old) := by unfold δ; positivity
  have hlo : N^(-((s old-s root+2*δ₀)*L)) ≤ N^(-(p.r old))/N^(-(p.r root)) := by
    rw [←Real.rpow_sub hNp]
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith only [hr.1,ho.2]
  have hhi : N^(-(p.r old))/N^(-(p.r root)) ≤ N^(-((s old-s root-2*δ₀)*L)) := by
    rw [←Real.rpow_sub hNp]
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith only [hr.2,ho.1]
  constructor
  · calc
      _ ≤ (N^(-(p.r old))/N^(-(p.r root)))/2 := div_le_div_of_nonneg_right hlo (by norm_num)
      _ = N^(-(p.r old))/(2*N^(-(p.r root))) := by ring
      _ ≤ δ N (p.r old)/(2*N^(-(p.r root))) := div_le_div_of_nonneg_right hoLo (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left holdPos.le hrootPos hrHi
  · calc
      _ ≤ (2*N^(-(p.r old)))/δ N (p.r root) := div_le_div_of_nonneg_right hoHi hrootPos.le
      _ ≤ (2*N^(-(p.r old)))/N^(-(p.r root)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hrLo
      _ = 2*(N^(-(p.r old))/N^(-(p.r root))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hhi (by norm_num)

/-- Fix one integer lag before every path and EVERY ancestor in the
first half of the supplied grid. Its exact relative dyadic clock is
Q^(-clockExponent), up to the already allowed subpower envelope.
The exponent is fixed before the fine grid or the ancestor is supplied. -/
theorem WidePreparationGrid.exists_relative_window_scales
    {κ₁ ρ S η χ windowFactor clockExponent : ℝ}
    (q : WidePreparationGrid κ₁ ρ S η χ windowFactor)
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hclock : 1 ≤ clockExponent)
    (hχ1 : χ ≤ 1)
    (hfirst : (q.m : ℝ)⁻¹+2*q.δ₀ ≤ χ*q.gain)
    (hsmall : ((clockExponent/κ₁)+4)*q.gain ≤ 1/8) :
    ∃ lag : ℕ, 0 < lag ∧
      (clockExponent/κ₁)*q.gain ≤ (lag : ℝ)/(q.m : ℝ) ∧
      (lag : ℝ)/(q.m : ℝ) ≤ (clockExponent/κ₁)*q.gain+(q.m : ℝ)⁻¹ ∧
      (∀ root : ℕ, transferScale q.m root ≤ 1/2 →
        root < root+lag ∧ root+lag<q.m ∧
        transferScale q.m (root+lag) ≤ 5/8 ∧
        transferScale q.m (root+lag)-transferScale q.m root=(lag : ℝ)/(q.m : ℝ)) ∧
      ∀ {W : ℕ} {N L σ : ℝ} {p : PathData W}
        {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
        {B : Fin W → ℝ} {f : ℝ → ℝ} {Mp Dp : ℕ},
      p.Valid N L ω ν E B f κ₁ q.m (transferScale q.m) q.δ₀ Mp Dp σ →
      1 ≤ N → 0 ≤ L → ∀ K : ℝ, N^(χ*q.gain*L) ≤ K →
      ∀ root : ℕ, transferScale q.m root ≤ 1/2 →
        p.T root ≤ p.T (root+lag) ∧
        (N^(q.gain*L))^(-clockExponent)/K ≤ ((2 : ℝ)^(p.T (root+lag)-p.T root))⁻¹ ∧
        ((2 : ℝ)^(p.T (root+lag)-p.T root))⁻¹ ≤ K*(N^(q.gain*L))^(-clockExponent) ∧
        p.r (root+lag)+2*q.gain*L ≤ L := by
  let A := clockExponent/κ₁
  let lag := ⌈A*q.gain*(q.m : ℝ)⌉₊
  have hg : 0 < q.gain := q.valid.2.1
  have hδ : 0 < q.δ₀ := q.valid.2.2.2.1
  have hmR : (0 : ℝ) < q.m := Nat.cast_pos.mpr q.valid.1.1
  have hA : 0 < A := by dsimp [A]; positivity
  have hceilLo : A*q.gain*(q.m : ℝ) ≤ (lag : ℝ) := Nat.le_ceil _
  have hceilHi : (lag : ℝ) < A*q.gain*(q.m : ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hlo : A*q.gain ≤ (lag : ℝ)/(q.m : ℝ) := (le_div_iff₀ hmR).mpr hceilLo
  have hhi : (lag : ℝ)/(q.m : ℝ) ≤ A*q.gain+(q.m : ℝ)⁻¹ := by
    apply (div_le_iff₀ hmR).mpr
    have hi : (q.m : ℝ)⁻¹*(q.m : ℝ)=1 := inv_mul_cancel₀ hmR.ne'
    nlinarith only [hceilHi,hi]
  have hlag : 0 < lag := by
    have hh : (0 : ℝ) < lag := (by positivity : 0 < A*q.gain*(q.m : ℝ)).trans_le hceilLo
    exact_mod_cast hh
  have hinv : 0 ≤ (q.m : ℝ)⁻¹ := by positivity
  have hχg : χ*q.gain ≤ q.gain := mul_le_of_le_one_left hg.le hχ1
  have hfirstg : (q.m : ℝ)⁻¹ ≤ q.gain := by linarith only [hfirst,hδ,hχg]
  have herror : κ₁*(q.m : ℝ)⁻¹+2*q.δ₀ ≤ χ*q.gain := by
    linarith only [hfirst,mul_le_of_le_one_left hinv hκ1]
  have hκA : κ₁*(A*q.gain)=clockExponent*q.gain := by dsimp [A]; field_simp
  have hrelLo : clockExponent*q.gain ≤ κ₁*((lag : ℝ)/(q.m : ℝ)) := by
    simpa only [hκA] using mul_le_mul_of_nonneg_left hlo hκ.le
  have hrelHi : κ₁*((lag : ℝ)/(q.m : ℝ)) ≤ clockExponent*q.gain+κ₁*(q.m : ℝ)⁻¹ := by
    have hh := mul_le_mul_of_nonneg_left hhi hκ.le
    rwa [mul_add,hκA] at hh
  have hdiff (root : ℕ) : transferScale q.m (root+lag)-transferScale q.m root=
      (lag : ℝ)/(q.m : ℝ) := by
    simp only [transferScale,Nat.cast_add]
    ring
  have hlevels (root : ℕ) (hr : transferScale q.m root ≤ 1/2) :
      root < root+lag ∧ root+lag<q.m ∧ transferScale q.m (root+lag) ≤ 5/8 := by
    have hs : transferScale q.m (root+lag)=transferScale q.m root+(lag : ℝ)/(q.m : ℝ) := by
      linarith only [hdiff root]
    have hdepth : transferScale q.m (root+lag) ≤ 5/8 := by
      change (A+4)*q.gain ≤ 1/8 at hsmall
      nlinarith only [hs,hr,hhi,hfirstg,hsmall,hg]
    have hlm : root+lag < q.m := by
      have hh : ((root+lag : ℕ) : ℝ)+1 < q.m := by
        have hh' : transferScale q.m (root+lag)<1 := by linarith only [hdepth]
        exact (div_lt_one hmR).mp hh'
      exact_mod_cast (show ((root+lag : ℕ) : ℝ) < q.m by linarith only [hh])
    exact ⟨by omega,hlm,hdepth⟩
  refine ⟨lag,hlag,hlo,hhi,fun root hr => ⟨(hlevels root hr).1,
    (hlevels root hr).2.1,(hlevels root hr).2.2,hdiff root⟩,?_⟩
  intro W N L σ p ω ν E B f Mp Dp hp hN hL K hK root hr
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hKp : 0 < K := (Real.rpow_pos_of_pos hNp _).trans_le hK
  have hold := (hlevels root hr).2.1
  have hroot : root < q.m := lt_trans (hlevels root hr).1 hold
  have hgap : 2*q.δ₀ ≤ κ₁*(transferScale q.m (root+lag)-transferScale q.m root) := by
    rw [hdiff]
    nlinarith only [hrelLo,hclock,mul_le_mul_of_nonneg_right hclock hg.le,hfirst,hχg,hinv]
  obtain ⟨hT,hdyadic⟩ := hp.relative_old_clock_dyadic hN hL root (root+lag) hroot hold hgap
  obtain ⟨hpathLo,hpathHi⟩ := hp.relative_old_clock_bounds hNp root (root+lag) hroot hold
  rw [hdyadic] at hpathLo hpathHi
  rw [hdiff] at hpathLo hpathHi
  have hbase : (N^(q.gain*L))^(-clockExponent)=N^(-(clockExponent*q.gain*L)) := by
    rw [←Real.rpow_mul hNp.le]
    congr 1
    ring
  refine ⟨hT,?_,?_,?_⟩
  · rw [hbase]
    apply le_trans _ hpathLo
    calc
      _ ≤ N^(-(clockExponent*q.gain*L))/N^(χ*q.gain*L) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hK
      _ = N^(-((clockExponent*q.gain+χ*q.gain)*L)) := by
        rw [←Real.rpow_sub hNp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by
        nlinarith only [mul_le_mul_of_nonneg_right (hrelHi.trans
          (by linarith only [herror] : clockExponent*q.gain+κ₁*(q.m : ℝ)⁻¹ ≤
            clockExponent*q.gain+χ*q.gain-2*q.δ₀)) hL])
  · rw [hbase]
    apply hpathHi.trans
    calc
      _ ≤ N^(χ*q.gain*L)*N^(-(clockExponent*q.gain*L)) := by
        rw [←Real.rpow_add hNp]
        apply Real.rpow_le_rpow_of_exponent_le hN
        have hh : clockExponent*q.gain-χ*q.gain ≤
            κ₁*((lag : ℝ)/(q.m : ℝ))-2*q.δ₀ := by
          nlinarith only [hrelLo,hfirst,hinv]
        nlinarith only [mul_le_mul_of_nonneg_right hh hL]
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (by positivity)
  · have hpath := (abs_le.mp (hp.2.2.2.2.1 (root+lag) hold).1).2
    have hδg : q.δ₀ ≤ q.gain := by linarith only [hfirst,hχg,hinv,hδ]
    have hgSmall : 3*q.gain ≤ 1/8 := by
      change (A+4)*q.gain ≤ 1/8 at hsmall
      nlinarith only [hsmall,mul_pos hA hg,hg]
    have hroom : transferScale q.m (root+lag)+q.δ₀+2*q.gain ≤ 1 := by
      linarith only [(hlevels root hr).2.2,hδg,hgSmall]
    nlinarith only [hpath,mul_le_mul_of_nonneg_right hroom hL]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
