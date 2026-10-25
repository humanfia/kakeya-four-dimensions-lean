-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2BlockFit, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2BlockFit.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2BlockFit.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2BlockFit.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Search
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAffineTransport
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLocalFitConstants
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

set_option autoImplicit false

/-!
# Uniform affine fitting of one row component on a block, version 2

The `j = 2` counterpart of `uniform_original_scalar_block_affine_fit` of o078 (session x0662,
branch `x0662` at `f2bac599`, `ScalarUniformBlockFit.lean`); paper `tex-05`, proof of
Prop. `prop:scalar-normal`, "Fitting one row component": after slicing the other tangential
coordinate (`V2Search`, `V2Observations`, `V2Caps`), x0662's planar kernel
`uniform_original_scalar_affine_fit` (WangZahlLot's projection dichotomy) fits the component
`F · e_i` of the row by an affine function on labelled times of the block of length
`≥ H N^(-τ)`, with error `41 K² H p`, `p = N^(-exponent) ≥ H`.

The kernel enters through `LocalFitStatement` (its exact statement), discharged in
`V2BlockFitKernel.lean`; this keeps the present file free of the heavy planar imports.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

/-- The statement of x0662's planar kernel `uniform_original_scalar_affine_fit`
(`ScalarUniformLocalFit.lean`), verbatim, for one trajectory type. -/
def LocalFitStatement (Λ : Type*) [MeasurableSpace Λ] : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 1 ≤ N k) → Tendsto N atTop atTop → (∀ k, 1 ≤ K k) →
    SubpowerBound N K → ∀ {c d τ : ℝ}, 0 < c → 0 ≤ d → d < 1 → 0 < τ →
    ∀ᶠ k in atTop,
      let p := N k ^ (-c)
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
        (E : Set (ℝ × Λ)) (A : Set Λ) (v Z : Λ → ℝ) (F : ℝ × Λ → ℝ) (f G : ℝ → ℝ)
        (S : ℝ → Set ℝ) (S₀ : Set ℝ),
      μ ≤ volume → MeasurableSet E → E ⊆ Icc (-1 : ℝ) 1 ×ˢ A →
      Measurable v → Measurable Z → Measurable F → f 0 = 0 →
      (∀ u t, |f u - f t| ≤ |u - t|) → (∀ v w, |G v - G w| ≤ K k * |v - w|) →
      (∀ l ∈ A, |v l| ≤ K k ∧ |G (v l)| ≤ K k) →
      (∀ t, IntervalAD p d (K k) (S t)) → IntervalAD p d (K k) S₀ →
      (∀ u l, (u, l) ∈ E → F (u, l) ∈ S u ∩ Icc (-K k) (K k)) →
      (∀ l ∈ A, Z l ∈ S₀ ∩ Icc (-K k) (K k)) →
      (∀ u l, (u, l) ∈ E → |F (u, l) - (Z l + u * G (v l) + f u * v l)| ≤ K k * p) →
      (∀ a b r : ℝ, p ≤ r →
        ν.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ Z l ∈ Icc b (b + r)} ≤ K k * r ^ (1 + d)) →
      (K k)⁻¹ ≤ (μ.prod ν).real E →
      ∃ (T : Set ℝ) (a slope : ℝ), MeasurableSet T ∧ T ⊆ Icc (-1 : ℝ) 1 ∧
        (∀ u ∈ T, ∃ l, (u, l) ∈ E) ∧ ENNReal.ofReal (N k ^ (-τ)) ≤ volume T ∧
        |a| ≤ 9 ∧ |slope| ≤ 4 ∧ ∀ u ∈ T, |f u - (a + slope * u)| ≤ 13 * p

/-- One polynomial bound for all normalized block inputs. -/
def v2BlockFitBound (K : ℝ) : ℝ := 300000 * K ^ 10

theorem v2BlockFitBound_bounds {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ v2BlockFitBound K ∧ K ≤ v2BlockFitBound K ∧ 250000 * K ^ 6 ≤ v2BlockFitBound K ∧
      48 * K ^ 2 ≤ v2BlockFitBound K ∧ 28 * K ^ 2 ≤ v2BlockFitBound K ∧
      6 * K ^ 3 ≤ v2BlockFitBound K ∧ 17 * K ^ 2 ≤ v2BlockFitBound K := by
  have h1 : 1 ≤ K ^ 10 := one_le_pow₀ hK
  have h01 : K ^ 1 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  have h2 : K ^ 2 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  have h3 : K ^ 3 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  have h6 : K ^ 6 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  simp only [pow_one] at h01
  dsimp [v2BlockFitBound]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem v2BlockFitBound_inverse {K : ℝ} (hK : 1 ≤ K) :
    (v2BlockFitBound K)⁻¹ ≤ (K⁻¹) ^ 2 / (250000 * K ^ 6) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have he : (K⁻¹) ^ 2 / (250000 * K ^ 6) = (250000 * K ^ 8)⁻¹ := by
    field_simp
  rw [he]
  apply inv_anti₀ (by positivity)
  have h8 : K ^ 8 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  have h10 : 0 ≤ K ^ 10 := by positivity
  dsimp [v2BlockFitBound]; linarith

theorem measurable_zS_joint {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ}
    (hc : Measurable c) {F : ℝ → Fin 2 → ℝ} (hF : Measurable F) :
    Measurable (fun q : Λ × ℝ => zS F (c q.1) q.2) := by
  have hcomp : ∀ e : Fin 7, Measurable (fun q : Λ × ℝ => c q.1 e) :=
    fun e => (measurable_pi_apply e).comp (hc.comp measurable_fst)
  have hFc : ∀ i : Fin 2, Measurable (fun q : Λ × ℝ => F q.2 i) :=
    fun i => (measurable_pi_apply i).comp (hF.comp measurable_snd)
  have h0 := hcomp 0; have h1 := hcomp 1; have h2 := hcomp 2; have h3 := hcomp 3
  have h4 := hcomp 4; have h5 := hcomp 5; have h6 := hcomp 6
  have hF0 := hFc 0; have hF1 := hFc 1
  simp only [zS, zx, dot_two, zy_zero, zy_one]
  fun_prop

/-- **Uniform affine fitting of one row component on a block** (version 2). -/
theorem uniform_v2_block_affine_fit {Λ : Type*} [MeasurableSpace Λ]
    (hker : LocalFitStatement Λ) (N K : ℕ → ℝ) (hN : ∀ n, 1 ≤ N n) (hNt : Tendsto N atTop atTop)
    (hK : ∀ n, 1 ≤ K n) (hsub : SubpowerBound N K)
    {exponent d τ : ℝ} (hexponent : 0 < exponent) (hd0 : 0 ≤ d) (hd : d < 1) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (ν : Measure Λ) [IsProbabilityMeasure ν] (c : Λ → Fin 7 → ℝ)
      (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (ζ H s : ℝ) (i : Fin 2),
      UpperHyp ν c E F (K n) ζ d → 0 < ζ → 0 < H → H ≤ 1 →
      H ≤ N n ^ (-exponent) → ζ ≤ H ^ 2 → E ⊆ univ ×ˢ Icc s (s + H) →
      H / K n ≤ (ν.prod volume).real E →
      ∃ (T : Set ℝ) (a slope : ℝ), MeasurableSet T ∧ T ⊆ Icc s (s + H) ∧
        T ⊆ activeTimes E ∧ ENNReal.ofReal (H * N n ^ (-τ)) ≤ volume T ∧
        |a| ≤ 40 * K n ^ 2 ∧ |slope| ≤ 40 * K n ^ 2 ∧
        ∀ t ∈ T, |F t i - (a + slope * t)| ≤ 41 * K n ^ 2 * H * N n ^ (-exponent) := by
  let B : ℕ → ℝ := fun n => v2BlockFitBound (K n)
  have hB : ∀ n, 1 ≤ B n := fun n => (v2BlockFitBound_bounds (hK n)).1
  have hBsub : SubpowerBound N B := by
    exact subpower_mul (fun n => zero_lt_one.trans_le (hN n))
      (fun _ => by norm_num) (fun n => pow_nonneg (zero_le_one.trans (hK n)) 10)
      (subpower_const hNt 300000) (subpower_pow hN (fun n => zero_le_one.trans (hK n)) hsub 10)
  filter_upwards [hker N B hN hNt hB hBsub hexponent hd0 hd hτ] with n hn
  intro ν _ c E F ζ H s i h hζ hH hH1 hHp hζH2 hblock hmass
  set p := N n ^ (-exponent) with hpdef
  have hp : 0 < p := Real.rpow_pos_of_pos (zero_lt_one.trans_le (hN n)) _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN n) (by linarith)
  have hKpos : 0 < K n := zero_lt_one.trans_le (hK n)
  have hK0 : 0 ≤ K n := hKpos.le
  have hKsq : K n ≤ K n ^ 2 := by nlinarith [hK n]
  have hζH : ζ ≤ H := hζH2.trans (by nlinarith)
  have hζHp : ζ ≤ H * p := hζH2.trans (by nlinarith)
  obtain ⟨anchor, b, hanchor, hc, hprior, hselected⟩ :=
    exists_v2_block_search h (hK n) hd0 hd.le hH hH1 hζH hHp hp1 i hblock hmass
  set t₀ := s + H * anchor with ht₀
  let A := slicedLabels c F E t₀ H p i b
  let νb := slicedPrior ν c F E t₀ H p d i b
  let μ := scalarIntervalTime (-anchor)
  letI : IsProbabilityMeasure μ := scalarIntervalTime_probability _
  letI : IsFiniteMeasure νb := slicedPrior_finite ν c F E t₀ H p d i b
  let E' := scalarCenteredEvent E A t₀ H
  have hA : MeasurableSet A :=
    slicedLabels_measurable h.measurable_c h.event_measurable F t₀ H p i b
  have hE' : MeasurableSet E' := scalarCenteredEvent_measurable h.event_measurable hA t₀ H
  have hcblock : t₀ ∈ Icc s (s + H) := by
    rw [ht₀]; constructor <;> nlinarith [hanchor.1, hanchor.2]
  have hE'unit : E' ⊆ Icc (-1 : ℝ) 1 ×ˢ A := scalarCenteredEvent_unit hH hcblock hblock
  obtain ⟨g, G, hgc, hnear, hgcont, hf0, hf, hG, hbound, hmodel⟩ :=
    exists_v2_block_observations h (hK n) hH hH1 hζ.le hζH2 hHp hp1 hc i b
  let v := scaledFitted c (K n) t₀ i
  let Z := slicedStart c F t₀ H b
  let Obs := slicedObs c g F t₀ H p i b
  let f := fittedRow g F t₀ H (K n) i
  let S' := slicedSupport c g F E t₀ H p i b
  obtain ⟨hB1, hKB, hpriorB, hObsB, herrB, hvB, hGB⟩ := v2BlockFitBound_bounds (hK n)
  have hS' (u : ℝ) : IntervalAD p d (B n) (S' u) :=
    CellProofs.Assouad.mono_constant hp (slicedSupport_AD hζ hH hζHp h.support_AD u) hKB
  have hv : Measurable v := (measurable_zy_at h.measurable_c t₀ i).const_mul _
  have hZ : Measurable Z :=
    ((measurable_zS_at h.measurable_c F t₀).sub_const (H * b.1)).div_const H
  have hObs : Measurable Obs := by
    have hzS := measurable_zS_joint h.measurable_c h.row_measurable
    have h1 : Measurable (fun q : ℝ × Λ => zS F (c q.2) (t₀ + H * q.1)) :=
      hzS.comp (measurable_snd.prodMk (measurable_const.add (measurable_const.mul measurable_fst)))
    have hgk : Measurable (fun u : ℝ => g (t₀ + H * u) (Fin.rev i)) :=
      ((hgcont (Fin.rev i)).comp (continuous_const.add (continuous_const.mul continuous_id))).measurable
    have h2 : Measurable (fun q : ℝ × Λ => sliceShift g F t₀ H p i b q.1) := by
      have : Measurable (fun u : ℝ => sliceShift g F t₀ H p i b u) := by
        simp only [sliceShift, normRow, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        exact ((hgk.sub_const _).const_mul _).mul_const _
      exact this.comp measurable_fst
    exact ((h1.sub_const _).div_const H).add h2
  have hGb (x y : ℝ) : |G x - G y| ≤ B n * |x - y| :=
    (hG x y).trans (le_mul_of_one_le_left (abs_nonneg _) (hB n))
  have hvs (l : Λ) (hl : l ∈ A) : |v l| ≤ B n ∧ |G (v l)| ≤ B n :=
    ⟨((hbound l hl).1).trans hvB, ((hbound l hl).2.1).trans hGB⟩
  have hcurrent u l (hl : (u, l) ∈ E') : Obs (u, l) ∈ S' u ∩ Icc (-(B n)) (B n) := by
    have hu : |u| ≤ 1 := abs_le.mpr (hE'unit hl).1
    exact ⟨slicedObs_mem hH u l hl.1,
      abs_le.mp (((hmodel u l hu hl.2.2 hl.1).1).trans hObsB)⟩
  have hstart l (hl : l ∈ A) : Z l ∈ S' 0 ∩ Icc (-(B n)) (B n) := by
    have hz := (hbound l hl).2.2
    have hzbound : |Z l| ≤ B n := (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩).trans hB1
    refine ⟨?_, abs_le.mp hzbound⟩
    have hmem := slicedObs_mem (c := c) (g := g) (F := F) (E := E) (t₀ := t₀) (H := H) (p := p)
      (k := i) (b := b) hH 0 l (by simpa using hl.1)
    rwa [slicedStart_eq_obs hgc] at hmem
  have herror u l (hl : (u, l) ∈ E') :
      |Obs (u, l) - (Z l + u * G (v l) + f u * v l)| ≤ B n * p :=
    ((hmodel u l (abs_le.mpr (hE'unit hl).1) hl.2.2 hl.1).2).trans
      (mul_le_mul_of_nonneg_right herrB hp.le)
  have hjoint a b' r (hr : p ≤ r) :
      νb.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ Z l ∈ Icc b' (b' + r)} ≤ B n * r ^ (1 + d) := by
    have hcap := sliced_group_joint_cap h (hK n) hd0 hd.le hH hH1 hHp hζHp t₀ i b hprior a b' r hr
    exact hcap.trans (mul_le_mul_of_nonneg_right hpriorB
      (Real.rpow_nonneg (hp.le.trans hr) _))
  have hmass' : (B n)⁻¹ ≤ (μ.prod νb).real E' :=
    (v2BlockFitBound_inverse (hK n)).trans hselected
  obtain ⟨U, a, slope, hUm, hUunit, hUactive, hUvol, ha, hslope, hfit⟩ :=
    hn μ νb E' A v Z Obs f G S' (S' 0) (scalarIntervalTime_le_volume _) hE' hE'unit
      hv hZ hObs hf0 hf hGb hvs hS' (hS' 0) hcurrent hstart herror hjoint hmass'
  let L := graphScale (K n)
  have hL : 0 < L := by dsimp [L, graphScale]; positivity
  have hgfit u (hu : u ∈ U) :
      |(g (t₀ + H * u) i - g t₀ i) / (H * L) - (-a + -slope * u)| ≤ 13 * p := by
    have he : (g (t₀ + H * u) i - g t₀ i) / (H * L) - (-a + -slope * u) =
        -(f u - (a + slope * u)) := by
      dsimp [f, fittedRow, normRow, L]
      rw [hgc]
      try simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    rw [he, abs_neg]
    exact hfit u hu
  obtain ⟨hTm, hTvol, hgphysical⟩ :=
    original_affine_fit_transport hUm (fun t => g t i) t₀ (-a) (-slope) hH hL hUvol hgfit
  let T := (fun u => t₀ + H * u) '' U
  let a' := g t₀ i + H * L * -a - L * -slope * t₀
  let slope' := L * -slope
  have hTactive : T ⊆ activeTimes E := by
    rintro t ⟨u, hu, rfl⟩
    obtain ⟨l, hl⟩ := hUactive u hu
    exact ⟨l, hl.1⟩
  have hTblock : T ⊆ Icc s (s + H) := by
    rintro t ⟨u, hu, rfl⟩
    obtain ⟨l, hl⟩ := hUactive u hu
    exact (hblock hl.1).2
  have hcunit : |t₀| ≤ 1 := by
    have ht := h.active_unit_time hc
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hgt₀ : |g t₀ i| ≤ K n := by
    rw [hgc]; exact (abs_le_norm (F t₀) i).trans (h.row_bounded t₀)
  have hcoeff := original_affine_fit_coefficients hH.le hH1 hL.le hgt₀ hcunit
    (show |-a| ≤ 9 by simpa only [abs_neg] using ha)
    (show |-slope| ≤ 4 by simpa only [abs_neg] using hslope)
  have hab : |a'| ≤ 40 * K n ^ 2 := hcoeff.2.trans (by dsimp [L, graphScale]; nlinarith)
  have hsb : |slope'| ≤ 40 * K n ^ 2 := hcoeff.1.trans (by dsimp [L, graphScale]; nlinarith)
  refine ⟨T, a', slope', hTm, hTblock, hTactive, hTvol, hab, hsb, ?_⟩
  intro t ht
  have hng : |F t i - g t i| ≤ 2 * K n * ζ := by
    have := abs_le_norm (F t - g t) i
    simp only [Pi.sub_apply] at this
    exact this.trans (by rw [norm_sub_rev]; exact hnear t (hTactive ht))
  have hphys : |g t i - (a' + slope' * t)| ≤ 39 * K n ^ 2 * (H * p) := by
    have hh := hgphysical t ht
    calc |g t i - (a' + slope' * t)| =
          |(fun t => g t i) t - (((fun t => g t i) t₀ + H * L * -a - L * -slope * t₀) +
            (L * -slope) * t)| := rfl
      _ ≤ H * L * (13 * p) := hh
      _ = 39 * K n ^ 2 * (H * p) := by dsimp [L, graphScale]; ring
  have hnζ : 2 * K n * ζ ≤ 2 * K n * (H * p) := mul_le_mul_of_nonneg_left hζHp (by positivity)
  have hnK : 2 * K n * (H * p) ≤ 2 * K n ^ 2 * (H * p) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hH.le hp.le)
  have htriangle := abs_sub_le (F t i) (g t i) (a' + slope' * t)
  change |F t i - (a' + slope' * t)| ≤ 41 * K n ^ 2 * H * p
  have e41 : 41 * K n ^ 2 * H * p = 39 * K n ^ 2 * (H * p) + 2 * K n ^ 2 * (H * p) := by ring
  rw [e41]
  linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
