-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2RangeFit, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2RangeFit.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2RangeFit.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2RangeFit.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Hierarchy

set_option autoImplicit false

/-!
# Block fitting and the affine hierarchy at power-range meshes, version 2

The planar kernel enters at one resolution `p` through `V2NormalizedFitAt` (the conclusion of
x0662's planar kernel at one `p`, called `OriginalScalarNormalizedFitAt` in x0260's
`ScalarUniformRangeLocalFit.lean`, o078 branch `x0260` at `206ab988`, restated verbatim so that
this file does not import the heavy planar files), and the range form of the kernel through
`RangeFitStatement` (the statement of x0260's
`uniform_original_scalar_affine_fit_between_powers_all_labels` for `Λ : Type`, discharged in
`V2BlockFitKernel.lean`).

* `v2_block_fit_of_normalized_fit`: the version-2 block fit of one row component at one
  resolution (the proof of `uniform_v2_block_affine_fit` of `V2BlockFit.lean`, at fixed `p`);
* `uniform_subpower_v2_block_fit_between_powers`: one subpower duration loss for all
  resolutions `p ∈ [N^-b, N^-a]` (x0260's `ScalarUniformRangeBlockFit.lean`, version 2);
* `uniform_v2_grid_hierarchy_between_powers`: the version-2 affine hierarchy at arbitrary meshes
  `1/J i ∈ [N^-b, N^-a]` with reading scales `(1/J i)^(1/4)` (x0260's
  `ScalarUniformRangeHierarchy.lean`, version 2).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

/-- The conclusion of x0662's planar kernel at one resolution `p` (x0260's
`OriginalScalarNormalizedFitAt`, verbatim). -/
def V2NormalizedFitAt {d : ℝ} (Λ : Type*) [MeasurableSpace Λ] (K p duration : ℝ) : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    (E : Set (ℝ × Λ)) (A : Set Λ) (v Z : Λ → ℝ) (F : ℝ × Λ → ℝ) (f G : ℝ → ℝ)
    (S : ℝ → Set ℝ) (S₀ : Set ℝ),
  μ ≤ volume → MeasurableSet E → E ⊆ Icc (-1 : ℝ) 1 ×ˢ A →
  Measurable v → Measurable Z → Measurable F → f 0 = 0 →
  (∀ u t, |f u - f t| ≤ |u - t|) → (∀ v w, |G v - G w| ≤ K * |v - w|) →
  (∀ l ∈ A, |v l| ≤ K ∧ |G (v l)| ≤ K) →
  (∀ t, IntervalAD p d (K) (S t)) → IntervalAD p d (K) S₀ →
  (∀ u l, (u, l) ∈ E → F (u, l) ∈ S u ∩ Icc (-K) (K)) →
  (∀ l ∈ A, Z l ∈ S₀ ∩ Icc (-K) (K)) →
  (∀ u l, (u, l) ∈ E → |F (u, l) - (Z l + u * G (v l) + f u * v l)| ≤ K * p) →
  (∀ a b r : ℝ, p ≤ r →
    ν.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ Z l ∈ Icc b (b + r)} ≤ K * r ^ (1 + d)) →
  (K)⁻¹ ≤ (μ.prod ν).real E →
  ∃ (T : Set ℝ) (a slope : ℝ), MeasurableSet T ∧ T ⊆ Icc (-1 : ℝ) 1 ∧
    (∀ u ∈ T, ∃ l, (u, l) ∈ E) ∧ ENNReal.ofReal duration ≤ volume T ∧
    |a| ≤ 9 ∧ |slope| ≤ 4 ∧ ∀ u ∈ T, |f u - (a + slope * u)| ≤ 13 * p

/-- The statement of x0260's `uniform_original_scalar_affine_fit_between_powers_all_labels`
(o078, `ScalarUniformRangeLocalFit.lean`) for trajectory types in `Type`. -/
def RangeFitStatement : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 1 ≤ N k) → Tendsto N atTop atTop → (∀ k, 1 ≤ K k) →
    SubpowerBound N K → ∀ {a b d τ : ℝ}, 0 < a → a ≤ b → 0 ≤ d → d < 1 → 0 < τ →
    ∀ᶠ k in atTop, ∀ (Λ : Type) [MeasurableSpace Λ], ∀ p : ℝ, N k ^ (-b) ≤ p →
      p ≤ N k ^ (-a) → V2NormalizedFitAt (d := d) Λ (K k) p (N k ^ (-τ))

/-- **The version-2 block fit at one resolution**, from the planar kernel at that resolution. -/
theorem v2_block_fit_of_normalized_fit {Λ : Type*} [MeasurableSpace Λ] {K p duration d : ℝ}
    (hK : 1 ≤ K) (hp : 0 < p) (hp1 : p ≤ 1) (hd0 : 0 ≤ d) (hd : d < 1)
    (hfit : V2NormalizedFitAt (d := d) Λ (v2BlockFitBound K) p duration) :
    ∀ i, V2BlockFitAt (d := d) Λ K p duration i := by
  set B := v2BlockFitBound K with hBdef
  have hB1' : 1 ≤ B := (v2BlockFitBound_bounds hK).1
  intro i ν _ c E F ζ H s h hζ hH hH1 hHp hζH2 hblock hmass
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hKsq : K ≤ K ^ 2 := by nlinarith [hK]
  have hζH : ζ ≤ H := hζH2.trans (by nlinarith)
  have hζHp : ζ ≤ H * p := hζH2.trans (by nlinarith)
  obtain ⟨anchor, b, hanchor, hc, hprior, hselected⟩ :=
    exists_v2_block_search h hK hd0 hd.le hH hH1 hζH hHp hp1 i hblock hmass
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
    exists_v2_block_observations h hK hH hH1 hζ.le hζH2 hHp hp1 hc i b
  let v := scaledFitted c (K) t₀ i
  let Z := slicedStart c F t₀ H b
  let Obs := slicedObs c g F t₀ H p i b
  let f := fittedRow g F t₀ H (K) i
  let S' := slicedSupport c g F E t₀ H p i b
  obtain ⟨hB1, hKB, hpriorB, hObsB, herrB, hvB, hGB⟩ := v2BlockFitBound_bounds hK
  have hS' (u : ℝ) : IntervalAD p d (B) (S' u) :=
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
  have hGb (x y : ℝ) : |G x - G y| ≤ B * |x - y| :=
    (hG x y).trans (le_mul_of_one_le_left (abs_nonneg _) hB1')
  have hvs (l : Λ) (hl : l ∈ A) : |v l| ≤ B ∧ |G (v l)| ≤ B :=
    ⟨((hbound l hl).1).trans hvB, ((hbound l hl).2.1).trans hGB⟩
  have hcurrent u l (hl : (u, l) ∈ E') : Obs (u, l) ∈ S' u ∩ Icc (-(B)) (B) := by
    have hu : |u| ≤ 1 := abs_le.mpr (hE'unit hl).1
    exact ⟨slicedObs_mem hH u l hl.1,
      abs_le.mp (((hmodel u l hu hl.2.2 hl.1).1).trans hObsB)⟩
  have hstart l (hl : l ∈ A) : Z l ∈ S' 0 ∩ Icc (-(B)) (B) := by
    have hz := (hbound l hl).2.2
    have hzbound : |Z l| ≤ B := (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩).trans hB1
    refine ⟨?_, abs_le.mp hzbound⟩
    have hmem := slicedObs_mem (c := c) (g := g) (F := F) (E := E) (t₀ := t₀) (H := H) (p := p)
      (k := i) (b := b) hH 0 l (by simpa using hl.1)
    rwa [slicedStart_eq_obs hgc] at hmem
  have herror u l (hl : (u, l) ∈ E') :
      |Obs (u, l) - (Z l + u * G (v l) + f u * v l)| ≤ B * p :=
    ((hmodel u l (abs_le.mpr (hE'unit hl).1) hl.2.2 hl.1).2).trans
      (mul_le_mul_of_nonneg_right herrB hp.le)
  have hjoint a b' r (hr : p ≤ r) :
      νb.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ Z l ∈ Icc b' (b' + r)} ≤ B * r ^ (1 + d) := by
    have hcap := sliced_group_joint_cap h hK hd0 hd.le hH hH1 hHp hζHp t₀ i b hprior a b' r hr
    exact hcap.trans (mul_le_mul_of_nonneg_right hpriorB
      (Real.rpow_nonneg (hp.le.trans hr) _))
  have hmass' : (B)⁻¹ ≤ (μ.prod νb).real E' :=
    (v2BlockFitBound_inverse hK).trans hselected
  obtain ⟨U, a, slope, hUm, hUunit, hUactive, hUvol, ha, hslope, hfit⟩ :=
    hfit μ νb E' A v Z Obs f G S' (S' 0) (scalarIntervalTime_le_volume _) hE' hE'unit
      hv hZ hObs hf0 hf hGb hvs hS' (hS' 0) hcurrent hstart herror hjoint hmass'
  let L := graphScale (K)
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
  have hgt₀ : |g t₀ i| ≤ K := by
    rw [hgc]; exact (abs_le_norm (F t₀) i).trans (h.row_bounded t₀)
  have hcoeff := original_affine_fit_coefficients hH.le hH1 hL.le hgt₀ hcunit
    (show |-a| ≤ 9 by simpa only [abs_neg] using ha)
    (show |-slope| ≤ 4 by simpa only [abs_neg] using hslope)
  have hab : |a'| ≤ 40 * K ^ 2 := hcoeff.2.trans (by dsimp [L, graphScale]; nlinarith)
  have hsb : |slope'| ≤ 40 * K ^ 2 := hcoeff.1.trans (by dsimp [L, graphScale]; nlinarith)
  refine ⟨T, a', slope', hTm, hTblock, hTactive, hTvol, hab, hsb, ?_⟩
  intro t ht
  have hng : |F t i - g t i| ≤ 2 * K * ζ := by
    have := abs_le_norm (F t - g t) i
    simp only [Pi.sub_apply] at this
    exact this.trans (by rw [norm_sub_rev]; exact hnear t (hTactive ht))
  have hphys : |g t i - (a' + slope' * t)| ≤ 39 * K ^ 2 * (H * p) := by
    have hh := hgphysical t ht
    calc |g t i - (a' + slope' * t)| =
          |(fun t => g t i) t - (((fun t => g t i) t₀ + H * L * -a - L * -slope * t₀) +
            (L * -slope) * t)| := rfl
      _ ≤ H * L * (13 * p) := hh
      _ = 39 * K ^ 2 * (H * p) := by dsimp [L, graphScale]; ring
  have hnζ : 2 * K * ζ ≤ 2 * K * (H * p) := mul_le_mul_of_nonneg_left hζHp (by positivity)
  have hnK : 2 * K * (H * p) ≤ 2 * K ^ 2 * (H * p) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hH.le hp.le)
  have htriangle := abs_sub_le (F t i) (g t i) (a' + slope' * t)
  change |F t i - (a' + slope' * t)| ≤ 41 * K ^ 2 * H * p
  have e41 : 41 * K ^ 2 * H * p = 39 * K ^ 2 * (H * p) + 2 * K ^ 2 * (H * p) := by ring
  rw [e41]
  linarith

/-- **One subpower duration loss at every resolution of a power range** (version 2). -/
theorem uniform_subpower_v2_block_fit_between_powers (hker : RangeFitStatement)
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) :
    ∃ Q : ℕ → ℝ, (∀ k, 1 ≤ Q k) ∧ SubpowerBound N Q ∧
      ∀ᶠ k in atTop, ∀ (Λ : Type) [MeasurableSpace Λ], ∀ p : ℝ, N k ^ (-b) ≤ p →
        p ≤ N k ^ (-a) → ∀ i, V2BlockFitAt (d := d) Λ (K k) p (Q k)⁻¹ i := by
  let B : ℕ → ℝ := fun k => v2BlockFitBound (K k)
  have hB : ∀ k, 1 ≤ B k := fun k => (v2BlockFitBound_bounds (hK k)).1
  have hBsub : SubpowerBound N B := by
    exact subpower_mul (fun n => zero_lt_one.trans_le (hN n))
      (fun _ => by norm_num) (fun n => pow_nonneg (zero_le_one.trans (hK n)) 10)
      (subpower_const hNt 300000) (subpower_pow hN (fun n => zero_le_one.trans (hK n)) hsub 10)
  obtain ⟨τ, Q, _, _, hQeq, hQ, hQsub, hgood⟩ := exists_uniform_subpower_tolerance N hN
    (fun τ k => ∀ (Λ : Type) [MeasurableSpace Λ], ∀ p : ℝ, N k ^ (-b) ≤ p → p ≤ N k ^ (-a) →
      ∀ i, V2BlockFitAt (d := d) Λ (K k) p (N k ^ (-τ)) i)
    (fun τ hτ => by
      filter_upwards [hker N B hN hNt hB hBsub ha hab hd0 hd hτ] with k hk
      intro Λ _ p hlow hhigh
      have hp : 0 < p :=
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hN k)) _).trans_le hlow
      have hp1 : p ≤ 1 :=
        hhigh.trans (Real.rpow_le_one_of_one_le_of_nonpos (hN k) (by linarith))
      exact v2_block_fit_of_normalized_fit (hK k) hp hp1 hd0 hd (hk Λ p hlow hhigh))
  refine ⟨Q, hQ, hQsub, ?_⟩
  filter_upwards [hgood] with k hk
  have he : N k ^ (-τ k) = (Q k)⁻¹ := by rw [hQeq k, Real.rpow_neg (zero_le_one.trans (hN k))]
  simpa only [he] using hk

/-- **The version-2 affine hierarchy at power-range meshes**, with reading scales
`(1/J i)^(1/4)`. -/
theorem uniform_v2_grid_hierarchy_between_powers (hker : RangeFitStatement)
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) :
    ∀ n : ℕ, ∃ B : ℕ → ℝ, (∀ k, 1 ≤ B k) ∧ (∀ k, K k ≤ B k) ∧ SubpowerBound N B ∧
      ∀ᶠ k in atTop, ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsProbabilityMeasure ν]
        (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (ζ : ℝ)
        (J : Fin n → ℕ) (hJ : ∀ i, 0 < J i),
        UpperHyp ν c E F (K k) ζ d → 0 < ζ → (K k)⁻¹ ≤ (ν.prod volume).real E →
        (∀ i, N k ^ (-b) ≤ 1 / (J i : ℝ)) → (∀ i, 1 / (J i : ℝ) ≤ N k ^ (-a)) →
        (∀ i, ζ ≤ (1 / (J i : ℝ)) ^ 2) →
        Nonempty (V2Hierarchy ν E F J hJ (fun i => (1 / (J i : ℝ)) ^ (1 / 4 : ℝ)) (B k)) := by
  intro n
  induction n with
  | zero =>
      let B : ℕ → ℝ := fun k => 8 * K k
      have hB : ∀ k, 1 ≤ B k := fun k => by simp only [B]; linarith [hK k]
      have hKB : ∀ k, K k ≤ B k := fun k => by simp only [B]; linarith [hK k]
      have hBsub : SubpowerBound N B :=
        subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
          (fun k => zero_le_one.trans (hK k)) (subpower_const hNt 8) hsub
      refine ⟨B, hB, hKB, hBsub, ?_⟩
      filter_upwards [] with k
      intro Λ _ ν _ c E F ζ J hJ h hζ hmass hlow hhigh hζH
      exact exists_initial_v2_hierarchy ν h.event_measurable h.unit_time
        (hK k) hmass F J hJ (fun i => (1 / (J i : ℝ)) ^ (1 / 4 : ℝ))
  | succ n ih =>
      obtain ⟨B, hB, hKB, hBsub, hprevious⟩ := ih
      have h8B : ∀ k, 1 ≤ 8 * B k := fun k => by linarith [hB k]
      have h8Bsub : SubpowerBound N (fun k => 8 * B k) :=
        subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
          (fun k => zero_le_one.trans (hB k)) (subpower_const hNt 8) hBsub
      have ha4 : 0 < a / 4 := by positivity
      have hab4 : a / 4 ≤ b / 4 := by linarith
      obtain ⟨Q₀, hQ₀, hQ₀sub, hlocal₀⟩ := uniform_subpower_v2_block_fit_between_powers
        hker N (fun k => 8 * B k) hN hNt h8B h8Bsub ha4 hab4 hd0 hd
      let B₁ : ℕ → ℝ := fun k => scalarGridStageBound (B k) (Q₀ k)
      have hB₁ : ∀ k, 1 ≤ B₁ k := fun k => (scalarGridStageBound_bounds (hB k) (hQ₀ k)).1
      have hBB₁ : ∀ k, B k ≤ B₁ k := fun k => (scalarGridStageBound_bounds (hB k) (hQ₀ k)).2.1
      have hstagesub : ∀ {X Q : ℕ → ℝ}, (∀ k, 1 ≤ X k) → (∀ k, 1 ≤ Q k) → SubpowerBound N X →
          SubpowerBound N Q → SubpowerBound N (fun k => scalarGridStageBound (X k) (Q k)) := by
        intro X Q hX hQ hXsub hQsub
        exact subpower_mul (fun k => zero_lt_one.trans_le (hN k))
          (fun k => by positivity) (fun k => zero_le_one.trans (hQ k))
          (subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
            (fun k => sq_nonneg (X k)) (subpower_const hNt 10000)
            (subpower_pow hN (fun k => zero_le_one.trans (hX k)) hXsub 2)) hQsub
      have hB₁sub : SubpowerBound N B₁ := hstagesub hB hQ₀ hBsub hQ₀sub
      have h8B₁ : ∀ k, 1 ≤ 8 * B₁ k := fun k => by linarith [hB₁ k]
      have h8B₁sub : SubpowerBound N (fun k => 8 * B₁ k) :=
        subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
          (fun k => zero_le_one.trans (hB₁ k)) (subpower_const hNt 8) hB₁sub
      obtain ⟨Q₁, hQ₁, hQ₁sub, hlocal₁⟩ := uniform_subpower_v2_block_fit_between_powers
        hker N (fun k => 8 * B₁ k) hN hNt h8B₁ h8B₁sub ha4 hab4 hd0 hd
      let B' : ℕ → ℝ := fun k => scalarGridStageBound (B₁ k) (Q₁ k)
      have hB' : ∀ k, 1 ≤ B' k := fun k => (scalarGridStageBound_bounds (hB₁ k) (hQ₁ k)).1
      have hB₁B' : ∀ k, B₁ k ≤ B' k :=
        fun k => (scalarGridStageBound_bounds (hB₁ k) (hQ₁ k)).2.1
      refine ⟨B', hB', fun k => (hKB k).trans ((hBB₁ k).trans (hB₁B' k)),
        hstagesub hB₁ hQ₁ hB₁sub hQ₁sub, ?_⟩
      filter_upwards [hprevious, hlocal₀, hlocal₁] with k hpreviousk hlocal₀k hlocal₁k
      intro Λ _ ν _ c E F ζ J hJ h hζ hmass hlow hhigh hζH
      obtain ⟨G⟩ := hpreviousk Λ ν c E F ζ (fun i => J i.succ) (fun i => hJ i.succ)
        h hζ hmass (fun i => hlow i.succ) (fun i => hhigh i.succ) (fun i => hζH i.succ)
      let H : ℝ := 1 / (J 0 : ℝ)
      have hJpos : (0 : ℝ) < J 0 := Nat.cast_pos.mpr (hJ 0)
      have hH : 0 < H := by simp only [H]; positivity
      have hH1 : H ≤ 1 := by
        apply (div_le_iff₀ hJpos).mpr
        simpa using (show (1 : ℝ) ≤ J 0 from by
          exact_mod_cast (Nat.succ_le_iff.mpr (hJ 0) : 1 ≤ J 0))
      have hpLow : N k ^ (-(b / 4)) ≤ H ^ (1 / 4 : ℝ) := by
        calc
          _ = (N k ^ (-b)) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_mul (zero_le_one.trans (hN k))]
            congr 1
            ring
          _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans (hN k)) _) (hlow 0)
            (by norm_num)
      have hpHigh : H ^ (1 / 4 : ℝ) ≤ N k ^ (-(a / 4)) := by
        calc
          _ ≤ (N k ^ (-a)) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hH.le (hhigh 0) (by norm_num)
          _ = _ := by
            rw [← Real.rpow_mul (zero_le_one.trans (hN k))]
            congr 1
            ring
      exact V2Hierarchy.extend J hJ (fun i => (1 / (J i : ℝ)) ^ (1 / 4 : ℝ)) G h hζ
        (hKB k) (hB k) (hQ₀ k) (hQ₁ k) (fun i => Real.rpow_nonneg (by positivity) _)
        (Real.self_le_rpow_of_le_one hH.le hH1 (by norm_num)) (hζH 0)
        (hlocal₀k Λ (H ^ (1 / 4 : ℝ)) hpLow hpHigh 0)
        (hlocal₁k Λ (H ^ (1 / 4 : ℝ)) hpLow hpHigh 1)


end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
