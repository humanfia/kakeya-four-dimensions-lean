-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Grid, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Grid.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Grid.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Grid.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2BlockFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformLoss
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPreparedBlocks
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockRecovery

set_option autoImplicit false

/-!
# Fitting one row component at one mesh, version 2

The `j = 2` counterparts of `ScalarNormalRestriction.lean`, `ScalarSubpowerBlockFit.lean` and
`ScalarGridAffineFit.lean` of o078 (session x0662, branch `x0662` at `f2bac599`); paper `tex-05`,
proof of Prop. `prop:scalar-normal`, "Preparing the current labels" and "Fitting one row
component" at one hierarchy length `H = 1/J`:

* `UpperHyp.restrict_event`, `UpperHyp.increase_constant`;
* `V2BlockFitAt`: the block fit of component `i` at constant `K`, tolerance `p` and duration;
* `uniform_subpower_v2_block_affine_fit`: one subpower duration loss for all blocks;
* `v2_grid_affine_fit`: on the prepared blocks of the mesh `1/J`, measurable time-only affine
  rows `C + A t` for the component `i`, constant on each block, fitting `F · e_i` within
  `2624 K² (1/J) p` on a retained set of times, with all labels at those times retained.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set Filter
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_discrete_of_terminal_charts
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

namespace UpperHyp

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
  {E R : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K K' ζ d : ℝ}

theorem restrict_event [IsFiniteMeasure ν] (h : UpperHyp ν c E F K ζ d) (hR : MeasurableSet R)
    (hRE : R ⊆ E) : UpperHyp ν c R F K ζ d := by
  refine ⟨h.measurable_c, hR, h.row_measurable, hRE.trans h.unit_time,
    fun p hp => h.coefficients p (hRE hp), h.row_bounded,
    fun p hp q hq => h.row_comparison p (hRE hp) q (hRE hq),
    fun p hp q hq => h.residual_comparison p (hRE hp) q (hRE hq), ?_, ?_⟩
  · intro t r R' a hr hrR
    obtain ⟨m, z, hcov, hm⟩ := h.support_AD t r R' a hr hrR
    refine ⟨m, z, fun x hx => hcov ⟨?_, hx.2⟩, hm⟩
    obtain ⟨l, hl, rfl⟩ := hx.1
    exact ⟨l, hRE hl, rfl⟩
  · intro t a b₀ b₁ r hr
    refine (measureReal_mono ?_ (measure_ne_top ν _)).trans (h.spatial_cap t a b₀ b₁ r hr)
    exact fun l hl => ⟨hRE hl.1, hl.2⟩

theorem increase_constant (h : UpperHyp ν c E F K ζ d) (hζ : 0 < ζ) (hKK : K ≤ K') :
    UpperHyp ν c E F K' ζ d := by
  refine ⟨h.measurable_c, h.event_measurable, h.row_measurable, h.unit_time,
    fun p hp e => (h.coefficients p hp e).trans hKK, fun t => (h.row_bounded t).trans hKK,
    ?_, ?_, fun t => CellProofs.Assouad.mono_constant hζ (h.support_AD t) hKK, ?_⟩
  · intro p hp q hq
    exact (h.row_comparison p hp q hq).trans
      (mul_le_mul_of_nonneg_right hKK (add_nonneg (abs_nonneg _) hζ.le))
  · intro p hp q hq
    exact (h.residual_comparison p hp q hq).trans
      (mul_le_mul_of_nonneg_right hKK (by positivity))
  · intro t a b₀ b₁ r hr
    exact (h.spatial_cap t a b₀ b₁ r hr).trans
      (mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg (hζ.le.trans hr) _))

end UpperHyp

/-- **The block fit of component `i`** at constant `K`, tolerance `p` and duration. -/
def V2BlockFitAt {d : ℝ} (Λ : Type*) [MeasurableSpace Λ] (K p duration : ℝ) (i : Fin 2) :
    Prop :=
  ∀ (ν : Measure Λ) [IsProbabilityMeasure ν] (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (F : ℝ → Fin 2 → ℝ) (ζ H s : ℝ),
    UpperHyp ν c E F K ζ d → 0 < ζ → 0 < H → H ≤ 1 → H ≤ p → ζ ≤ H ^ 2 →
    E ⊆ univ ×ˢ Icc s (s + H) → H / K ≤ (ν.prod volume).real E →
    ∃ (T : Set ℝ) (a slope : ℝ), MeasurableSet T ∧ T ⊆ Icc s (s + H) ∧
      T ⊆ activeTimes E ∧ ENNReal.ofReal (H * duration) ≤ volume T ∧
      |a| ≤ 40 * K ^ 2 ∧ |slope| ≤ 40 * K ^ 2 ∧
      ∀ t ∈ T, |F t i - (a + slope * t)| ≤ 41 * K ^ 2 * H * p

/-- **One subpower duration loss for all blocks** (version 2). -/
theorem uniform_subpower_v2_block_affine_fit {Λ : Type*} [MeasurableSpace Λ]
    (hker : LocalFitStatement Λ) (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {exponent d : ℝ} (hexponent : 0 < exponent) (hd0 : 0 ≤ d) (hd : d < 1) :
    ∃ Q : ℕ → ℝ, (∀ k, 1 ≤ Q k) ∧ SubpowerBound N Q ∧
      ∀ᶠ k in atTop, ∀ i, V2BlockFitAt (d := d) Λ (K k) (N k ^ (-exponent)) (Q k)⁻¹ i := by
  obtain ⟨τ, Q, _, _, hQeq, hQ, hQsub, hgood⟩ := exists_uniform_subpower_tolerance N hN
    (fun τ k => ∀ i, V2BlockFitAt (d := d) Λ (K k) (N k ^ (-exponent)) (N k ^ (-τ)) i)
    (fun τ hτ => by
      filter_upwards [uniform_v2_block_affine_fit hker N K hN hNt hK hsub hexponent hd0 hd hτ]
        with k hk
      intro i ν _ c E F ζ H s h hζ hH hH1 hHp hζH hblock hmass
      exact hk ν c E F ζ H s i h hζ hH hH1 hHp hζH hblock hmass)
  refine ⟨Q, hQ, hQsub, ?_⟩
  filter_upwards [hgood] with k hk
  have he : N k ^ (-τ k) = (Q k)⁻¹ := by rw [hQeq k, Real.rpow_neg (zero_le_one.trans (hN k))]
  simpa only [he] using hk

/-- **Fitting one row component at one mesh** (version 2). -/
theorem v2_grid_affine_fit {Λ : Type*} [MeasurableSpace Λ]
    {ν : Measure Λ} [IsProbabilityMeasure ν] {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {K ζ d p duration : ℝ} (i : Fin 2)
    (h : UpperHyp ν c E F K ζ d) (hK : 1 ≤ K) (hζ : 0 < ζ)
    (hduration : 0 ≤ duration) (hmass : K⁻¹ ≤ (ν.prod volume).real E)
    {J : ℕ} (hJ : 0 < J) (hHp : 1 / (J : ℝ) ≤ p) (hζH : ζ ≤ (1 / (J : ℝ)) ^ 2)
    (hfit : V2BlockFitAt (d := d) Λ (8 * K) p duration i) :
    ∃ (U : Set ℝ) (A C : ℝ → ℝ), MeasurableSet U ∧ U ⊆ Ico (0 : ℝ) 1 ∧
      U ⊆ activeTimes E ∧
      Measurable A ∧ Measurable C ∧ (∀ t, |A t| ≤ 2624 * K ^ 2 ∧ |C t| ≤ 2624 * K ^ 2) ∧
      ENNReal.ofReal (duration / (2 * K)) ≤ volume U ∧
      ENNReal.ofReal (duration / (16 * K ^ 2)) ≤ (ν.prod volume) (E ∩ (univ ×ˢ U)) ∧
      (∀ t ∈ U, ENNReal.ofReal (1 / (8 * K)) ≤ ν {l | (l, t) ∈ E ∩ (univ ×ˢ U)}) ∧
      (∀ t ∈ U, ∀ u ∈ U, scalarTimeBlockCode J hJ t = scalarTimeBlockCode J hJ u →
        A t = A u ∧ C t = C u) ∧
      ∀ q ∈ E ∩ (univ ×ˢ U),
        |F q.2 i - (C q.2 + A q.2 * q.2)| ≤ 2624 * K ^ 2 * (1 / (J : ℝ)) * p := by
  classical
  let H : ℝ := 1 / (J : ℝ)
  let τ : ℝ := 1 / (8 * K)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hJpos : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast (Nat.succ_le_iff.mpr hJ : 1 ≤ J)
  have hH : 0 < H := by dsimp [H]; positivity
  have hH1 : H ≤ 1 := by
    apply (div_le_iff₀ hJpos).mpr
    simpa using hJone
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hbudget : 4 * τ ≤ K⁻¹ := by dsimp [τ]; field_simp; nlinarith
  obtain ⟨S₀, I, hS₀, hSunit, hretained, hfloor, hcellmass, hcount⟩ :=
    prepare_original_scalar_blocks ν h.event_measurable h.unit_time hτ hbudget hmass hJ
  let R := E ∩ (univ ×ˢ S₀)
  have hR : MeasurableSet R := h.event_measurable.inter (MeasurableSet.univ.prod hS₀)
  have hRnormal : UpperHyp ν c R F (8 * K) ζ d :=
    (h.restrict_event hR inter_subset_left).increase_constant hζ (by linarith)
  have hlocal : ∀ j ∈ I, ∃ (T : Set ℝ) (a v : ℝ), MeasurableSet T ∧
      T ⊆ Icc ((j : ℕ) / (J : ℝ)) ((j : ℕ) / (J : ℝ) + H) ∧
      T ⊆ activeTimes (R ∩ (univ ×ˢ timeCell J j)) ∧
      ENNReal.ofReal (H * duration) ≤ volume T ∧
      |a| ≤ 2624 * K ^ 2 ∧ |v| ≤ 2624 * K ^ 2 ∧
      ∀ t ∈ T, |F t i - (a + v * t)| ≤ 2624 * K ^ 2 * H * p := by
    intro j hj
    let E₁ := R ∩ (univ ×ˢ timeCell J j)
    have hE₁ : MeasurableSet E₁ := hR.inter (MeasurableSet.univ.prod (measurableSet_timeCell J j))
    have hE₁normal := hRnormal.restrict_event hE₁ inter_subset_left
    have hE₁unit : E₁ ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun q hq => h.unit_time hq.1.1
    have hE₁mass : H / (8 * K) ≤ (ν.prod volume).real E₁ := by
      have hh := ENNReal.toReal_mono (original_unit_incidence_ne_top ν hE₁ hE₁unit)
        (hcellmass j hj)
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ τ / (J : ℝ))] at hh
      have e : H / (8 * K) = τ / (J : ℝ) := by
        show (1 / (J : ℝ)) / (8 * K) = (1 / (8 * K)) / (J : ℝ)
        ring
      rw [e]
      exact hh
    have hE₁block : E₁ ⊆ univ ×ˢ Icc ((j : ℕ) / (J : ℝ)) ((j : ℕ) / (J : ℝ) + H) := by
      intro q hq
      refine ⟨mem_univ _, hq.2.2.1, ?_⟩
      have hh := hq.2.2.2.le
      try dsimp only [timeCell] at hh
      try dsimp only [H]
      linarith [show (((j : ℕ) : ℝ) + 1) / (J : ℝ) = (j : ℕ) / (J : ℝ) + 1 / (J : ℝ) by ring]
    obtain ⟨T, a, v, hTm, hTblock, hTactive, hTvol, ha, hv, hrow⟩ :=
      hfit ν c E₁ F ζ H ((j : ℕ) / (J : ℝ)) hE₁normal hζ hH hH1 hHp hζH hE₁block hE₁mass
    refine ⟨T, a, v, hTm, hTblock, hTactive, hTvol, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · intro t ht
      have := hrow t ht
      have e : 41 * (8 * K) ^ 2 * H * p = 2624 * K ^ 2 * H * p := by ring
      linarith
  choose! T a v hTm hTblock hTactive hTvol ha hv hrow using hlocal
  have hTcode j (hj : j ∈ I) t (ht : t ∈ T j) : scalarTimeBlockCode J hJ t = j := by
    obtain ⟨l, hl⟩ := hTactive j hj ht
    exact scalarTimeBlockCode_on_cell hJ j hl.2.2
  have hTS j (hj : j ∈ I) t (ht : t ∈ T j) : t ∈ S₀ := by
    obtain ⟨l, hl⟩ := hTactive j hj ht
    exact hl.1.2.2
  have hTfloor j (hj : j ∈ I) t (ht : t ∈ T j) :
      ENNReal.ofReal τ ≤ ν {l | (l, t) ∈ E} :=
    (hfloor t (hTS j hj t ht)).trans (measure_mono (fun l hl => hl.1))
  obtain ⟨U, A, C, hUeq, hUm, hAm, hCm, hb, hvol, hmassU, hrows, hfloorU, hfitU⟩ :=
    original_block_fit_recovery ν h.event_measurable I T (scalarTimeBlockCode J hJ)
      (scalarTimeBlockCode_measurable J hJ) (fun t => F t i) a v hτ.le
      (show 0 ≤ 2624 * K ^ 2 by positivity) hTm hTcode hTvol hTfloor ha hv hrow
  have hUunit : U ⊆ Ico (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp (hUeq ▸ ht)
    exact hSunit (hTS j hj t htj)
  have hUactive : U ⊆ activeTimes E := by
    intro t ht
    obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp (hUeq ▸ ht)
    obtain ⟨l, hl⟩ := hTactive j hj htj
    exact ⟨l, hl.1.1⟩
  have hvolnum : duration / (2 * K) ≤ (I.card : ℝ) * (H * duration) := by
    have hh := mul_le_mul_of_nonneg_right hcount hduration
    convert hh using 1 <;> (try dsimp only [H]) <;> field_simp <;> ring
  have hmassnum : duration / (16 * K ^ 2) ≤ τ * (I.card : ℝ) * (H * duration) := by
    have hh := mul_le_mul_of_nonneg_left hvolnum hτ.le
    convert hh using 1 <;> (try dsimp only [τ]) <;> field_simp <;> ring
  refine ⟨U, A, C, hUm, hUunit, hUactive, hAm, hCm, hb,
    (ENNReal.ofReal_le_ofReal hvolnum).trans hvol,
    (ENNReal.ofReal_le_ofReal hmassnum).trans hmassU, hfloorU, ?_, hfitU⟩
  intro t ht u hu hcode
  obtain ⟨i', hi', hti⟩ := mem_iUnion₂.mp (hUeq ▸ ht)
  obtain ⟨j, hj, huj⟩ := mem_iUnion₂.mp (hUeq ▸ hu)
  have hij : i' = j := (hTcode i' hi' t hti).symm.trans (hcode.trans (hTcode j hj u huj))
  subst j
  exact ⟨(hrows i' hi' t hti).1.trans (hrows i' hi' u huj).1.symm,
    (hrows i' hi' t hti).2.trans (hrows i' hi' u huj).2.symm⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
