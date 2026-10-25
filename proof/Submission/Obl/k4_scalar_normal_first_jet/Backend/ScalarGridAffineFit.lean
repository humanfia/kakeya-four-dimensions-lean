/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGridAffineFit.lean.
Original o078/x0260 and support-module attributions are retained below.
Block arithmetic follows o078/x0260 commit e78f74ed, from
Submission/Obl/k4_scalar_exact_angular_packets/ScalarGridAffineFit.lean.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGridAffineFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarSubpowerBlockFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalRestriction
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPreparedBlocks
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockRecovery

/-! Assemble actual local fits at one mesh and restore all original labels. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

theorem original_scalar_grid_affine_fit {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d p duration : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hζ : 0 < ζ)
    (hduration : 0 ≤ duration) (hmass : K⁻¹ ≤ (ν.prod volume).real E)
    {J : ℕ} (hJ : 0 < J) (hHp : 1 / (J : ℝ) ≤ p) (hζH : ζ ≤ (1 / (J : ℝ)) ^ 2)
    (hfit : OriginalScalarBlockFitAt (d := d) Λ (8 * K) p duration) :
    ∃ (U : Set ℝ) (A C : ℝ → ℝ), MeasurableSet U ∧ U ⊆ Ico (0 : ℝ) 1 ∧
      U ⊆ scalarNormalTimes E ∧
      Measurable A ∧ Measurable C ∧ (∀ t, |A t| ≤ 5120 * K ^ 2 ∧ |C t| ≤ 5120 * K ^ 2) ∧
      ENNReal.ofReal (duration / (2 * K)) ≤ volume U ∧
      ENNReal.ofReal (duration / (16 * K ^ 2)) ≤ (ν.prod volume) (E ∩ (univ ×ˢ U)) ∧
      (∀ t ∈ U, ENNReal.ofReal (1 / (8 * K)) ≤ ν {l | (l, t) ∈ E ∩ (univ ×ˢ U)}) ∧
      (∀ t ∈ U, ∀ u ∈ U, scalarTimeBlockCode J hJ t = scalarTimeBlockCode J hJ u →
        A t = A u ∧ C t = C u) ∧
      ∀ q ∈ E ∩ (univ ×ˢ U),
        |F q.2 - (C q.2 + A q.2 * q.2)| ≤ 5120 * K ^ 2 * (1 / (J : ℝ)) * p := by
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
  have hRnormal : ScalarNormalHyp D ν R F S (8 * K) ζ d :=
    (h.restrict_event hR inter_subset_left).increase_constant hζ (by linarith)
  have hlocal : ∀ j ∈ I, ∃ (T : Set ℝ) (a v : ℝ), MeasurableSet T ∧
      T ⊆ Icc ((j : ℕ) / (J : ℝ)) ((j : ℕ) / (J : ℝ) + H) ∧
      T ⊆ scalarNormalTimes (R ∩ (univ ×ˢ timeCell J j)) ∧
      ENNReal.ofReal (H * duration) ≤ volume T ∧
      |a| ≤ 5120 * K ^ 2 ∧ |v| ≤ 5120 * K ^ 2 ∧
      ∀ t ∈ T, |F t - (a + v * t)| ≤ 5120 * K ^ 2 * H * p := by
    intro j hj
    let E₁ := R ∩ (univ ×ˢ timeCell J j)
    have hE₁ : MeasurableSet E₁ := hR.inter (MeasurableSet.univ.prod (measurableSet_timeCell J j))
    have hE₁normal := hRnormal.restrict_event hE₁ inter_subset_left
    have hE₁unit : E₁ ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun q hq => h.unit_time hq.1.1
    have hE₁mass : H / (8 * K) ≤ (ν.prod volume).real E₁ := by
      have hh := ENNReal.toReal_mono (original_unit_incidence_ne_top ν hE₁ hE₁unit) (hcellmass j hj)
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ τ / (J : ℝ))] at hh
      calc
        H / (8 * K) = τ / (J : ℝ) := div_right_comm 1 (J : ℝ) (8 * K)
        _ ≤ _ := hh
    have hE₁block : E₁ ⊆ univ ×ˢ Icc ((j : ℕ) / (J : ℝ)) ((j : ℕ) / (J : ℝ) + H) := by
      intro q hq
      refine ⟨mem_univ _, hq.2.2.1, ?_⟩
      have hh := hq.2.2.2.le
      change q.2 ≤ (((j : ℕ) : ℝ) + 1) / (J : ℝ) at hh
      change q.2 ≤ (j : ℕ) / (J : ℝ) + 1 / (J : ℝ)
      linarith [show (((j : ℕ) : ℝ) + 1) / (J : ℝ) = (j : ℕ) / (J : ℝ) + 1 / (J : ℝ) by ring]
    obtain ⟨T, a, v, hTm, hTblock, hTactive, hTvol, ha, hv, hrow⟩ :=
      hfit D ν E₁ F S ζ H ((j : ℕ) / (J : ℝ)) hE₁normal hζ hH hH1 hHp hζH hE₁block hE₁mass
    refine ⟨T, a, v, hTm, hTblock, hTactive, hTvol, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · intro t ht
      convert hrow t ht using 1 <;> ring
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
      (scalarTimeBlockCode_measurable J hJ) F a v hτ.le
      (show 0 ≤ 5120 * K ^ 2 by positivity) hTm hTcode hTvol hTfloor ha hv hrow
  have hUunit : U ⊆ Ico (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp (hUeq ▸ ht)
    exact hSunit (hTS j hj t htj)
  have hUactive : U ⊆ scalarNormalTimes E := by
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
  obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp (hUeq ▸ ht)
  obtain ⟨j, hj, huj⟩ := mem_iUnion₂.mp (hUeq ▸ hu)
  have hij : i = j := (hTcode i hi t hti).symm.trans (hcode.trans (hTcode j hj u huj))
  subst j
  exact ⟨(hrows i hi t hti).1.trans (hrows i hi u huj).1.symm,
    (hrows i hi t hti).2.trans (hrows i hi u huj).2.symm⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
