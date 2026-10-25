/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGridFirstJetCovers.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGridFirstJetCovers.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockFirstJetCovers
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyComparison
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFiniteCellRestriction
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalRestriction

/-! Assemble the original residual windows on every occupied finest time cell. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

namespace ScalarGridHierarchy

theorem exists_original_first_jet_cover_restriction {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K B P ζ d duration : ℝ}
    {J : Fin n → ℕ} {hJ : ∀ i, 0 < J i}
    (G : ScalarGridHierarchy ν E F J hJ (fun j => (1 / (J j : ℝ)) ^ (1 / 4 : ℝ)) B)
    (i : Fin n)
    (h : ScalarNormalHyp D ν E F S K ζ d) (hζ : 0 < ζ) (hd0 : 0 ≤ d) (hd : d < 1)
    (hP : 1 ≤ P) (hKP : K ≤ P) (hBP : B ≤ P) (hduration : 0 ≤ duration)
    {R : Set (Λ × ℝ)} (hRm : MeasurableSet R) (hR : R ⊆ E ∩ (univ ×ˢ G.times))
    (hζH : ζ ≤ (1 / (J i : ℝ)) ^ 2)
    (hfloor : ∀ q ∈ R,
      ENNReal.ofReal ((1 / (J i : ℝ)) / P) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ timeCell (J i)
          (scalarTimeBlockCode (J i) (hJ i) q.2))))
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 1) Λ ℤ (scalarBlockFitBound P)
      ((1 / (J i : ℝ)) ^ (1 / 8 : ℝ)) duration) :
    ∃ R' : Set (Λ × ℝ), MeasurableSet R' ∧ R' ⊆ R ∧
      (duration / (20000 * P ^ 6)) * (ν.prod volume).real R ≤ (ν.prod volume).real R' ∧
      ∀ r : ℝ, (1 / (J i : ℝ)) ^ ((1 - d) / 32) ≤ r →
        ∃ L : ℝ → ℤ → Finset ℝ,
          (∀ t z, ((L t z).card : ℝ) ≤ 1000 * (scalarBlockFitBound P) ^ 2) ∧
          ∀ q ∈ R', ∃ v ∈ L q.2 ⌊D.scalar F q.1 q.2 / (1 / (J i : ℝ))⌋,
            |scalarFirstJet D F (G.slope i) q.1 q.2 - v| ≤ r := by
  classical
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  let m := J i
  have hm : 0 < m := hJ i
  let H : ℝ := 1 / (m : ℝ)
  let code := scalarTimeBlockCode m hm
  let cell : Fin m → Set (Λ × ℝ) := fun j => R ∩ (univ ×ˢ timeCell m j)
  let α := duration / (20000 * P ^ 6)
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hH : 0 < H := by dsimp [H]; exact one_div_pos.mpr (Nat.cast_pos.mpr hm)
  have hH1 : H ≤ 1 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hm)).mpr
    simpa using (show (1 : ℝ) ≤ m from by exact_mod_cast (Nat.succ_le_iff.mpr hm : 1 ≤ m))
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hRunit : R ⊆ univ ×ˢ Ico (0 : ℝ) 1 := fun q hq => ⟨mem_univ _, G.unit_time (hR hq).2.2⟩
  have hnormal : ScalarNormalHyp D ν R F S P ζ d :=
    (h.restrict_event hRm (fun q hq => (hR hq).1)).increase_constant hζ hKP
  have hcellm j : MeasurableSet (cell j) := hRm.inter (MeasurableSet.univ.prod (measurableSet_timeCell m j))
  have hcellunit j : cell j ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    fun q hq => ⟨mem_univ _, (hRunit hq.1).2.1, (hRunit hq.1).2.2.le⟩
  have hcellEq j : R ∩ (fun q : Λ × ℝ => code q.2) ⁻¹' {j} = cell j := by
    ext q
    constructor
    · intro hq
      exact ⟨hq.1, mem_univ _, (scalarTimeBlockCode_eq_iff hm j (hRunit hq.1).2).mp hq.2⟩
    · intro hq
      exact ⟨hq.1, scalarTimeBlockCode_on_cell hm j hq.2.2⟩
  have hcellcap j : (ν.prod volume).real (cell j) ≤ H := by
    have hh := original_time_grid_cell_cap ν hRunit hm j
    rw [hcellEq, original_unit_time_prod_real ν (hcellm j) (hcellunit j)] at hh
    exact hh
  have hlocal j : ∃ A : Set Λ, MeasurableSet A ∧
      α * (ν.prod volume).real (cell j) ≤ (ν.prod volume).real (cell j ∩ (A ×ˢ univ)) ∧
      ∀ r : ℝ, H ^ ((1 - d) / 32) ≤ r →
        ∃ L : ℝ → ℤ → Finset ℝ,
          (∀ t z, ((L t z).card : ℝ) ≤ 1000 * (scalarBlockFitBound P) ^ 2) ∧
          ∀ l ∈ A, ∀ t, (l, t) ∈ cell j → ∃ v ∈ L t ⌊D.scalar F l t / H⌋,
            |scalarFirstJet D F (G.slope i) l t - v| ≤ r := by
    by_cases hnonempty : (cell j).Nonempty
    · obtain ⟨q₀, hq₀⟩ := hnonempty
      let a := G.intercept i q₀.2
      let slope := G.slope i q₀.2
      have hrows q (hq : q ∈ cell j) :
          G.slope i q.2 = slope ∧ G.intercept i q.2 = a :=
        G.constant_on_grid i q.2 (hR hq.1).2.2 q₀.2 (hR hq₀.1).2.2
          ((scalarTimeBlockCode_on_cell hm j hq.2.2).trans (scalarTimeBlockCode_on_cell hm j hq₀.2.2).symm)
      have hrow q (hq : q ∈ cell j) : |F q.2 - (a + slope * q.2)| ≤ P * H * H ^ (1 / 8 : ℝ) := by
        have hh := G.time_fit i (hR hq.1).2.2
        rw [(hrows q hq).1, (hrows q hq).2] at hh
        have hpowers : H ^ (1 / 4 : ℝ) ≤ H ^ (1 / 8 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hH hH1 (by norm_num)
        exact hh.trans (mul_le_mul
          (mul_le_mul_of_nonneg_right hBP hH.le) hpowers (Real.rpow_nonneg hH.le _) (by positivity))
      have hmasscell : H / P ≤ (ν.prod volume).real (cell j) := by
        have hf := hfloor q₀ hq₀.1
        rw [scalarTimeBlockCode_on_cell hm j hq₀.2.2] at hf
        have hh := ENNReal.toReal_mono (original_unit_incidence_ne_top ν (hcellm j) (hcellunit j)) hf
        change (ENNReal.ofReal (H / P)).toReal ≤ (ν.prod volume).real (cell j) at hh
        rw [ENNReal.toReal_ofReal (div_nonneg hH.le hPpos.le)] at hh
        exact hh
      have hblock : cell j ⊆ univ ×ˢ Icc ((j : ℕ) / (m : ℝ)) ((j : ℕ) / (m : ℝ) + H) := by
        intro q hq
        have hh := hq.2.2
        refine ⟨mem_univ _, hh.1, ?_⟩
        dsimp [timeCell] at hh
        dsimp [H]
        linarith [hh.2, show (((j : ℕ) : ℝ) + 1) / (m : ℝ) = (j : ℕ) / (m : ℝ) + 1 / (m : ℝ) by ring]
      have hζHp : ζ ≤ H * H ^ (1 / 8 : ℝ) :=
        hζH.trans (by nlinarith [Real.self_le_rpow_of_le_one hH.le hH1 (by norm_num : (1 / 8 : ℝ) ≤ 1)])
      obtain ⟨A, hAm, hmassA, hcover⟩ :=
        (hnormal.restrict_event (hcellm j) inter_subset_left).exists_original_block_first_jet_covers
          hP hζ hd0 hd hH hH1 hζHp hduration hblock hmasscell a slope
          ((G.bounded i q₀.2).1.trans hBP) hrow hconcentration
      refine ⟨A, hAm, ?_, ?_⟩
      · have hh := mul_le_mul_of_nonneg_left (hcellcap j) hα
        have he : α * H = H * duration / (20000 * P ^ 6) := by dsimp [α]; ring
        exact hh.trans (by simpa only [he] using hmassA)
      · intro r hr
        obtain ⟨L, hL, hLcover⟩ := hcover r hr
        refine ⟨L, hL, ?_⟩
        intro l hl t ht
        obtain ⟨v, hv, hdist⟩ := hLcover l hl t ht
        refine ⟨v, hv, ?_⟩
        simpa only [scalarFirstJet, (hrows (l, t) ht).1] using hdist
    · have hempty : cell j = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
      refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
      · simp only [hempty, empty_inter, measureReal_empty, mul_zero, le_refl]
      · intro r hr
        exact ⟨fun _ _ => ∅, fun _ _ => by simp only [Finset.card_empty, Nat.cast_zero]; positivity,
          fun l hl => False.elim hl⟩
  choose A hAm hmassA hcover using hlocal
  have hselection j : α * (ν.prod scalarUnitTime).real (R ∩ (fun q => code q.2) ⁻¹' {j}) ≤
      (ν.prod scalarUnitTime).real ((R ∩ (fun q => code q.2) ⁻¹' {j}) ∩ (A j ×ˢ univ)) := by
    rw [hcellEq, original_unit_time_prod_real ν (hcellm j) (hcellunit j),
      original_unit_time_prod_real ν ((hcellm j).inter ((hAm j).prod MeasurableSet.univ))
        (fun q hq => hcellunit j hq.1)]
    exact hmassA j
  obtain ⟨R', hR'm, hR'R, hmassR', hassigned⟩ := original_finite_time_cell_restriction ν scalarUnitTime hRm
    code (scalarTimeBlockCode_measurable m hm) A hAm hselection
  refine ⟨R', hR'm, hR'R, ?_, ?_⟩
  · rw [original_unit_time_prod_real ν hRm (fun q hq =>
      ⟨mem_univ _, (hRunit hq).2.1, (hRunit hq).2.2.le⟩),
      original_unit_time_prod_real ν hR'm (fun q hq =>
        ⟨mem_univ _, (hRunit (hR'R hq)).2.1, (hRunit (hR'R hq)).2.2.le⟩)] at hmassR'
    exact hmassR'
  · intro r hr
    choose L hL hLcover using fun j => hcover j r hr
    refine ⟨fun t z => L (code t) t z, fun t z => hL (code t) t z, ?_⟩
    intro q hq
    exact hLcover (code q.2) q.1 (hassigned q hq) q.2
      ⟨hR'R hq, mem_univ _, (scalarTimeBlockCode_eq_iff hm (code q.2) (hRunit (hR'R hq)).2).mp rfl⟩

end ScalarGridHierarchy

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
