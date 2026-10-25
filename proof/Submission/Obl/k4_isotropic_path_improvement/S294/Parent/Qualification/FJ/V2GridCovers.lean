-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2GridCovers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2GridCovers.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2GridCovers.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2GridCovers.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2BlockWindows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Taylor
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Grid
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyComparison
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFiniteCellRestriction

set_option autoImplicit false

/-!
# First-jet covers on every occupied cell of a hierarchy level, version 2

The `j = 2` counterpart of x0662's and x0260's `ScalarGridFirstJetCovers.lean` (o078, branch
`x0260` at `206ab988`), with the same proof: on every occupied cell of length `H = 1/J i` of the
level `i` of a version-2 hierarchy, both row components are affine up to `B H H^(1/4)`; the block
covers of `V2BlockWindows.lean` apply there, and one finite selection over the cells keeps the
fraction `duration / (400000 P⁸)` of the retained mass, with covers of the first jet against the
row of slopes `G.slopeRow i` of that level.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

noncomputable section

/-- The row of slopes of level `i` of a version-2 hierarchy. -/
def V2Hierarchy.slopeRow {Λ : Type*} [MeasurableSpace Λ] {n : ℕ} {ν : Measure Λ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {J : Fin n → ℕ} {hJ : ∀ i, 0 < J i}
    {p : Fin n → ℝ} {B : ℝ} (G : V2Hierarchy ν E F J hJ p B) (i : Fin n) (t : ℝ) : Fin 2 → ℝ :=
  fun k => (G.comp k).slope i t

theorem V2Hierarchy.measurable_slopeRow {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {J : Fin n → ℕ} {hJ : ∀ i, 0 < J i}
    {p : Fin n → ℝ} {B : ℝ} (G : V2Hierarchy ν E F J hJ p B) (i : Fin n) :
    Measurable (G.slopeRow i) := by
  apply measurable_pi_lambda
  intro k
  exact (G.comp k).measurable_slope i

theorem V2Hierarchy.times_comp {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {J : Fin n → ℕ} {hJ : ∀ i, 0 < J i}
    {p : Fin n → ℝ} {B : ℝ} (G : V2Hierarchy ν E F J hJ p B) (k : Fin 2) :
    (G.comp k).times = (G.comp 0).times := by
  fin_cases k
  · rfl
  · exact G.times_eq

theorem V2Hierarchy.finestRow_eq {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {J : Fin (n + 1) → ℕ}
    {hJ : ∀ i, 0 < J i} {p : Fin (n + 1) → ℝ} {B : ℝ} (G : V2Hierarchy ν E F J hJ p B) :
    G.finestRow = G.slopeRow (Fin.last n) := rfl

/-- **First-jet covers on all occupied cells of one level** (version 2). -/
theorem V2Hierarchy.exists_v2_first_jet_cover_restriction {Λ : Type*} [MeasurableSpace Λ]
    {n : ℕ} {ν : Measure Λ} [IsProbabilityMeasure ν] {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {K B P ζ d duration : ℝ}
    {J : Fin n → ℕ} {hJ : ∀ i, 0 < J i}
    (G : V2Hierarchy ν E F J hJ (fun j => (1 / (J j : ℝ)) ^ (1 / 4 : ℝ)) B)
    (i : Fin n)
    (h : UpperHyp ν c E F K ζ d) (hζ : 0 < ζ) (hd0 : 0 ≤ d) (hd : d < 1)
    (hP : 1 ≤ P) (hKP : K ≤ P) (hBP : B ≤ P) (hduration : 0 ≤ duration)
    {R : Set (Λ × ℝ)} (hRm : MeasurableSet R) (hR : R ⊆ E ∩ (univ ×ˢ (G.comp 0).times))
    (hζH : ζ ≤ (1 / (J i : ℝ)) ^ 2)
    (hfloor : ∀ q ∈ R,
      ENNReal.ofReal ((1 / (J i : ℝ)) / P) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ timeCell (J i)
          (scalarTimeBlockCode (J i) (hJ i) q.2))))
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 2) Λ (Fin 2 → ℤ)
      (v2ResidualBound P) ((1 / (J i : ℝ)) ^ (1 / 8 : ℝ)) duration) :
    ∃ R' : Set (Λ × ℝ), MeasurableSet R' ∧ R' ⊆ R ∧
      (duration / (400000 * P ^ 8)) * (ν.prod volume).real R ≤ (ν.prod volume).real R' ∧
      ∀ r : ℝ, (1 / (J i : ℝ)) ^ ((1 - d) / 32) ≤ r →
        ∃ L : ℝ → ℤ → Finset ℝ,
          (∀ t z, ((L t z).card : ℝ) ≤ 1000 * (v2ResidualBound P) ^ 2) ∧
          ∀ q ∈ R', ∃ v ∈ L q.2 ⌊zS F (c q.1) q.2 / (1 / (J i : ℝ))⌋,
            |v2FirstJet (c q.1) F (G.slopeRow i) q.2 - v| ≤ r := by
  classical
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  let m := J i
  have hm : 0 < m := hJ i
  let H : ℝ := 1 / (m : ℝ)
  let code := scalarTimeBlockCode m hm
  let cell : Fin m → Set (Λ × ℝ) := fun j => R ∩ (univ ×ˢ timeCell m j)
  let α := duration / (400000 * P ^ 8)
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hH : 0 < H := by simp only [H]; exact one_div_pos.mpr (Nat.cast_pos.mpr hm)
  have hH1 : H ≤ 1 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hm)).mpr
    simpa using (show (1 : ℝ) ≤ m from by exact_mod_cast (Nat.succ_le_iff.mpr hm : 1 ≤ m))
  have hα : 0 ≤ α := by simp only [α]; positivity
  have hRunit : R ⊆ univ ×ˢ Ico (0 : ℝ) 1 :=
    fun q hq => ⟨mem_univ _, (G.comp 0).unit_time (hR hq).2.2⟩
  have hnormal : UpperHyp ν c R F P ζ d :=
    (h.restrict_event hRm (fun q hq => (hR hq).1)).increase_constant hζ hKP
  have hcellm j : MeasurableSet (cell j) :=
    hRm.inter (MeasurableSet.univ.prod (measurableSet_timeCell m j))
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
  have htimes : ∀ k, (G.comp k).times = (G.comp 0).times := G.times_comp
  have hlocal j : ∃ A : Set Λ, MeasurableSet A ∧
      α * (ν.prod volume).real (cell j) ≤ (ν.prod volume).real (cell j ∩ (A ×ˢ univ)) ∧
      ∀ r : ℝ, H ^ ((1 - d) / 32) ≤ r →
        ∃ L : ℝ → ℤ → Finset ℝ,
          (∀ t z, ((L t z).card : ℝ) ≤ 1000 * (v2ResidualBound P) ^ 2) ∧
          ∀ l ∈ A, ∀ t, (l, t) ∈ cell j → ∃ v ∈ L t ⌊zS F (c l) t / H⌋,
            |v2FirstJet (c l) F (G.slopeRow i) t - v| ≤ r := by
    by_cases hnonempty : (cell j).Nonempty
    · obtain ⟨q₀, hq₀⟩ := hnonempty
      let a : Fin 2 → ℝ := fun k => (G.comp k).intercept i q₀.2
      let slope : Fin 2 → ℝ := fun k => (G.comp k).slope i q₀.2
      have hq₀t : ∀ k, q₀.2 ∈ (G.comp k).times := fun k => by
        rw [htimes k]; exact (hR hq₀.1).2.2
      have hrows q (hq : q ∈ cell j) (k : Fin 2) :
          (G.comp k).slope i q.2 = slope k ∧ (G.comp k).intercept i q.2 = a k := by
        have hqt : q.2 ∈ (G.comp k).times := by rw [htimes k]; exact (hR hq.1).2.2
        exact (G.comp k).constant_on_grid i q.2 hqt q₀.2 (hq₀t k)
          ((scalarTimeBlockCode_on_cell hm j hq.2.2).trans
            (scalarTimeBlockCode_on_cell hm j hq₀.2.2).symm)
      have hpowers : H ^ (1 / 4 : ℝ) ≤ H ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hH hH1 (by norm_num)
      have hrow q (hq : q ∈ cell j) (k : Fin 2) :
          |F q.2 k - (a k + slope k * q.2)| ≤ P * H * H ^ (1 / 8 : ℝ) := by
        have hqt : q.2 ∈ (G.comp k).times := by rw [htimes k]; exact (hR hq.1).2.2
        have hh := (G.comp k).time_fit i hqt
        rw [(hrows q hq k).1, (hrows q hq k).2] at hh
        exact hh.trans (mul_le_mul
          (mul_le_mul_of_nonneg_right hBP hH.le) hpowers (Real.rpow_nonneg hH.le _)
          (by positivity))
      have hmasscell : H / P ≤ (ν.prod volume).real (cell j) := by
        have hf := hfloor q₀ hq₀.1
        rw [scalarTimeBlockCode_on_cell hm j hq₀.2.2] at hf
        have hh := ENNReal.toReal_mono
          (original_unit_incidence_ne_top ν (hcellm j) (hcellunit j)) hf
        rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (J i : ℝ) / P)] at hh
        exact hh
      have hblock : cell j ⊆ univ ×ˢ Icc ((j : ℕ) / (m : ℝ)) ((j : ℕ) / (m : ℝ) + H) := by
        intro q hq
        have hh : q.2 ∈ timeCell m j := hq.2.2
        simp only [timeCell, mem_Ico] at hh
        refine ⟨mem_univ _, hh.1, ?_⟩
        show q.2 ≤ (j : ℕ) / (m : ℝ) + 1 / (m : ℝ)
        have e : (((j : ℕ) : ℝ) + 1) / (m : ℝ) = (j : ℕ) / (m : ℝ) + 1 / (m : ℝ) := by ring
        linarith [hh.2]
      have hζHp : ζ ≤ H * H ^ (1 / 8 : ℝ) :=
        hζH.trans (by
          nlinarith [Real.self_le_rpow_of_le_one hH.le hH1 (by norm_num : (1 / 8 : ℝ) ≤ 1)])
      have hslope : ∀ k, |slope k| ≤ P := fun k => ((G.comp k).bounded i q₀.2).1.trans hBP
      obtain ⟨A, hAm, hmassA, hcover⟩ :=
        (hnormal.restrict_event (hcellm j) inter_subset_left).exists_v2_block_first_jet_covers
          hP hζ hd0 hd hH hH1 hζHp hduration hblock hmasscell a slope hslope hrow
          hconcentration
      refine ⟨A, hAm, ?_, ?_⟩
      · have hh := mul_le_mul_of_nonneg_left (hcellcap j) hα
        have he : α * H = H * duration / (400000 * P ^ 8) := by simp only [α]; ring
        exact hh.trans (by simpa only [he] using hmassA)
      · intro r hr
        obtain ⟨L, hL, hLcover⟩ := hcover r hr
        refine ⟨L, hL, ?_⟩
        intro l hl t ht
        obtain ⟨v, hv, hdist⟩ := hLcover l hl t ht
        refine ⟨v, hv, ?_⟩
        have hrowfun : G.slopeRow i t = slope := by
          funext k
          exact (hrows (l, t) ht k).1
        simpa only [v2FirstJet, hrowfun] using hdist
    · have hempty : cell j = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
      refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
      · simp only [hempty, empty_inter, measureReal_empty, mul_zero, le_refl]
      · intro r _
        exact ⟨fun _ _ => ∅, fun _ _ => by simp; positivity, fun l hl => False.elim hl⟩
  choose A hAm hmassA hcover using hlocal
  have hselection j : α * (ν.prod scalarUnitTime).real (R ∩ (fun q => code q.2) ⁻¹' {j}) ≤
      (ν.prod scalarUnitTime).real ((R ∩ (fun q => code q.2) ⁻¹' {j}) ∩ (A j ×ˢ univ)) := by
    rw [hcellEq, original_unit_time_prod_real ν (hcellm j) (hcellunit j),
      original_unit_time_prod_real ν ((hcellm j).inter ((hAm j).prod MeasurableSet.univ))
        (fun q hq => hcellunit j hq.1)]
    exact hmassA j
  obtain ⟨R', hR'm, hR'R, hmassR', hassigned⟩ :=
    original_finite_time_cell_restriction ν scalarUnitTime hRm code
      (scalarTimeBlockCode_measurable m hm) A hAm hselection
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
      ⟨hR'R hq, mem_univ _,
        (scalarTimeBlockCode_eq_iff hm (code q.2) (hRunit (hR'R hq)).2).mp rfl⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
