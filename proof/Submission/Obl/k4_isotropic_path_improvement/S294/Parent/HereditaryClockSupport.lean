-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.HereditaryClockSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/HereditaryClockSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourcePhysicalCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockIsotropicFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalVerticalCounts
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockStateCoarsening
import Submission.Obl.k4_profile_density_bounds.Support

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set
open Submission.Lib.K4ParentSignalPreparation.Census

noncomputable section

namespace HereditaryClockSupport

/-- Count the actual fine codes inside one coarse code using their
original whole-cell floors and the original coarse-cell ceiling. -/
theorem count_from_original_floors {Ω I Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (fine : Ω → I) (hfine : Measurable fine) (coarse : Ω → Q)
    (hcoarse : Measurable coarse) (mapCode : I → Q)
    (hfactor : ∀ x, coarse x = mapCode (fine x)) (E : Set Ω)
    (reference : ENNReal) (href : 0 < reference) (hreftop : reference ≠ ⊤)
    {floor cap : ℝ} (hfloor : 0 < floor) (hcap : 0 ≤ cap)
    (hFloor : ∀ x ∈ E, ENNReal.ofReal floor * reference ≤ μ (fine ⁻¹' {fine x}))
    (hCap : ∀ q, μ (coarse ⁻¹' {q}) ≤ ENNReal.ofReal cap * reference) (q : Q) :
    {i | ∃ x ∈ E, coarse x = q ∧ fine x = i}.Finite ∧
      ({i | ∃ x ∈ E, coarse x = q ∧ fine x = i}.ncard : ℝ) ≤ cap / floor := by
  classical
  let A : Set I := {i | ∃ x ∈ E, coarse x = q ∧ fine x = i}
  let μq := μ.restrict (coarse ⁻¹' {q})
  let ref := reference.toReal
  have hrefR : 0 < ref := ENNReal.toReal_pos href.ne' hreftop
  have htotal : μq.real univ ≤ cap * ref := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hreftop) (hCap q)
    simpa only [μq, measureReal_def, Measure.restrict_apply_univ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hcap, ref] using hh
  have hcount (F : Finset I) (hF : (↑F : Set I) ⊆ A) :
      (F.card : ℝ) ≤ cap / floor := by
    have hdisjoint : (↑F : Set I).PairwiseDisjoint (fun i => fine ⁻¹' {i}) := by
      intro i hi j hj hij
      apply disjoint_left.mpr
      intro x hx hy
      exact hij (hx.symm.trans hy)
    have hcell (i : I) (hi : i ∈ F) :
        μq (fine ⁻¹' {i}) = μ (fine ⁻¹' {i}) := by
      apply Measure.restrict_eq_self
      obtain ⟨x,hx,hxq,hxi⟩ := hF hi
      intro y hy
      change coarse y = q
      rw [hfactor y,hy,← hxi,← hfactor x,hxq]
    have hmass (i : I) (hi : i ∈ F) : floor * ref ≤ μq.real (fine ⁻¹' {i}) := by
      obtain ⟨x,hx,hxq,hxi⟩ := hF hi
      have hh := hFloor x hx
      rw [hxi] at hh
      have hr := ENNReal.toReal_mono (measure_ne_top μ _) hh
      simpa only [measureReal_def, hcell i hi, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hfloor.le, ref] using hr
    have hh := Submission.Lib.K4FinitePlankAtlases.old_cell_count μq F
      (fun i => fine ⁻¹' {i}) hdisjoint (fun i _ => hfine (measurableSet_singleton i))
      (mul_pos hfloor hrefR) hmass
    apply hh.trans
    apply (div_le_div_of_nonneg_right htotal (mul_pos hfloor hrefR).le).trans_eq
    field_simp
  have hfinite := Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
    A (cap / floor) hcount
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hcount _ (by simp)

/-- Both mesh coordinates coarsen by their exact dyadic factors. -/
theorem product_code_coarsens {Ω : Type*} (z : Ω → Fin 3 → ℝ) (Y : Ω → ℝ)
    (base hidden : ℝ) (bs hs : ℕ) (x : Ω) :
    gridCode z Y (base * (2 : ℝ) ^ bs) (hidden * (2 : ℝ) ^ hs) x =
      ParentSource.coarsenProductGrid bs hs (gridCode z Y base hidden x) := by
  unfold gridCode ParentSource.coarsenProductGrid
  congr 1
  · funext j
    rw [div_mul_eq_div_div, Submission.Lib.K4XInterface.floor_div_two_pow]
  · rw [div_mul_eq_div_div, Submission.Lib.K4XInterface.floor_div_two_pow]

/-- A moving-band ceiling controls one actual coarse physical cube.
The base cube has volume `(2R)^3`; the height center is constant. -/
theorem coarse_mass_of_band_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → P3) (Y : Ω → ℝ)
    (reference : ENNReal) {R C θ d : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hθ : 0 < θ)
    (hband : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      μ {x | z x ∈ U ∧ |Y x - c (z x)| ≤ R} ≤
        ENNReal.ofReal (C * θ ^ (-d) * R ^ d) * reference * volume U)
    (q : (Fin 3 → ℤ) × ℤ) :
    μ ((gridCode (fun x j => z x j) Y R R) ⁻¹' {q}) ≤
      ENNReal.ofReal (C * θ ^ (-d) * R ^ d * (2 * R) ^ 3) * reference := by
  let center : EuclideanSpace ℝ (Fin 4) :=
    WithLp.toLp 2 (Fin.snoc (fun j : Fin 3 => R * (q.1 j : ℝ)) (R * (q.2 : ℝ)))
  let U := k4_profile_density_bounds.baseBox center R
  have hsub : ((gridCode (fun x j => z x j) Y R R) ⁻¹' {q}) ⊆
      {x | z x ∈ U ∧ |Y x - R * (q.2 : ℝ)| ≤ R} := by
    intro x hx
    have hbase := congrArg Prod.fst hx
    have hheight := congrArg Prod.snd hx
    refine ⟨?_, ParentSource.physical_grid_corner_error hR hheight⟩
    apply (k4_profile_density_bounds.mem_baseBox_iff center R (z x)).mpr
    intro j
    simpa only [center, PiLp.toLp_apply, Fin.snoc_castSucc] using
      ParentSource.physical_grid_corner_error hR (congrFun hbase j)
  apply (measure_mono hsub).trans
  have hh := hband U (k4_profile_density_bounds.measurableSet_baseBox center R)
    (fun _ => R * (q.2 : ℝ)) measurable_const
  rw [k4_profile_density_bounds.volume_baseBox center R hR.le] at hh
  apply hh.trans_eq
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C * θ ^ (-d) * R ^ d)]
  ring

/-- The exact clock factor cancels in the hereditary fine-cell count.
The result counts all occupied cells, even if later labels are arbitrary. -/
theorem hereditary_clock_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → Fin 3 → ℝ) (hz : Measurable z) (Y : Ω → ℝ) (hY : Measurable Y)
    (E : Set Ω) (reference : ENNReal) (href : 0 < reference) (hreftop : reference ≠ ⊤)
    {base hidden R θ rate C d : ℝ} (hbase : 0 < base) (hhidden : 0 < hidden)
    (hR : 0 < R) (hθ : 0 < θ) (hrate : 0 < rate) (hC : 0 ≤ C)
    (bs hs : ℕ) (hRb : R = base * (2 : ℝ) ^ bs) (hRh : R = hidden * (2 : ℝ) ^ hs)
    (hFloor : ∀ x ∈ E,
      ENNReal.ofReal (rate * θ ^ (-d) * base ^ 3 * hidden ^ d) * reference ≤
        μ ((gridCode z Y base hidden) ⁻¹' {gridCode z Y base hidden x}))
    (hCap : ∀ q, μ ((gridCode z Y R R) ⁻¹' {q}) ≤
      ENNReal.ofReal (C * θ ^ (-d) * R ^ d * (2 * R) ^ 3) * reference)
    (q : (Fin 3 → ℤ) × ℤ) :
    {i | ∃ x ∈ E, gridCode z Y R R x = q ∧ gridCode z Y base hidden x = i}.Finite ∧
      ({i | ∃ x ∈ E, gridCode z Y R R x = q ∧ gridCode z Y base hidden x = i}.ncard : ℝ) ≤
        (8 * C / rate) * (R / base) ^ 3 * (R / hidden) ^ d := by
  have hf : Measurable (gridCode z Y base hidden) :=
    ParentSource.measurable_product_gridCode z hz Y hY base hidden
  have hc : Measurable (gridCode z Y R R) :=
    ParentSource.measurable_product_gridCode z hz Y hY R R
  have hfactor (x : Ω) : gridCode z Y R R x =
      ParentSource.coarsenProductGrid bs hs (gridCode z Y base hidden x) := by
    calc
      _ = gridCode z Y (base * (2 : ℝ) ^ bs) (hidden * (2 : ℝ) ^ hs) x := by
        rw [← hRb, ← hRh]
      _ = _ := product_code_coarsens z Y base hidden bs hs x
  obtain ⟨hfinite,hcount⟩ := count_from_original_floors μ _ hf _ hc
    (ParentSource.coarsenProductGrid bs hs) hfactor E reference href hreftop
    (by positivity : 0 < rate * θ ^ (-d) * base ^ 3 * hidden ^ d)
    (by positivity : 0 ≤ C * θ ^ (-d) * R ^ d * (2 * R) ^ 3) hFloor hCap q
  refine ⟨hfinite,hcount.trans_eq ?_⟩
  rw [Real.div_rpow hR.le hhidden.le]
  have hθd : θ ^ (-d) ≠ 0 := (Real.rpow_pos_of_pos hθ _).ne'
  have hhd : hidden ^ d ≠ 0 := (Real.rpow_pos_of_pos hhidden _).ne'
  field_simp
  <;> ring

/-- Produce the finite hereditary support tables required by the velocity
graph, directly from the original calibrated floors and moving-band caps. -/
theorem exists_hereditary_support {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → P3) (hz : Measurable z) (Y : Ω → ℝ) (hY : Measurable Y)
    (E : Set Ω) (reference : ENNReal) (href : 0 < reference) (hreftop : reference ≠ ⊤)
    {base hidden R θ rate C d : ℝ} (hbase : 0 < base) (hhidden : 0 < hidden)
    (hR : 0 < R) (hθ : 0 < θ) (hrate : 0 < rate) (hC : 0 ≤ C)
    (bs hs : ℕ) (hRb : R = base * (2 : ℝ) ^ bs) (hRh : R = hidden * (2 : ℝ) ^ hs)
    (hFloor : ∀ x ∈ E,
      ENNReal.ofReal (rate * θ ^ (-d) * base ^ 3 * hidden ^ d) * reference ≤
        μ ((gridCode (fun x j => z x j) Y base hidden) ⁻¹'
          {gridCode (fun x j => z x j) Y base hidden x}))
    (hband : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      μ {x | z x ∈ U ∧ |Y x - c (z x)| ≤ R} ≤
        ENNReal.ofReal (C * θ ^ (-d) * R ^ d) * reference * volume U)
    (q : (Fin 3 → ℤ) × ℤ) :
    ∃ F : Finset ((Fin 3 → ℤ) × ℤ),
      (F.card : ℝ) ≤ (8 * C / rate) * (R / base) ^ 3 * (R / hidden) ^ d ∧
      (∀ x ∈ E, gridCode (fun x j => z x j) Y R R x = q →
        gridCode (fun x j => z x j) Y base hidden x ∈ F) ∧
      ∀ i ∈ F, ∃ x ∈ E, gridCode (fun x j => z x j) Y R R x = q ∧
        gridCode (fun x j => z x j) Y base hidden x = i := by
  classical
  have hz' : Measurable (fun x j => z x j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (PiLp.continuous_apply 2 _ j).measurable.comp hz
  obtain ⟨hfinite,hcount⟩ := hereditary_clock_count μ _ hz' Y hY E reference href hreftop
    hbase hhidden hR hθ hrate hC bs hs hRb hRh hFloor
    (coarse_mass_of_band_cap μ z Y reference hR hC hθ hband) q
  refine ⟨hfinite.toFinset, ?_, ?_, ?_⟩
  · simpa only [Set.ncard_eq_toFinset_card _ hfinite] using hcount
  · intro x hx hxq
    exact hfinite.mem_toFinset.mpr ⟨x,hx,hxq,rfl⟩
  · intro i hi
    exact hfinite.mem_toFinset.mp hi

end HereditaryClockSupport

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
