import Submission.Obl.k4_scalar_tangent_isotropic_improvement.PlaneDichotomy

set_option linter.unusedVariables false

/-!
# Bad cells in product-measure form

`pi_det_lower` turns "no plane through the origin captures more than `1 - c` of a cell's unit
lifted directions within `ε`" into the hypothesis `hbad` of `bad_mass_le`: the triples of the
cell's incidences have direction determinant at least `ε²` with mass at least `c² m³`
(`triple_det_lower` after `pi_fin_three_eq_map` and `Measure.pi_map_pi`).
-/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The triple product measure as a pushforward of the iterated product. -/
lemma pi_fin_three_eq_map {β : Type*} [MeasurableSpace β] (P : Measure β) [SigmaFinite P] :
    Measure.pi (fun _ : Fin 3 => P) =
      (P.prod (P.prod P)).map (fun x : β × β × β => ![x.1, x.2.1, x.2.2]) := by
  have hg : Measurable (fun x : β × β × β => (![x.1, x.2.1, x.2.2] : Fin 3 → β)) := by
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i
    · exact measurable_fst
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hg (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : β × β × β => (![x.1, x.2.1, x.2.2] : Fin 3 → β)) ⁻¹' Set.univ.pi s =
      s 0 ×ˢ (s 1 ×ˢ s 2) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Fin.forall_fin_succ,
      Fin.forall_fin_zero_pi]
    simp
  rw [hpre, Measure.prod_prod, Measure.prod_prod, Fin.prod_univ_three]
  ring

/-- **Bad cells from the absence of a capturing plane.** If, on a set `X` of incidences, every
open `ε`-slab about a plane through the origin contains at most `(1 - c)` of the `inc`-mass of the
unit lifted directions `u`, then the triples of incidences of `X` have direction determinant at
least `ε²` with `inc³`-mass at least `c² inc(X)³` (the hypothesis `hbad` of `bad_mass_le`). -/
theorem pi_det_lower {β : Type*} [MeasurableSpace β] (inc : Measure β) [IsFiniteMeasure inc]
    {X : Set β} (hX : MeasurableSet X) (u : β → E3) (hu : Measurable u)
    (hu1 : ∀ ω, ‖u ω‖ = 1) {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcap : ∀ ν : E3, ‖ν‖ = 1 → inc {ω | ω ∈ X ∧ |inner ℝ ν (u ω)| < ε} ≤
      ENNReal.ofReal (1 - c) * inc X) :
    ENNReal.ofReal (c ^ 2) * inc X ^ 3 ≤ Measure.pi (fun _ : Fin 3 => inc)
      {ω | (∀ i, ω i ∈ X) ∧ ε ^ 2 ≤ |Matrix.det (Matrix.of fun i k : Fin 3 => u (ω i) k)|} := by
  set P : Measure E3 := (inc.restrict X).map u with hP
  have hPuniv : P univ = inc X := by
    rw [hP, Measure.map_apply hu MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
  have hunit : P {v | ‖v‖ ≠ 1} = 0 := by
    have hm : MeasurableSet {v : E3 | ‖v‖ ≠ 1} :=
      (measurableSet_eq_fun measurable_norm measurable_const).compl
    rw [hP, Measure.map_apply hu hm]
    have : u ⁻¹' {v : E3 | ‖v‖ ≠ 1} = ∅ := by ext ω; simp [hu1 ω]
    rw [this, measure_empty]
  have hcapP : ∀ ν : E3, ‖ν‖ = 1 → P {v | |inner ℝ ν v| < ε} ≤ ENNReal.ofReal (1 - c) * P univ := by
    intro ν hν
    rw [hPuniv, hP, Measure.map_apply hu (measurableSet_lt (by fun_prop) measurable_const),
      Measure.restrict_apply (hu (measurableSet_lt (by fun_prop) measurable_const))]
    refine le_trans (le_of_eq ?_) (hcap ν hν)
    congr 1
    ext ω; simp [and_comm]
  have hT := triple_det_lower P hunit hε hc hc1 hcapP
  rw [hPuniv] at hT
  set D : Set (Fin 3 → E3) := {v | ε ^ 2 ≤ |Matrix.det (Matrix.of fun i k : Fin 3 => v i k)|}
    with hD
  have hDm : MeasurableSet D := by
    apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Continuous.measurable
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i k
    exact ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous).comp (continuous_apply i)
  have h1 : (P.prod (P.prod P)) {x | ε ^ 2 ≤
      |Matrix.det (Matrix.of fun i k : Fin 3 => (![x.1, x.2.1, x.2.2] i) k)|} =
      Measure.pi (fun _ : Fin 3 => P) D := by
    rw [pi_fin_three_eq_map, Measure.map_apply _ hDm]
    · rfl
    · apply measurable_pi_iff.mpr
      intro i
      fin_cases i
      · exact measurable_fst
      · exact measurable_fst.comp measurable_snd
      · exact measurable_snd.comp measurable_snd
  have hmap : Measure.pi (fun _ : Fin 3 => P) =
      (Measure.pi (fun _ : Fin 3 => inc.restrict X)).map (fun ω i => u (ω i)) := by
    rw [hP, ← Measure.pi_map_pi (fun _ => hu.aemeasurable)]
  have hum : Measurable (fun ω : Fin 3 → β => fun i => u (ω i)) :=
    Measurable.of_eval fun i => hu.comp (measurable_pi_apply i)
  have h2 : Measure.pi (fun _ : Fin 3 => P) D =
      Measure.pi (fun _ : Fin 3 => inc) ((fun ω i => u (ω i)) ⁻¹' D ∩ Set.univ.pi (fun _ => X)) := by
    rw [hmap]
    erw [Measure.map_apply hum hDm]
    rw [← Measure.restrict_pi_pi, Measure.restrict_apply (hum hDm)]
  rw [h1, h2] at hT
  refine hT.trans (measure_mono ?_)
  rintro ω ⟨hωD, hωX⟩
  exact ⟨fun i => hωX i (Set.mem_univ i), hωD⟩

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
