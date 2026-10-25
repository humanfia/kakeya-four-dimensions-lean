import Submission.Obl.k4_initial_horizon_bound.BoundedResidual
import Submission.Obl.k4_initial_horizon_bound.PlanarPacking

/-! The per-group finite-mesh greedy interface for the initial horizon construction. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_initial_horizon_bound

open Submission.Lib.K4ContinuousPlanks

abbrev MeshPlank (D : ℕ) := {p : PlanarPlank // 2 / (D : ℝ) ≤ p.thin ∧ p.wide ≤ 2}

theorem mesh_greedy_plank_cover (ε : ℝ) (hε : 0 < ε) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ D : ℕ, 2 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
      (b u : α → EuclideanSpace ℝ (Fin 2)),
    Measurable b → Measurable u → ∀ U : Set α, MeasurableSet U →
    (∀ x ∈ U, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
    ∀ E Gd : Set (α × ℝ), MeasurableSet E → MeasurableSet Gd →
      E ⊆ univ ×ˢ Icc (0 : ℝ) 1 →
    ∀ τ₀ s : ℝ, 0 < τ₀ → (D : ℝ) ^ (-η) ≤ s →
    ∀ F : Finset (ℤ × (Fin 2 → ℤ)),
      (∀ p ∈ E ∩ Gd, p.1 ∈ U →
        (⌊p.2 * (D : ℝ)⌋, fun k : Fin 2 => ⌊(D : ℝ) * (b p.1 + p.2 • u p.1) k⌋) ∈ F) →
    ∃ ps : List PlanarPlank,
      (∀ p ∈ ps, 2 / (D : ℝ) ≤ p.thin ∧ p.wide ≤ 2) ∧
      GreedyEligible (ν.withDensity (incidenceDuration E)) (fun p => p.lines b u)
        (fun p => τ₀ * p.area) U ps ∧
      (ν.prod volume) (E ∩ (greedyResidual (fun p => p.lines b u) U ps ×ˢ univ)) ≤
        (ν.prod volume) (E ∩ Gdᶜ ∩ (greedyResidual (fun p => p.lines b u) U ps ×ˢ univ)) +
        ENNReal.ofReal s * ν (greedyResidual (fun p => p.lines b u) U ps) +
        ENNReal.ofReal (C * τ₀ * (D : ℝ) ^ ε / (s * (D : ℝ) ^ 3) * (F.card : ℝ)) := by
  classical
  obtain ⟨η, C, hη, hC, H⟩ := bounded_stopped_residual ε hε
  refine ⟨η, C, hη, hC, ?_⟩
  intro D hD α _ ν _ b u hb hu U hU hbu E Gd hE hGd hunit τ₀ s hτ₀ hlong F hF
  have hD1 : 1 ≤ D := by omega
  have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hs : 0 < s := (Real.rpow_pos_of_pos hDp (-η)).trans_le hlong
  let μ := ν.withDensity (incidenceDuration E)
  haveI : IsFiniteMeasure μ := finite_duration_law ν hE hunit
  let S : PlanarPlank → Set α := fun p => p.lines b u
  let S' : MeshPlank D → Set α := fun p => S p.1
  let floor : MeshPlank D → ℝ := fun p => τ₀ * p.1.area
  have hS : ∀ p, MeasurableSet (S p) := fun p => p.measurableSet_lines hb hu
  have hfloor (p : MeshPlank D) : τ₀ * (2 / (D : ℝ)) ^ 2 ≤ floor p := by
    have hmul := mul_le_mul p.property.1 (p.property.1.trans p.1.widths_le)
      (by positivity : 0 ≤ 2 / (D : ℝ)) p.1.thin_pos.le
    exact mul_le_mul_of_nonneg_left (by simpa only [pow_two, PlanarPlank.area] using hmul) hτ₀.le
  obtain ⟨qs, hqs, hstop⟩ := exists_greedy_packing μ S' (fun p => hS p.1) floor
    (by positivity : 0 < τ₀ * (2 / (D : ℝ)) ^ 2) hfloor U
  let ps : List PlanarPlank := qs.map Subtype.val
  have hps : GreedyEligible μ S (fun p => τ₀ * p.area) U ps :=
    (greedyEligible_map μ S (fun p => τ₀ * p.area) Subtype.val U qs).mpr hqs
  have hpswidths : ∀ p ∈ ps, 2 / (D : ℝ) ≤ p.thin ∧ p.wide ≤ 2 := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    exact q.property
  let R := greedyResidual S U ps
  have hRU : R ⊆ U := greedyResidual_subset S U ps
  have hR : MeasurableSet R := measurableSet_greedyResidual S hS hU ps
  let Eg : Set (α × ℝ) := E ∩ Gd ∩ (R ×ˢ univ)
  have hEg : MeasurableSet Eg := (hE.inter hGd).inter (hR.prod MeasurableSet.univ)
  have hEgsub : Eg ⊆ R ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨hp.2.1, (hunit hp.1.1).2⟩
  have hstopg : MeshPlankCap D (ν.withDensity (incidenceDuration Eg)) b u τ₀ := by
    intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ
    have ha0 : 0 < a := (div_pos (by norm_num) hDp).trans_le ha
    let p : PlanarPlank := ⟨c, w, e₁, e₂, a, β, he₁, he₂, he, ha0, hab⟩
    let q : MeshPlank D := ⟨p, ha, hβ⟩
    have hr : μ.real (R ∩ S p) ≤ τ₀ * p.area := by
      change μ.real (greedyResidual S U (qs.map Subtype.val) ∩ S p) ≤ _
      rw [greedyResidual_map]
      exact (hstop q).le
    have hbound : μ (R ∩ S p) ≤ ENNReal.ofReal (τ₀ * p.area) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal hr
    have heq : μ (R ∩ S p) = (ν.prod volume) (E ∩ ((R ∩ S p) ×ˢ univ)) :=
      duration_withDensity_apply ν hE (hR.inter (hS p))
    have hsub : Eg ∩ (S p ×ˢ univ) ⊆ E ∩ ((R ∩ S p) ×ˢ univ) := by
      rintro ⟨x, t⟩ ⟨⟨⟨hxE, _⟩, hxR, _⟩, hxS, _⟩
      exact ⟨hxE, ⟨hxR, hxS⟩, mem_univ _⟩
    have hmass := (measure_mono (μ := ν.prod volume) hsub).trans (heq ▸ hbound)
    rw [← duration_withDensity_apply ν hEg (hS p)] at hmass
    simpa only [S, PlanarPlank.lines, PlanarPlank.area, p, mul_assoc] using hmass
  let F' : Finset (ℕ × (Fin 2 → ℤ)) := F.image (fun z => (z.1.toNat, z.2))
  have hFg : ∀ p ∈ Eg, actualBaseCell D b u p ∈ F' := by
    intro p hp
    let z : ℤ × (Fin 2 → ℤ) :=
      (⌊p.2 * (D : ℝ)⌋, fun k : Fin 2 => ⌊(D : ℝ) * (b p.1 + p.2 • u p.1) k⌋)
    refine Finset.mem_image.mpr ⟨z, hF p hp.1 (hRU hp.2.1), ?_⟩
    apply Prod.ext
    · simpa only [z, actualBaseCell, Int.floor_toNat, mul_comm]
    · rfl
  have hg := H D hD1 α ν b u hb hu R hR (fun x hx => hbu x (hRU hx)) Eg hEg hEgsub
    s τ₀ hs hτ₀ hlong hstopg F' hFg
  have hcard : (F'.card : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast Finset.card_image_le (s := F) (f := fun z : ℤ × (Fin 2 → ℤ) => (z.1.toNat, z.2))
  refine ⟨ps, hpswidths, hps, ?_⟩
  have hsub : E ∩ (R ×ˢ univ) ⊆ (E ∩ Gdᶜ ∩ (R ×ˢ univ)) ∪ Eg := by
    intro p hp
    by_cases hpg : p ∈ Gd
    · exact Or.inr ⟨⟨hp.1, hpg⟩, hp.2⟩
    · exact Or.inl ⟨⟨hp.1, hpg⟩, hp.2⟩
  calc
    _ ≤ (ν.prod volume) ((E ∩ Gdᶜ ∩ (R ×ˢ univ)) ∪ Eg) := measure_mono hsub
    _ ≤ (ν.prod volume) (E ∩ Gdᶜ ∩ (R ×ˢ univ)) + (ν.prod volume) Eg := measure_union_le _ _
    _ ≤ (ν.prod volume) (E ∩ Gdᶜ ∩ (R ×ˢ univ)) +
        (ENNReal.ofReal s * ν R +
          ENNReal.ofReal (C * τ₀ * (D : ℝ) ^ ε / (s * (D : ℝ) ^ 3) * (F'.card : ℝ))) :=
      add_le_add (le_refl _) hg
    _ ≤ _ := by
      rw [← add_assoc]
      apply add_le_add (le_refl _)
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hcard (by positivity)

theorem greedyPieces_incidence_floor {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] {b u : α → EuclideanSpace ℝ (Fin 2)}
    (hb : Measurable b) (hu : Measurable u) {U : Set α} (hU : MeasurableSet U)
    {E : Set (α × ℝ)} (hE : MeasurableSet E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {τ₀ : ℝ} {ps : List PlanarPlank}
    (hps : GreedyEligible (ν.withDensity (incidenceDuration E)) (fun p => p.lines b u)
      (fun p => τ₀ * p.area) U ps) :
    ∀ z ∈ greedyPieces (fun p => p.lines b u) U ps,
      ENNReal.ofReal (τ₀ * z.1.area) ≤ (ν.prod volume) (E ∩ (z.2 ×ˢ univ)) := by
  haveI := finite_duration_law ν hE hunit
  intro z hz
  have h := ENNReal.ofReal_le_ofReal (greedyPieces_floor hps z hz)
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
    duration_withDensity_apply ν hE
      (measurableSet_greedyPieces (fun p => p.lines b u)
        (fun p => p.measurableSet_lines hb hu) hU ps z hz)] at h
  exact h

end Submission.Obl.k4_initial_horizon_bound
