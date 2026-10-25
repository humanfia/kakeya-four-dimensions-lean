import Submission.Obl.k4_initial_horizon_bound.CellResidualEstimate
import Submission.Obl.k4_initial_horizon_bound.QuadraticGreedy

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_initial_horizon_bound

open Submission.Lib.K4ContinuousPlanks

structure PlanarPlank where
  center : EuclideanSpace ℝ (Fin 2)
  speed : EuclideanSpace ℝ (Fin 2)
  axis₁ : EuclideanSpace ℝ (Fin 2)
  axis₂ : EuclideanSpace ℝ (Fin 2)
  thin : ℝ
  wide : ℝ
  unit₁ : ‖axis₁‖ = 1
  unit₂ : ‖axis₂‖ = 1
  orthogonal : inner ℝ axis₁ axis₂ = 0
  thin_pos : 0 < thin
  widths_le : thin ≤ wide

def PlanarPlank.area (p : PlanarPlank) : ℝ := p.thin * p.wide

theorem PlanarPlank.area_pos (p : PlanarPlank) : 0 < p.area :=
  mul_pos p.thin_pos (p.thin_pos.trans_le p.widths_le)

def PlanarPlank.lines {α : Type*} (p : PlanarPlank)
    (b u : α → EuclideanSpace ℝ (Fin 2)) : Set α :=
  {x | InFullTracePlank (b x) (u x) p.center p.speed p.axis₁ p.axis₂ p.thin p.wide}

theorem PlanarPlank.measurableSet_lines {α : Type*} [MeasurableSpace α]
    (p : PlanarPlank) {b u : α → EuclideanSpace ℝ (Fin 2)}
    (hb : Measurable b) (hu : Measurable u) : MeasurableSet (p.lines b u) :=
  measurableSet_fullTracePlank b u hb hu p.center p.speed p.axis₁ p.axis₂ p.thin p.wide

/-- Finite exact greedy assignments with true linear-in-area floors. The
remaining original incidence mass is bounded by the bad-cell budget,
duration deletion, and the old-cell estimate. All masses use the original law. -/
theorem normalized_greedy_plank_cover (ε : ℝ) (hε : 0 < ε) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
      (b u : α → EuclideanSpace ℝ (Fin 2)),
    Measurable b → Measurable u → (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
    ∀ E G : Set (α × ℝ), MeasurableSet E → MeasurableSet G → G ⊆ E →
      E ⊆ univ ×ˢ Icc (0 : ℝ) 1 →
    ∀ τ a n B bad : ℝ, 0 < τ → 0 < a → 0 < n → 0 < B → 0 ≤ bad →
      (D : ℝ) ^ (-η) ≤ τ →
    (∀ p : PlanarPlank,
      (ν.withDensity (incidenceDuration E)).real (p.lines b u) ≤ B * p.area ^ 2) →
    (ν.prod volume) (E \ G) ≤ ENNReal.ofReal bad →
    ∀ (old : Measure (α × ℝ)) [IsFiniteMeasure old] (F : Finset (ℕ × (Fin 2 → ℤ))),
      (∀ p ∈ G, actualBaseCell D b u p ∈ F) →
      (∀ z ∈ F, n / (D : ℝ) ^ 3 ≤ old.real (actualBaseCell D b u ⁻¹' {z})) →
    ∃ ps : List PlanarPlank,
      GreedyEligible (ν.withDensity (incidenceDuration E)) (fun p => p.lines b u)
        (fun p => a * p.area) univ ps ∧
      (a ^ 2 / B) * (ps.length : ℝ) ≤ (ν.withDensity (incidenceDuration E)).real univ ∧
      (ν.withDensity (incidenceDuration E)).real univ ≤
        ((greedyPieces (fun p => p.lines b u) univ ps).map
          (fun z => (ν.withDensity (incidenceDuration E)).real z.2)).sum +
        bad + τ * ν.real univ + C * (a / n) * (D : ℝ) ^ ε / τ * old.real univ := by
  classical
  obtain ⟨η, hη, C, hC, H⟩ := stopped_residual_old_cell_bound ε hε
  refine ⟨η, C, hη, hC, ?_⟩
  intro D hD α _ ν _ b u hb hu hbu E G hE hG hGE hunit τ a n B bad
    hτ ha hn hB hbad hlong hcap hbadmass old _ F hF hfloor
  let μ := ν.withDensity (incidenceDuration E)
  haveI : IsFiniteMeasure μ := finite_duration_law ν hE hunit
  let S : PlanarPlank → Set α := fun p => p.lines b u
  have hS : ∀ p, MeasurableSet (S p) := fun p => p.measurableSet_lines hb hu
  obtain ⟨ps, hps, hlen, hstop⟩ := exists_quadratic_greedy_packing μ S hS
    PlanarPlank.area (fun p => p.area_pos.le) ha hB hcap univ
  let R := greedyResidual S univ ps
  have hR : MeasurableSet R := measurableSet_greedyResidual S hS MeasurableSet.univ ps
  let G' : Set (α × ℝ) := G ∩ (R ×ˢ univ)
  have hG' : MeasurableSet G' := hG.inter (hR.prod MeasurableSet.univ)
  have hG'unit : G' ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun p hp => hunit (hGE hp.1)
  have hstop' : ∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (v z : ℝ),
      ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 0 < v → v ≤ z →
      (ν.withDensity (incidenceDuration G'))
        {x | InFullTracePlank (b x) (u x) c w e₁ e₂ v z} ≤ ENNReal.ofReal (a * v * z) := by
    intro c w e₁ e₂ v z he₁ he₂ he hv hvz
    let p : PlanarPlank := ⟨c, w, e₁, e₂, v, z, he₁, he₂, he, hv, hvz⟩
    have hbound : μ (R ∩ S p) ≤ ENNReal.ofReal (a * p.area) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (hstop p)
    have heq : μ (R ∩ S p) = (ν.prod volume) (E ∩ ((R ∩ S p) ×ˢ univ)) :=
      duration_withDensity_apply ν hE (hR.inter (hS p))
    have hsub : G' ∩ (S p ×ˢ univ) ⊆ E ∩ ((R ∩ S p) ×ˢ univ) := by
      rintro ⟨x, t⟩ ⟨⟨hxG, hxR, _⟩, hxS, _⟩
      exact ⟨hGE hxG, ⟨hxR, hxS⟩, mem_univ _⟩
    have hmass := (measure_mono (μ := ν.prod volume) hsub).trans (heq ▸ hbound)
    rw [← duration_withDensity_apply ν hG' (hS p)] at hmass
    simpa only [S, PlanarPlank.lines, PlanarPlank.area, p, mul_assoc] using hmass
  have hg := H D hD α ν b u hb hu hbu G' hG' hG'unit τ a n hτ ha hn hlong
    hstop' old F (fun p hp => hF p hp.1) hfloor
  have hres : μ R ≤ ENNReal.ofReal bad + ENNReal.ofReal τ * ν univ +
      ENNReal.ofReal (C * (a / n) * (D : ℝ) ^ ε / τ * old.real univ) := by
    rw [duration_withDensity_apply ν hE hR]
    have hsub : E ∩ (R ×ˢ univ) ⊆ (E \ G) ∪ G' := by
      intro p hp
      by_cases hpG : p ∈ G
      · exact Or.inr ⟨hpG, hp.2⟩
      · exact Or.inl ⟨hp.1, hpG⟩
    calc
      _ ≤ (ν.prod volume) ((E \ G) ∪ G') := measure_mono hsub
      _ ≤ (ν.prod volume) (E \ G) + (ν.prod volume) G' := measure_union_le _ _
      _ ≤ ENNReal.ofReal bad +
          (ENNReal.ofReal τ * ν univ +
            ENNReal.ofReal (C * (a / n) * (D : ℝ) ^ ε / τ * old.real univ)) :=
        add_le_add hbadmass hg
      _ = _ := by ac_rfl
  have hresreal : μ.real R ≤ bad + τ * ν.real univ +
      C * (a / n) * (D : ℝ) ^ ε / τ * old.real univ := by
    have hcoef : 0 ≤ C * (a / n) * (D : ℝ) ^ ε / τ * old.real univ := by positivity
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    convert hres using 1
    rw [ENNReal.ofReal_add (by positivity) hcoef, ENNReal.ofReal_add hbad (by positivity),
      ENNReal.ofReal_mul hτ.le]
    simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top ν _)]
  have hid := greedy_mass_identity μ S hS univ ps
  refine ⟨ps, hps, hlen, ?_⟩
  change _ ≤ _
  linarith

end Submission.Obl.k4_initial_horizon_bound
