import Mathlib
import Submission.Obl.k4_finite_narrowness_path_improvement.XAngularCharge
import Submission.Obl.k4_finite_narrowness_path_improvement.ChartCells

/-!
# Mass of listed charts with few velocity cells, over all worlds

`sum_measure_inter_le_of_lists`: labels known through lists of size `κ` overlap at most `κ`
times. `world_label_mass_le`: in one world, listed labels with at most `M` velocity cells carry
at most `κ M (α/β) μ(univ)` on the good set and `κ μ(bad)` on the rest. `level_mass_le`: the
`ω`-weighted sum over all worlds, as needed for one level of a critical path of X.
-/

namespace Submission.Obl.k4_finite_narrowness_path_improvement

open MeasureTheory

open scoped ENNReal

/-- Labels known through lists of size `κ` overlap at most `κ` times. -/
theorem sum_measure_inter_le_of_lists {P O : Type*} [MeasurableSpace P] (μ : Measure P)
    (obs : P → O) {ι : Type*} [Fintype ι] (F : ι → Set P) (hF : ∀ b, MeasurableSet (F b))
    (lst : O → Finset ι) (hlst : ∀ b, ∀ p ∈ F b, b ∈ lst (obs p)) (κ : ℕ)
    (hκ : ∀ o, (lst o).card ≤ κ) {X : Set P} (hX : MeasurableSet X) :
    ∑ b, μ (F b ∩ X) ≤ κ * μ X := by
  classical
  have hpt : ∀ p, ∑ b, (F b ∩ X).indicator (fun _ => (1 : ℝ≥0∞)) p ≤
      X.indicator (fun _ => (κ : ℝ≥0∞)) p := by
    intro p
    by_cases hpX : p ∈ X
    · rw [Set.indicator_of_mem hpX]
      calc ∑ b, (F b ∩ X).indicator (fun _ => (1 : ℝ≥0∞)) p
          = ∑ b ∈ Finset.univ.filter (fun b => p ∈ F b), (1 : ℝ≥0∞) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun b _ => ?_
            by_cases hb : p ∈ F b
            · simp [Set.indicator_of_mem (Set.mem_inter hb hpX), hb]
            · simp [hb]
        _ = (Finset.univ.filter (fun b => p ∈ F b)).card := by simp
        _ ≤ (lst (obs p)).card := by
            exact_mod_cast Finset.card_le_card fun b hb => hlst b p (by simpa using hb)
        _ ≤ κ := by exact_mod_cast hκ (obs p)
    · rw [Set.indicator_of_notMem hpX]
      refine le_of_eq (Finset.sum_eq_zero fun b _ => ?_)
      exact Set.indicator_of_notMem (fun h => hpX h.2) _
  calc ∑ b, μ (F b ∩ X) = ∑ b, ∫⁻ p, (F b ∩ X).indicator (fun _ => (1 : ℝ≥0∞)) p ∂μ := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [lintegral_indicator_const ((hF b).inter hX), one_mul]
    _ = ∫⁻ p, ∑ b, (F b ∩ X).indicator (fun _ => (1 : ℝ≥0∞)) p ∂μ := by
        rw [lintegral_finsetSum]
        intro b _
        exact measurable_const.indicator ((hF b).inter hX)
    _ ≤ ∫⁻ p, X.indicator (fun _ => (κ : ℝ≥0∞)) p ∂μ := lintegral_mono hpt
    _ = κ * μ X := by rw [lintegral_indicator_const hX]

/-- One world: listed labels with few velocity cells carry at most `κ M (α/β) μ(univ)` on the
good set and at most `κ μ(bad)` on the rest. -/
theorem world_label_mass_le {ν : Measure (ℕ × (Fin 6 → ℝ))} [IsProbabilityMeasure ν]
    {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) (B a u : ℝ)
    (g : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞) (hg : Measurable g)
    (hmap : Measure.map (gobs B a) ((ν.prod volume).restrict E) =
      (volume.prod Measure.count).withDensity g)
    (G : (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ℝ≥0∞) (hG : Measurable G)
    (hmapG : Measure.map (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ =>
        (gobs B a p, fun j : Fin 2 => ⌊(gv p.1) j / u⌋)) ((ν.prod volume).restrict E) =
      ((volume.prod Measure.count).prod Measure.count).withDensity G)
    {ι : Type*} [Fintype ι] (F : ι → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hF : ∀ b, MeasurableSet (F b)) (lst : EuclideanSpace ℝ (Fin 3) × ℤ → Finset ι)
    (hlst : ∀ b, ∀ p ∈ F b, b ∈ lst (gobs B a p)) (κ : ℕ) (hκ : ∀ o, (lst o).card ≤ κ)
    (V : ι → Finset (Fin 2 → ℤ))
    (hV : ∀ b, ∀ p ∈ F b, (fun j : Fin 2 => ⌊(gv p.1) j / u⌋) ∈ V b) (M : ℕ)
    (hM : ∀ b, (V b).card ≤ M) (α β : ℝ≥0∞) (hβ : β ≠ 0) :
    ∑ b, ((ν.prod volume).restrict E) (F b) ≤
      ((κ : ℝ≥0∞) * M * (α / β)) * ((ν.prod volume).restrict E) Set.univ +
        κ * ((ν.prod volume).restrict E) {p | α < G (gobs B a p, fun j : Fin 2 =>
          ⌊(gv p.1) j / u⌋) ∨ g (gobs B a p) < β} := by
  set μ := (ν.prod volume).restrict E with hμ
  have hcm := measurable_gcell u
  have hom := measurable_gobs B a
  set Good := {p : (ℕ × (Fin 6 → ℝ)) × ℝ | G (gobs B a p, fun j : Fin 2 =>
    ⌊(gv p.1) j / u⌋) ≤ α ∧ β ≤ g (gobs B a p)} with hGood
  set Bad := {p : (ℕ × (Fin 6 → ℝ)) × ℝ | α < G (gobs B a p, fun j : Fin 2 =>
    ⌊(gv p.1) j / u⌋) ∨ g (gobs B a p) < β} with hBad
  have hBm : MeasurableSet Bad := by
    refine (measurableSet_lt measurable_const (hG.comp (hom.prodMk hcm))).union ?_
    exact measurableSet_lt (hg.comp hom) measurable_const
  have hcover : ∀ b, F b ⊆ (F b ∩ Good) ∪ (F b ∩ Bad) := by
    intro b p hp
    by_cases h1 : G (gobs B a p, fun j : Fin 2 => ⌊(gv p.1) j / u⌋) ≤ α
    · by_cases h2 : β ≤ g (gobs B a p)
      · exact Or.inl ⟨hp, h1, h2⟩
      · exact Or.inr ⟨hp, Or.inr (not_le.mp h2)⟩
    · exact Or.inr ⟨hp, Or.inl (not_le.mp h1)⟩
  calc ∑ b, μ (F b) ≤ ∑ b, (μ (F b ∩ Good) + μ (F b ∩ Bad)) :=
        Finset.sum_le_sum fun b _ => (measure_mono (hcover b)).trans (measure_union_le _ _)
    _ = ∑ b, μ (F b ∩ Good) + ∑ b, μ (F b ∩ Bad) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add
        (x_known_label_charge hE B a u g hg hmap G hG hmapG F hF lst hlst κ hκ V hV M hM α β hβ)
        (sum_measure_inter_le_of_lists μ (gobs B a) F hF lst hlst κ hκ hBm)

/-- All worlds: the `ω`-weighted mass of listed charts with few velocity cells. -/
theorem level_mass_le {W C : ℕ} (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    [hν : ∀ γ, IsProbabilityMeasure (ν γ)] (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hE : ∀ γ, E γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) (B : Fin W → ℝ) (a u : ℝ)
    (g : Fin W → EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞) (hg : ∀ γ, Measurable (g γ))
    (hmap : ∀ γ, Measure.map (gobs (B γ) a) (((ν γ).prod volume).restrict (E γ)) =
      (volume.prod Measure.count).withDensity (g γ))
    (G : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ℝ≥0∞)
    (hG : ∀ γ, Measurable (G γ))
    (hmapG : ∀ γ, Measure.map (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ =>
        (gobs (B γ) a p, fun j : Fin 2 => ⌊(gv p.1) j / u⌋)) (((ν γ).prod volume).restrict (E γ)) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (G γ))
    (γb : Fin C → Fin W) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hF : ∀ b, MeasurableSet (F b)) (hFE : ∀ b, F b ⊆ E (γb b))
    (lst : Fin W → EuclideanSpace ℝ (Fin 3) × ℤ → Finset (Fin C))
    (hlst : ∀ b, ∀ p ∈ F b, b ∈ lst (γb b) (gobs (B (γb b)) a p)) (κ : ℕ)
    (hκ : ∀ γ o, (lst γ o).card ≤ κ) (V : Fin C → Finset (Fin 2 → ℤ))
    (hV : ∀ b, ∀ p ∈ F b, (fun j : Fin 2 => ⌊(gv p.1) j / u⌋) ∈ V b) (M : ℕ)
    (hM : ∀ b, (V b).card ≤ M) (α β : ℝ≥0∞) (hβ : β ≠ 0) :
    ∑ b, ENNReal.ofReal (ω (γb b)) * ((ν (γb b)).prod volume) (F b) ≤
      ((κ : ℝ≥0∞) * M * (α / β)) *
          ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) Set.univ +
        κ * ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ))
          {p | α < G γ (gobs (B γ) a p, fun j : Fin 2 => ⌊(gv p.1) j / u⌋) ∨
            g γ (gobs (B γ) a p) < β} := by
  classical
  have hrestr : ∀ b, ((ν (γb b)).prod volume) (F b) =
      (((ν (γb b)).prod volume).restrict (E (γb b))) (F b) := by
    intro b
    rw [Measure.restrict_apply (hF b), Set.inter_eq_left.mpr (hFE b)]
  have hworld : ∀ γ, ∑ b ∈ Finset.univ.filter (fun b => γb b = γ),
      (((ν γ).prod volume).restrict (E γ)) (F b) ≤
      ((κ : ℝ≥0∞) * M * (α / β)) * (((ν γ).prod volume).restrict (E γ)) Set.univ +
        κ * (((ν γ).prod volume).restrict (E γ))
          {p | α < G γ (gobs (B γ) a p, fun j : Fin 2 => ⌊(gv p.1) j / u⌋) ∨
            g γ (gobs (B γ) a p) < β} := by
    intro γ
    have hw := world_label_mass_le (hE γ) (B γ) a u (g γ) (hg γ) (hmap γ) (G γ) (hG γ)
      (hmapG γ) (ι := {b // γb b = γ}) (fun b => F b.1) (fun b => hF b.1)
      (fun o => (lst γ o).subtype (fun b => γb b = γ))
      (by
        intro b p hp
        rw [Finset.mem_subtype]
        have := hlst b.1 p hp
        rwa [b.2] at this)
      κ
      (by
        intro o
        rw [Finset.card_subtype]
        exact (Finset.card_filter_le _ _).trans (hκ γ o))
      (fun b => V b.1) (fun b p hp => hV b.1 p hp) M (fun b => hM b.1) α β hβ
    rw [Finset.sum_subtype (p := fun b => γb b = γ) (Finset.univ.filter (fun b => γb b = γ))
      (by simp) (fun b => (((ν γ).prod volume).restrict (E γ)) (F b))]
    exact hw
  calc ∑ b, ENNReal.ofReal (ω (γb b)) * ((ν (γb b)).prod volume) (F b)
      = ∑ γ, ∑ b ∈ Finset.univ.filter (fun b => γb b = γ),
          ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) (F b) := by
        rw [← Finset.sum_fiberwise Finset.univ γb]
        refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_filter] at hb
        rw [hrestr b, hb.2]
    _ = ∑ γ, ENNReal.ofReal (ω γ) * ∑ b ∈ Finset.univ.filter (fun b => γb b = γ),
          (((ν γ).prod volume).restrict (E γ)) (F b) := by
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ γ, ENNReal.ofReal (ω γ) * (((κ : ℝ≥0∞) * M * (α / β)) *
          (((ν γ).prod volume).restrict (E γ)) Set.univ +
        κ * (((ν γ).prod volume).restrict (E γ))
          {p | α < G γ (gobs (B γ) a p, fun j : Fin 2 => ⌊(gv p.1) j / u⌋) ∨
            g γ (gobs (B γ) a p) < β}) :=
        Finset.sum_le_sum fun γ _ => by gcongr; exact hworld γ
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring

end Submission.Obl.k4_finite_narrowness_path_improvement
