import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedCells

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced fit: collision sets and their mass bounds

`Scol D p u₀ β₀` are the collisions (common `p`-bin at a common time `u`) of trajectories labeled
at the starting time `u₀`, the first one starting in bin `β₀`. At one time their pair weight is
at most `((2K/p+2) K p^(1+d))²` (`pairWeight_le`), and on a `(u, v, v')` cell of side `p` their
mass is at most `p · K p^(1+d) · (36K²+3) K p^(1+d)` (`cellMass_le`).
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Labeled incidences of trajectories labeled at `u₀`. -/
def Elab (D : SlicedData Ω) (u₀ : ℝ) : Set (Ω × ℝ) := D.E ∩ {q | (q.1, u₀) ∈ D.E}

/-- Collisions of trajectories labeled at `u₀`, with the first starting scalar in bin `β₀`. -/
def Scol (D : SlicedData Ω) (p u₀ : ℝ) (β₀ : ℤ) : Set ((Ω × Ω) × ℝ) :=
  timeColl (Elab D u₀) (fun l u => ⌊D.L l u / p⌋) ∩ {x | ⌊D.L x.1.1 u₀ / p⌋ = β₀}

/-- A `(u, v, v')` cell. -/
def cellSet (D : SlicedData Ω) (p : ℝ) (i c₁ c₂ : ℤ) : Set ((Ω × Ω) × ℝ) :=
  {x | ⌊x.2 / p⌋ = i ∧ ⌊D.v x.1.1 / p⌋ = c₁ ∧ ⌊D.v x.1.2 / p⌋ = c₂}

theorem measurableSet_Elab {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (u₀ : ℝ) :
    MeasurableSet (Elab D u₀) :=
  H.measE.inter ((measurable_fst.prodMk measurable_const) H.measE)

theorem measurable_L_at {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (u : ℝ) :
    Measurable (fun l => D.L l u) :=
  H.measL.comp (measurable_id.prodMk measurable_const)

theorem measurableSet_Scol {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (u₀ : ℝ)
    (β₀ : ℤ) : MeasurableSet (Scol D p u₀ β₀) := by
  have hbin : Measurable (fun q : Ω × ℝ => ⌊D.L q.1 q.2 / p⌋) :=
    Int.measurable_floor.comp (H.measL.div_const p)
  refine (measurableSet_timeColl (bin := fun l u => ⌊D.L l u / p⌋) (measurableSet_Elab H u₀)
    hbin).inter ?_
  exact (Int.measurable_floor.comp (((measurable_L_at H u₀).div_const p).comp
    (measurable_fst.comp measurable_fst))) (measurableSet_singleton β₀)

theorem measurableSet_cellSet {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d)
    (i c₁ c₂ : ℤ) : MeasurableSet (cellSet D p i c₁ c₂) := by
  have h1 : Measurable (fun x : (Ω × Ω) × ℝ => ⌊x.2 / p⌋) :=
    Int.measurable_floor.comp (measurable_snd.div_const p)
  have h2 : Measurable (fun x : (Ω × Ω) × ℝ => ⌊D.v x.1.1 / p⌋) :=
    Int.measurable_floor.comp ((H.measv.comp (measurable_fst.comp measurable_fst)).div_const p)
  have h3 : Measurable (fun x : (Ω × Ω) × ℝ => ⌊D.v x.1.2 / p⌋) :=
    Int.measurable_floor.comp ((H.measv.comp (measurable_snd.comp measurable_fst)).div_const p)
  exact (h1 (measurableSet_singleton i)).inter ((h2 (measurableSet_singleton c₁)).inter
    (h3 (measurableSet_singleton c₂)))

/-- **Pair weight at one time**: `(ν⊗ν)` of the time slice of `Scol` is at most `c²`,
`c = (2K/p+2) K p^(1+d)`. -/
theorem pairWeight_le {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hp : 0 < p)
    (hK : 0 ≤ K) (u₀ : ℝ) (β₀ : ℤ) (u : ℝ) :
    (D.ν.prod D.ν) ((fun x => (x, u)) ⁻¹' Scol D p u₀ β₀) ≤
      ENNReal.ofReal ((2 * K / p + 2) * (K * p ^ (1 + d))) *
        ENNReal.ofReal ((2 * K / p + 2) * (K * p ^ (1 + d))) := by
  have := H.finite
  set c := ENNReal.ofReal ((2 * K / p + 2) * (K * p ^ (1 + d))) with hc
  have hS : MeasurableSet ((fun x : Ω × Ω => (x, u)) ⁻¹' Scol D p u₀ β₀) :=
    measurable_prodMk_right (measurableSet_Scol H u₀ β₀)
  set A : Set Ω := {l | (l, u₀) ∈ D.E ∧ ⌊D.L l u₀ / p⌋ = β₀ ∧ True} with hA
  have hAm : MeasurableSet A := by
    have h1 : MeasurableSet {l | (l, u₀) ∈ D.E} := measurable_prodMk_right H.measE
    have h2 : MeasurableSet {l | ⌊D.L l u₀ / p⌋ = β₀} :=
      (Int.measurable_floor.comp ((measurable_L_at H u₀).div_const p)) (measurableSet_singleton _)
    have : A = {l | (l, u₀) ∈ D.E} ∩ {l | ⌊D.L l u₀ / p⌋ = β₀} := by ext l; simp [hA]
    rw [this]; exact h1.inter h2
  rw [Measure.prod_apply hS]
  calc ∫⁻ l, D.ν (Prod.mk l ⁻¹' ((fun x : Ω × Ω => (x, u)) ⁻¹' Scol D p u₀ β₀)) ∂D.ν
      ≤ ∫⁻ l, A.indicator (fun _ => c) l ∂D.ν := by
        apply lintegral_mono
        intro l
        dsimp only
        by_cases hl : l ∈ A
        · rw [indicator_of_mem hl]
          have hsub : Prod.mk l ⁻¹' ((fun x : Ω × Ω => (x, u)) ⁻¹' Scol D p u₀ β₀) ⊆
              {l' | (l', u) ∈ D.E ∧ ⌊D.L l' u / p⌋ = ⌊D.L l u / p⌋ ∧ True} := by
            rintro l' ⟨⟨_, ⟨hl'u, _⟩, hb⟩, _⟩
            exact ⟨hl'u, hb.symm, trivial⟩
          exact (measure_mono hsub).trans (cap_sum_v H hp hK u _ _)
        · rw [indicator_of_notMem hl]
          have : Prod.mk l ⁻¹' ((fun x : Ω × Ω => (x, u)) ⁻¹' Scol D p u₀ β₀) = ∅ := by
            ext l'; simp only [mem_preimage, mem_empty_iff_false, iff_false]
            rintro ⟨⟨⟨_, hl0⟩, _, _⟩, hβ⟩
            exact hl ⟨hl0, hβ, trivial⟩
          rw [this, measure_empty]
    _ = c * D.ν A := lintegral_indicator_const hAm c
    _ ≤ c * c := by gcongr; exact cap_sum_v H hp hK u₀ β₀ (fun _ => True)


theorem floor_div_eq_iff {u p : ℝ} (hp : 0 < p) (i : ℤ) :
    ⌊u / p⌋ = i ↔ u ∈ Ico ((i : ℝ) * p) (((i : ℝ) + 1) * p) := by
  rw [Int.floor_eq_iff, mem_Ico, le_div_iff₀ hp, div_lt_iff₀ hp]

theorem volume_floor_div_eq {p : ℝ} (hp : 0 < p) (i : ℤ) :
    volume {u : ℝ | ⌊u / p⌋ = i} = ENNReal.ofReal p := by
  have : {u : ℝ | ⌊u / p⌋ = i} = Ico ((i : ℝ) * p) (((i : ℝ) + 1) * p) := by
    ext u; exact floor_div_eq_iff hp i
  rw [this, Real.volume_Ico]; congr 1; ring

/-- **Cell mass**: a `(u, v, v')` cell of side `p` carries collision mass at most
`p · K p^(1+d) · (36K²+3) K p^(1+d)`. -/
theorem cellMass_le {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hp : 0 < p)
    (hK : 1 ≤ K) {u₀ : ℝ} (hu₀ : u₀ ∈ Icc (0:ℝ) 1) (β₀ i c₁ c₂ : ℤ) :
    ((D.ν.prod D.ν).prod volume) (Scol D p u₀ β₀ ∩ cellSet D p i c₁ c₂) ≤
      ENNReal.ofReal p * (ENNReal.ofReal (K * p ^ (1 + d)) *
        ENNReal.ofReal ((36 * K ^ 2 + 3) * (K * p ^ (1 + d)))) := by
  have := H.finite
  have hm := (measurableSet_Scol H u₀ β₀).inter (measurableSet_cellSet H i c₁ c₂)
  set B := ENNReal.ofReal (K * p ^ (1 + d)) * ENNReal.ofReal ((36 * K ^ 2 + 3) * (K * p ^ (1 + d)))
    with hB
  have hbinm : MeasurableSet {u : ℝ | ⌊u / p⌋ = i} :=
    (Int.measurable_floor.comp (measurable_id.div_const p)) (measurableSet_singleton i)
  rw [Measure.prod_apply_symm hm]
  calc ∫⁻ u, (D.ν.prod D.ν) ((fun x => (x, u)) ⁻¹' (Scol D p u₀ β₀ ∩ cellSet D p i c₁ c₂))
      ≤ ∫⁻ u, {u : ℝ | ⌊u / p⌋ = i}.indicator (fun _ => B) u := by
        apply lintegral_mono
        intro u
        dsimp only
        by_cases hu : ⌊u / p⌋ = i
        · rw [indicator_of_mem (show u ∈ {u : ℝ | ⌊u / p⌋ = i} from hu)]
          have hSu : MeasurableSet ((fun x : Ω × Ω => (x, u)) ⁻¹'
              (Scol D p u₀ β₀ ∩ cellSet D p i c₁ c₂)) := measurable_prodMk_right hm
          set A' : Set Ω := {l | (l, u₀) ∈ D.E ∧ ⌊D.v l / p⌋ = c₁ ∧ ⌊D.L l u₀ / p⌋ = β₀}
            with hA'
          have hA'm : MeasurableSet A' := by
            have h1 : MeasurableSet {l | (l, u₀) ∈ D.E} := measurable_prodMk_right H.measE
            have h2 : MeasurableSet {l | ⌊D.v l / p⌋ = c₁} :=
              (Int.measurable_floor.comp (H.measv.div_const p)) (measurableSet_singleton _)
            have h3 : MeasurableSet {l | ⌊D.L l u₀ / p⌋ = β₀} :=
              (Int.measurable_floor.comp ((measurable_L_at H u₀).div_const p))
                (measurableSet_singleton _)
            have : A' = {l | (l, u₀) ∈ D.E} ∩ ({l | ⌊D.v l / p⌋ = c₁} ∩
                {l | ⌊D.L l u₀ / p⌋ = β₀}) := by ext l; simp [hA']
            rw [this]; exact h1.inter (h2.inter h3)
          set SB := startBins D p K u₀ β₀ i c₁ c₂
          set c2b := ENNReal.ofReal ((36 * K ^ 2 + 3) * (K * p ^ (1 + d)))
          rw [Measure.prod_apply hSu]
          calc ∫⁻ l, D.ν (Prod.mk l ⁻¹' ((fun x : Ω × Ω => (x, u)) ⁻¹'
                (Scol D p u₀ β₀ ∩ cellSet D p i c₁ c₂))) ∂D.ν
              ≤ ∫⁻ l, A'.indicator (fun _ => c2b) l ∂D.ν := by
                apply lintegral_mono
                intro l
                dsimp only
                by_cases hl : l ∈ A'
                · rw [indicator_of_mem hl]
                  have hsub : Prod.mk l ⁻¹' ((fun x : Ω × Ω => (x, u)) ⁻¹'
                      (Scol D p u₀ β₀ ∩ cellSet D p i c₁ c₂)) ⊆
                      ⋃ b ∈ SB, {l' | (l', u₀) ∈ D.E ∧ ⌊D.v l' / p⌋ = c₂ ∧ ⌊D.L l' u₀ / p⌋ = b} := by
                    rintro l' ⟨⟨⟨⟨hlu, hl0⟩, ⟨hl'u, hl'0⟩, hb⟩, hβ⟩, ⟨hi, hc1, hc2⟩⟩
                    have hconf := start_bin_confined H hp hK hu₀ hl0 hl'0 hlu hl'u hb hβ
                    simp only at hi hc1 hc2
                    rw [hi, hc1, hc2] at hconf
                    exact mem_iUnion₂.2 ⟨_, hconf, hl'0, hc2, rfl⟩
                  calc D.ν (Prod.mk l ⁻¹' ((fun x : Ω × Ω => (x, u)) ⁻¹'
                        (Scol D p u₀ β₀ ∩ cellSet D p i c₁ c₂)))
                      ≤ ∑ b ∈ SB, D.ν {l' | (l', u₀) ∈ D.E ∧ ⌊D.v l' / p⌋ = c₂ ∧
                          ⌊D.L l' u₀ / p⌋ = b} := (measure_mono hsub).trans
                        (measure_biUnion_finset_le _ _)
                    _ ≤ ∑ _b ∈ SB, ENNReal.ofReal (K * p ^ (1 + d)) :=
                        Finset.sum_le_sum (fun b _ => H.cap u₀ c₂ b)
                    _ = SB.card * ENNReal.ofReal (K * p ^ (1 + d)) := by
                        rw [Finset.sum_const, nsmul_eq_mul]
                    _ ≤ c2b := by
                        simp only [c2b]
                        rw [ENNReal.ofReal_mul (p := 36 * K ^ 2 + 3) (by positivity)]
                        gcongr
                        rw [← ENNReal.ofReal_natCast]
                        exact ENNReal.ofReal_le_ofReal
                          (card_startBins D p K u₀ β₀ i c₁ c₂ (by linarith))
                · rw [indicator_of_notMem hl]
                  have : Prod.mk l ⁻¹' ((fun x : Ω × Ω => (x, u)) ⁻¹'
                      (Scol D p u₀ β₀ ∩ cellSet D p i c₁ c₂)) = ∅ := by
                    ext l'; simp only [mem_preimage, mem_empty_iff_false, iff_false]
                    rintro ⟨⟨⟨⟨_, hl0⟩, _, _⟩, hβ⟩, ⟨_, hc1, _⟩⟩
                    exact hl ⟨hl0, hc1, hβ⟩
                  rw [this, measure_empty]
            _ = c2b * D.ν A' := lintegral_indicator_const hA'm c2b
            _ ≤ c2b * ENNReal.ofReal (K * p ^ (1 + d)) := by gcongr; exact H.cap u₀ c₁ β₀
            _ = B := by rw [hB, mul_comm]
        · rw [indicator_of_notMem (show u ∉ {u : ℝ | ⌊u / p⌋ = i} from hu)]
          have : (fun x : Ω × Ω => (x, u)) ⁻¹' (Scol D p u₀ β₀ ∩ cellSet D p i c₁ c₂) = ∅ := by
            ext x; simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
            intro _ hc; exact hu hc.1
          rw [this, measure_empty]
    _ = B * volume {u : ℝ | ⌊u / p⌋ = i} := lintegral_indicator_const hbinm B
    _ = ENNReal.ofReal p * B := by rw [volume_floor_div_eq hp, mul_comm]

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
