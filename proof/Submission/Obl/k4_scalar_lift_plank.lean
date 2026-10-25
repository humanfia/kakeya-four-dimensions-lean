import Mathlib
import ChallengeDeps
import Submission.Obl.k4_scalar_lift_plank.Numerics
import Submission.Obl.k4_scalar_lift_plank.Lift
set_option linter.unusedVariables false

/-!
# `Submission.k4_scalar_lift_plank`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_scalar_lift_plank`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_scalar_lift_plank/`
belong to this obligation.
-/

open Submission.Obl.k4_scalar_lift_plank

theorem Submission.k4_scalar_lift_plank : (∀ d c κ τ : ℝ, 0 ≤ d → d < 1 → 0 < c → 0 < κ → 0 < τ → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (b U : α → EuclideanSpace ℝ (Fin 2)) (E : Set (α × ℝ)) (F : Finset (ℤ × (Fin 2 → ℤ))), Measurable b → Measurable U → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → (∀ l : α, ‖b l‖ ≤ N ^ η ∧ ‖U l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) → ENNReal.ofReal (N ^ (-η)) ≤ (ν.prod MeasureTheory.volume) E → (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-2 - d) → (∀ l : α, ∀ t : ℝ, (l, t) ∈ E → (⌊t / (N ^ (-c))⌋, fun k : Fin 2 => ⌊(b l + t • U l) k / (N ^ (-c))⌋) ∈ F) → ∃ (b₀ w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (u v : ℝ), ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ inner ℝ e₁ e₂ = 0 ∧ N ^ (-c - κ) ≤ u ∧ u ≤ v ∧ v ≤ N ^ κ ∧ ENNReal.ofReal (N ^ (-c * (d - 1) - κ) * u * v) ≤ ν {l : α | ENNReal.ofReal (N ^ (-τ)) ≤ MeasureTheory.volume {t : ℝ | (l, t) ∈ E} ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (b l + t • U l - b₀ - t • w) e₁| ≤ u ∧ |inner ℝ (b l + t • U l - b₀ - t • w) e₂| ≤ v}) → ∀ d c κ τ : ℝ, 0 ≤ d → d < 1 → 0 < c → 0 < κ → 0 < τ → ∃ η : ℝ, 0 < η ∧ η ≤ κ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (a : α → EuclideanSpace ℝ (Fin 3)) (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)), Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → (∀ l : α, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) → ENNReal.ofReal (N ^ (-η)) ≤ (ν.prod MeasureTheory.volume) E → (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) → (∀ l : α, ∀ t : ℝ, (l, t) ∈ E → (⌊t / (N ^ (-c))⌋, ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / (N ^ (-c))⌋) ∈ F) → ∃ (b₀ w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (u v : ℝ), ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ inner ℝ e₁ e₂ = 0 ∧ N ^ (-c - κ) ≤ u ∧ u ≤ v ∧ v ≤ N ^ κ ∧ ENNReal.ofReal (N ^ (-c * (d - 1) - κ) * u * v) ≤ (ν.prod (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))) {z : α × ℝ | ENNReal.ofReal (N ^ (-τ)) ≤ MeasureTheory.volume {t : ℝ | (z.1, t) ∈ E} ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - z.2), z.2 + t * a z.1 2] - b₀ - t • w) e₁| ≤ u ∧ |inner ℝ (WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - z.2), z.2 + t * a z.1 2] - b₀ - t • w) e₂| ≤ v} := by
  intro hinv d c κ τ hd hd1 hc hκ hτ
  obtain ⟨η', hη', Ninv, hNinv, hInv⟩ := hinv d c κ τ hd hd1 hc hκ hτ
  let η : ℝ := min κ (η' / 4)
  have hη : 0 < η := lt_min hκ (by positivity)
  have hηκ : η ≤ κ := min_le_left _ _
  have hη4 : 4 * η ≤ η' := by
    have := min_le_right κ (η' / 4)
    dsimp [η]
    linarith
  have hηle : η ≤ η' := by linarith
  obtain ⟨Nlarge, hNlarge⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop (1000 : ℝ)))
  refine ⟨η, hη, hηκ, max 2 (max Ninv Nlarge), le_max_left _ _, ?_⟩
  intro N hN α _ ν a E F ha hE hEs hA hν hmass hF hcover
  have hN2 : 2 ≤ N := (le_max_left 2 _).trans hN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hNi : Ninv ≤ N := (le_trans (le_max_left _ _) (le_max_right 2 _)).trans hN
  have hNl : Nlarge ≤ N := (le_trans (le_max_right _ _) (le_max_right 2 _)).trans hN
  have hlarge : 1000 ≤ N ^ η := hNlarge N hNl
  have hM0 : 0 < N ^ η := Real.rpow_pos_of_pos hN0 _
  have hMon : N ^ η ≤ N ^ η' := Real.rpow_le_rpow_of_exponent_le hN1 hηle
  let ν' := ν.prod (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
  have hNorm : ∀ z : α × ℝ, ‖liftB a z‖ ≤ N ^ η' ∧ ‖liftU a z‖ ≤ N ^ η' := by
    have hAbsorb : 2 * N ^ η + 1 ≤ N ^ η' := by
      calc
        _ ≤ (N ^ η) ^ 2 := by nlinarith
        _ = N ^ (2 * η) := by
          rw [show 2 * η = η * (2 : ℕ) by norm_num; ring, Real.rpow_mul_natCast hN0.le]
        _ ≤ N ^ η' := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    intro z
    constructor
    · exact (norm_liftB_le a z).trans (by linarith [hA z.1])
    · exact (norm_liftU_le a z).trans
        ((by linarith [hA z.1] : 2 * ‖a z.1‖ + 1 ≤ 2 * N ^ η + 1).trans hAbsorb)
  have hPrior : ν' Set.univ ≤ ENNReal.ofReal (N ^ η') := by
    rw [show ν' Set.univ = ν Set.univ from lift_prior_univ ν]
    exact hν.trans (ENNReal.ofReal_le_ofReal hMon)
  have hMass : ENNReal.ofReal (N ^ (-η')) ≤
      (ν'.prod MeasureTheory.volume) (liftE E) := by
    rw [show (ν'.prod MeasureTheory.volume) (liftE E) =
      (ν.prod MeasureTheory.volume) E from lift_label_mass ν hE]
    exact (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : -η' ≤ -η))).trans hmass
  have hCells : ∀ z : α × ℝ, ∀ t : ℝ, (z, t) ∈ liftE E →
      (⌊t / (N ^ (-c))⌋, fun k : Fin 2 =>
        ⌊(liftB a z + t • liftU a z) k / (N ^ (-c))⌋) ∈
        liftedCells (N ^ (-c)) (2 * N ^ η) F := by
    intro z t hzt
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := (hEs hzt).2
    have hy : |(liftB a z + t • liftU a z) 1| ≤ 2 * N ^ η := by
      rw [lift_trace_one]
      calc
        _ ≤ |clip z.2| + |t * a z.1 2| := abs_add_le _ _
        _ ≤ 1 + N ^ η := by
          gcongr
          · exact abs_clip_le_one _
          · rw [abs_mul, abs_of_nonneg ht.1]
            exact (mul_le_mul ht.2 ((abs_coord_le (a z.1) 2).trans (hA z.1))
              (abs_nonneg _) (by norm_num)).trans (by simp)
        _ ≤ _ := by linarith
    have hScalar : (liftB a z + t • liftU a z) 0 +
        t * (liftB a z + t • liftU a z) 1 =
        a z.1 0 + t * a z.1 1 + t ^ 2 * a z.1 2 := lift_trace_recover a z t
    have := mem_liftedCells (Real.rpow_pos_of_pos hN0 _)
      (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith : -c ≤ 0))
      (by linarith : 1 ≤ 2 * N ^ η) ht hy F (by rw [hScalar]; exact hcover z.1 t hzt)
    convert this using 1
    congr 1
    funext k
    fin_cases k <;> rfl
  obtain ⟨b₀, w, e₁, e₂, u, v, he₁, he₂, heorth, hu, huv, hv, hPlank⟩ :=
    hInv N hNi (α × ℝ) ν' (liftB a) (liftU a) (liftE E)
      (liftedCells (N ^ (-c)) (2 * N ^ η) F)
      (measurable_liftB ha) (measurable_liftU ha) (measurableSet_liftE hE)
      (liftE_subset hEs) hNorm hPrior hMass
      (liftedCells_budget hN2 hc hη hη4 hlarge F hF) hCells
  refine ⟨b₀, w, e₁, e₂, u, v, he₁, he₂, heorth, hu, huv, hv, ?_⟩
  exact hPlank.trans (lift_plank_transfer ν a E (ENNReal.ofReal (N ^ (-τ))) b₀ w e₁ e₂ u v)
