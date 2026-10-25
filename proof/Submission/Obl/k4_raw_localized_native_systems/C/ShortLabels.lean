import Submission.Obl.k4_raw_localized_native_systems.C.GoodPathMass
import Submission.Obl.k4_raw_localized_native_systems.C.Q2BadPair

/-
Adapted from this LOT tree, o178, session x0596, `ShortLabels.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Charts with a short major axis carry little mass

If both columns of a chart frame are shorter than `lam`, every assigned
trajectory has its velocity within `4 κ 2^T lam` of the chart's centre
velocity.  When this is at most the angular bin width, the velocity bin is in
the `3 × 3` block of the centre's bin; the chart being listed by the terminal
observation, angular charging bounds the mass of such incidences by
`N^(-S u + 2τ) ⋅ 9 κ_L` times the world mass.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

theorem norm_toEuclideanLin_le_longCol (Q : Matrix (Fin 2) (Fin 2) ℝ) (w : Plane) :
    ‖Matrix.toEuclideanLin Q w‖ ≤ 2 * ‖longCol Q‖ * ‖w‖ := by
  rw [toEuclideanLin_fin2_eq]
  obtain ⟨h0, h1⟩ := longCol_norm_ge Q
  have hw0 := abs_coord_le_norm_fin2 w 0
  have hw1 := abs_coord_le_norm_fin2 w 1
  calc ‖w 0 • col0 Q + w 1 • col1 Q‖ ≤ ‖w 0 • col0 Q‖ + ‖w 1 • col1 Q‖ := norm_add_le _ _
    _ = |w 0| * ‖col0 Q‖ + |w 1| * ‖col1 Q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖w‖ * ‖longCol Q‖ + ‖w‖ * ‖longCol Q‖ := by
        gcongr
    _ = 2 * ‖longCol Q‖ * ‖w‖ := by ring

/-- Velocities of a chart are within `2 ⋅ 2κ 2^T ⋅ ‖longCol‖` of its centre velocity. -/
theorem ChartsHyp.velocity_near_centre {M D : ℕ} {κ r : ℝ} {a : Atlas p k}
    {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex) (b : Fin a.C) {l : Line}
    (hl : l ∈ a.A b) : ‖v l - a.u b‖ ≤ 4 * κ * (2 : ℝ) ^ a.T * ‖longCol (a.Q b)‖ := by
  obtain ⟨h₁, h₂⟩ := hc.ends b hl
  have hv := Submission.Lib.K4XInterface.velocity_le_of_two_times (a.Q b) (a.c b) (a.u b) l
    (show ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T <
      ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T + 1 / (2 : ℝ) ^ a.T by
        have : (0 : ℝ) < 1 / (2 : ℝ) ^ a.T := by positivity
        linarith) h₁ h₂
  rw [add_sub_cancel_left, div_div_eq_mul_div, div_one] at hv
  have heq : v l - a.u b = Matrix.toEuclideanLin (a.Q b)
      (Matrix.toEuclideanLin (a.Q b)⁻¹ (v l - a.u b)) :=
    (Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel (a.Q b) (hc.det_ne b) _).symm
  rw [heq]
  refine (norm_toEuclideanLin_le_longCol _ _).trans ?_
  calc 2 * ‖longCol (a.Q b)‖ * ‖Matrix.toEuclideanLin (a.Q b)⁻¹ (v l - a.u b)‖
      ≤ 2 * ‖longCol (a.Q b)‖ * (2 * κ * (2 : ℝ) ^ a.T) := by gcongr; exact hv
    _ = 4 * κ * (2 : ℝ) ^ a.T * ‖longCol (a.Q b)‖ := by ring

/-- Velocity bins listed by short charts. -/
def shortBins (a : Atlas p k) (γ : Fin (p.W k)) (lam w : ℝ) (o : Observation) :
    Finset (Fin 2 → ℤ) := by
  classical
  exact ((a.lst γ o).filter (fun b => ‖longCol (a.Q b)‖ < lam)).biUnion
    fun b => nbhd (binOf w (a.u b))

theorem card_shortBins_le (a : Atlas p k) (γ : Fin (p.W k)) (lam w : ℝ) (o : Observation)
    {m : ℕ} (hm : (a.lst γ o).card ≤ m) : (shortBins a γ lam w o).card ≤ 9 * m := by
  classical
  unfold shortBins
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ b ∈ (a.lst γ o).filter (fun b => ‖longCol (a.Q b)‖ < lam),
        (nbhd (binOf w (a.u b))).card
      ≤ ∑ _b ∈ (a.lst γ o).filter (fun b => ‖longCol (a.Q b)‖ < lam), 9 :=
        Finset.sum_le_sum fun b _ => card_nbhd_le _
    _ = 9 * ((a.lst γ o).filter (fun b => ‖longCol (a.Q b)‖ < lam)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 9 * m := by gcongr; exact (Finset.card_filter_le _ _).trans hm

theorem measurableSet_shortBins (a : Atlas p k) (γ : Fin (p.W k)) (lam w : ℝ)
    (hmeas : ∀ b, MeasurableSet {o | b ∈ a.lst γ o}) (z : Fin 2 → ℤ) :
    MeasurableSet {o | z ∈ shortBins a γ lam w o} := by
  classical
  have : {o | z ∈ shortBins a γ lam w o} =
      ⋃ b : Fin a.C, {o | (‖longCol (a.Q b)‖ < lam ∧ z ∈ nbhd (binOf w (a.u b))) ∧
        b ∈ a.lst γ o} := by
    ext o
    simp only [shortBins, Finset.mem_biUnion, Finset.mem_filter, Set.mem_setOf_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨b, ⟨hb, hs⟩, hz⟩; exact ⟨b, ⟨hs, hz⟩, hb⟩
    · rintro ⟨b, ⟨hs, hz⟩, hb⟩; exact ⟨b, ⟨hb, hs⟩, hz⟩
  rw [this]
  refine MeasurableSet.iUnion fun b => ?_
  by_cases h : ‖longCol (a.Q b)‖ < lam ∧ z ∈ nbhd (binOf w (a.u b))
  · have : {o | (‖longCol (a.Q b)‖ < lam ∧ z ∈ nbhd (binOf w (a.u b))) ∧ b ∈ a.lst γ o} =
        {o | b ∈ a.lst γ o} := by ext o; simp [h]
    rw [this]; exact hmeas b
  · have : {o | (‖longCol (a.Q b)‖ < lam ∧ z ∈ nbhd (binOf w (a.u b))) ∧ b ∈ a.lst γ o} = ∅ := by
      ext o; simp [h]
    rw [this]; exact MeasurableSet.empty

/-- **Short charts carry little angular-good mass.** -/
theorem shortPath_mass_le (hp : Valid p) (a : Atlas p k) (γ : Fin (p.W k))
    {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
    (κL : ℕ) (hcard : ∀ o, (a.lst γ o).card ≤ κL)
    (hmeas : ∀ b, MeasurableSet {o | b ∈ a.lst γ o})
    {u τ lam : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (hshort : 4 * κ * (2 : ℝ) ^ a.T * lam ≤ δ (p.N k) u) :
    selected p k γ (shortPath a γ u τ lam) ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
        selected p k γ Set.univ := by
  have hδu : 0 < δ (p.N k) u := by unfold δ; positivity
  have hsub : shortPath a γ u τ lam ⊆ {q | AngGood p k γ u τ q ∧
      velBin (p.N k) u q ∈ shortBins a γ lam (δ (p.N k) u) (obs (p.B k γ) (δ (p.N k) p.L) q)} := by
    intro q hq
    obtain ⟨⟨b, hb, hF, hsh⟩, hgood⟩ := hq
    refine ⟨hgood, ?_⟩
    classical
    simp only [shortBins, Finset.mem_biUnion, Finset.mem_filter]
    refine ⟨b, ⟨?_, hsh⟩, ?_⟩
    · have := hknown b q hF
      rwa [hb.1] at this
    · have hA : q.1 ∈ a.A b := hb.2.1
      have hκ : 0 ≤ κ := (norm_nonneg _).trans (hc.ends b hA).1
      have hnear := hc.velocity_near_centre b hA
      have hclose : ‖v q.1 - a.u b‖ ≤ δ (p.N k) u := by
        refine hnear.trans (le_trans ?_ hshort)
        gcongr
      exact binOf_mem_nbhd hδu hclose
  refine (measure_mono hsub).trans ?_
  have := angular_listed_le hp k γ (τ := τ) hu huη
    (shortBins a γ lam (δ (p.N k) u)) (9 * κL)
    (measurableSet_shortBins a γ lam (δ (p.N k) u) hmeas)
    (fun o => card_shortBins_le a γ lam (δ (p.N k) u) o (hcard o))
  exact this

end

end Submission.Obl.k4_raw_localized_native_systems.C
