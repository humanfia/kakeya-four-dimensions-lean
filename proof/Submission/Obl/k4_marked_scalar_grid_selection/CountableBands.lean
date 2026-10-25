import Submission.Obl.k4_marked_scalar_grid_selection.VaryingSelection
import Submission.Obl.k4_tempered_grid_selection.SelectionMass
import Submission.Obl.k4_tempered_grid_selection.Exponents

namespace Submission.Obl.k4_marked_scalar_grid_selection

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- A record band gives a power window after absorbing its subpower factor. -/
theorem power_window_of_record_band
    {Λ Ω Y : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (obs : Ω → Y) (D : Y → ℝ≥0∞)
    (T : Set Λ) (W : Λ → ℝ) (n a δ τ P : ℝ)
    (hn : 1 < n) (hτ : 0 < τ) (hδ : δ ≤ τ / 4)
    (hP : P ≤ n ^ (τ / 4))
    (hfit : ∀ z ∈ T, 0 < W z ∧
      |k4_tempered_grid_selection.logarithmicExponent n (W z) - a| ≤ δ)
    (hband : ∀ l u ε : ℝ, 0 < l → 0 < u → 0 < ε →
      (∀ z ∈ T, l ≤ W z ∧ W z ≤ u) →
      ν {p | D (obs p) < ENNReal.ofReal (ε * l) ∨
        ENNReal.ofReal (P * u) < D (obs p)} ≤ ENNReal.ofReal (ε * P)) :
    ν {p | D (obs p) < ENNReal.ofReal (n ^ (-a - τ)) ∨
      ENNReal.ofReal (n ^ (-a + τ)) < D (obs p)} ≤
      ENNReal.ofReal (n ^ (-(τ / 4))) := by
  have hn0 : 0 < n := by linarith
  have hwindow := hband (n ^ (-a - δ)) (n ^ (-a + δ)) (n ^ (-(τ / 2)))
    (Real.rpow_pos_of_pos hn0 _) (Real.rpow_pos_of_pos hn0 _)
    (Real.rpow_pos_of_pos hn0 _) (fun z hz =>
      k4_tempered_grid_selection.power_band_of_exponent_fit hn
        (hfit z hz).1 (hfit z hz).2)
  apply (measure_mono (show
      {p | D (obs p) < ENNReal.ofReal (n ^ (-a - τ)) ∨
        ENNReal.ofReal (n ^ (-a + τ)) < D (obs p)} ⊆
      {p | D (obs p) < ENNReal.ofReal (n ^ (-(τ / 2)) * n ^ (-a - δ)) ∨
        ENNReal.ofReal (P * n ^ (-a + δ)) < D (obs p)} from ?_)).trans
    (hwindow.trans ?_)
  · intro p hp
    rcases hp with hp | hp
    · left
      apply hp.trans_le
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.rpow_add hn0]
      exact Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)
    · right
      apply lt_of_le_of_lt _ hp
      apply ENNReal.ofReal_le_ofReal
      calc
        P * n ^ (-a + δ) ≤ n ^ (τ / 4) * n ^ (-a + δ) :=
          mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hn0.le _)
        _ = n ^ (τ / 4 + (-a + δ)) := (Real.rpow_add hn0 _ _).symm
        _ ≤ n ^ (-a + τ) := Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)
  · apply ENNReal.ofReal_le_ofReal
    calc
      n ^ (-(τ / 2)) * P ≤ n ^ (-(τ / 2)) * n ^ (τ / 4) :=
        mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hn0.le _)
      _ = n ^ (-(τ / 4)) := by rw [← Real.rpow_add hn0]; congr 1; ring

/-- Countably many record weights can be selected together without dividing
atoms. Several observations may use the same column, which supplies the
compatibility between pure observations and zero-depth joint observations. -/
theorem countable_record_selection
    {Λ : ℕ → Type*} {Ω I J : Type*}
    [∀ k, MeasurableSpace (Λ k)] [∀ k, MeasurableSingletonClass (Λ k)]
    [∀ k, Countable (Λ k)] [MeasurableSpace Ω] [Countable I] [Nonempty I]
    (Y : J → Type*) (col : J → I)
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : k4_tempered_grid_selection.Subpower N K)
    (μ : (k : ℕ) → Measure (Λ k)) (S : (k : ℕ) → Set (Λ k))
    (hlower : ∀ k, ENNReal.ofReal (K k)⁻¹ ≤ μ k (S k))
    (ν : (k : ℕ) → Set (Λ k) → Measure Ω)
    (obs : (j : J) → ℕ → Ω → Y j)
    (D : (j : J) → (k : ℕ) → Set (Λ k) → Y j → ℝ≥0∞)
    (W : (k : ℕ) → I → Λ k → ℝ) (C : ℕ)
    (hW : ∀ i, ∀ᶠ k in atTop, ∀ z ∈ S k,
      N k ^ (-(C : ℝ)) ≤ W k i z ∧ W k i z ≤ N k ^ (C : ℝ))
    (P : J → ℕ → ℝ)
    (hP : ∀ j, k4_tempered_grid_selection.Subpower N (P j))
    (hband : ∀ j, ∀ᶠ k in atTop, ∀ T : Set (Λ k), T ⊆ S k →
      ∀ l u ε : ℝ, 0 < l → 0 < u → 0 < ε →
      (∀ z ∈ T, l ≤ W k (col j) z ∧ W k (col j) z ≤ u) →
      ν k T {p | D j k T (obs j k p) < ENNReal.ofReal (ε * l) ∨
        ENNReal.ofReal (P j k * u) < D j k T (obs j k p)} ≤
        ENNReal.ofReal (ε * P j k)) :
    ∃ (L : ℕ → ℝ) (T : (k : ℕ) → Set (Λ k)) (a : ℕ → I → ℝ),
      k4_tempered_grid_selection.Subpower N L ∧ (∀ k, K k ≤ L k) ∧
      (∀ k, T k ⊆ S k) ∧
      (∀ k, ENNReal.ofReal (L k)⁻¹ ≤ μ k (T k)) ∧
      (∀ k i, |a k i| ≤ (C : ℝ)) ∧
      ∀ (j : J) (τ : ℝ), 0 < τ → ∃ c : ℝ, 0 < c ∧
        ∀ᶠ k in atTop,
          ν k (T k) {p | D j k (T k) (obs j k p) <
            ENNReal.ofReal (N k ^ (-a k (col j) - τ)) ∨
            ENNReal.ofReal (N k ^ (-a k (col j) + τ)) <
              D j k (T k) (obs j k p)} ≤ ENNReal.ofReal (N k ^ (-c)) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat I
  choose index hindex using he
  let f (k j : ℕ) (z : Λ k) : ℝ :=
    k4_tempered_grid_selection.boundedExponent (C : ℝ) (N k) (W k (e j) z)
  obtain ⟨B, T', a', δ, hB, hBsub, ha', hδpos, hδ, hfit, hretain⟩ :=
    countable_type_selection_varying N hN hNt
      (fun k => (μ k).restrict (S k)) f (C : ℝ)
      (Nat.cast_nonneg C) (fun k j z =>
        k4_tempered_grid_selection.abs_boundedExponent _ _ _ (Nat.cast_nonneg C))
  let T (k : ℕ) : Set (Λ k) := S k ∩ T' k
  let L (k : ℕ) : ℝ := K k * (B k : ℝ)
  let a (k : ℕ) (i : I) : ℝ := a' k (index i)
  refine ⟨L, T, a,
    k4_tempered_grid_selection.subpower_mul (fun k => by linarith [hN k]) hK hBsub,
    ?_, (fun k => inter_subset_left), ?_, (fun k i => ha' k (index i)), ?_⟩
  · intro k
    have hb : (1 : ℝ) ≤ B k := by exact_mod_cast Nat.succ_le_iff.mpr (hB k)
    dsimp [L]
    nlinarith [hK.1 k]
  · intro k
    apply k4_tempered_grid_selection.inverse_mass_after_finite_loss
      (by linarith [hK.1 k]) (hB k) (hlower k)
    have hr := hretain k
    change (μ k).restrict (S k) univ ≤
      (B k : ℝ≥0∞) * (μ k).restrict (S k) (T' k) at hr
    rw [Measure.restrict_apply_univ,
      Measure.restrict_apply (Set.to_countable (T' k)).measurableSet] at hr
    simpa only [inter_comm, T] using hr
  · intro j τ hτ
    refine ⟨τ / 4, by linarith, ?_⟩
    have hδτ : ∀ᶠ k in atTop, δ k < τ / 4 :=
      hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < τ / 4))
    filter_upwards [hfit (index (col j)), hW (col j), hδτ,
      (hP j).2 (τ / 4) (by linarith), hband j]
      with k hkfit hkW hkδ hkP hkband
    apply power_window_of_record_band (ν k (T k)) (obs j k) (D j k (T k))
      (T k) (W k (col j)) (N k) (a k (col j)) (δ k) τ (P j k)
      (by linarith [hN k]) hτ hkδ.le hkP
    · intro z hz
      have hWz := hkW z hz.1
      have hpos : 0 < W k (col j) z :=
        (Real.rpow_pos_of_pos (by linarith [hN k]) _).trans_le hWz.1
      refine ⟨hpos, ?_⟩
      have hfz := hkfit z hz.2
      change |k4_tempered_grid_selection.boundedExponent
        (C : ℝ) (N k) (W k (e (index (col j))) z) - a' k (index (col j))| < δ k at hfz
      rw [hindex, k4_tempered_grid_selection.boundedExponent_eq
        (by linarith [hN k]) hWz.1 hWz.2] at hfz
      exact hfz.le
    · exact hkband (T k) inter_subset_left

end Submission.Obl.k4_marked_scalar_grid_selection
