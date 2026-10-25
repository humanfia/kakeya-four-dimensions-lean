/- Adapted from: here:o222, session x0774, commit 3c748bb8.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactSheetSelection.lean. -/
import Submission.Lib.K4ContactNormalization.HomogeneousCorrection
import Submission.Obl.k4_general_parent_projected_layers.Signal
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

/-! Choose one full-time affine predictor using the current incidence law. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MeasureTheory Set MvPolynomial Filter
open Submission.Lib.K4ContactNormalization (point affineBase)

noncomputable section

def affineSheetLines {α : Type*} (b : α → Fin 6 → ℝ) (I : Set ℝ) (L : Fin 4 → ℝ)
    (E : ℝ) : Set α :=
  {l | ∀ t ∈ I,
    |eval (point (b l) t) (affineBase L) - point (b l) t 3| ≤ E}

theorem measurableSet_affineSheetLines {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (I : Set ℝ) (L : Fin 4 → ℝ) (E : ℝ) :
    MeasurableSet (affineSheetLines b I L E) := by
  have hclosed : IsClosed {v : Fin 6 → ℝ | ∀ t ∈ I,
      |Submission.Obl.k4_general_parent_projected_layers.signal
        (affineBase L - X (3 : Fin 4)) v t| ≤ E} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_le
      (Submission.Obl.k4_general_parent_projected_layers.continuous_signal
        (affineBase L - X (3 : Fin 4)) t).abs continuous_const
  simpa only [affineSheetLines,
    Submission.Obl.k4_general_parent_projected_layers.signal,
    Submission.Obl.k4_general_parent_projected_layers.point, point,
    eval_sub, eval_X, Set.preimage_ofPred_eq] using hclosed.measurableSet.preimage hb

/-- Select one of three full-time sheets on a dense current-law event. The
selected event retains its original incidence points and loses at most a
factor three in mass. -/
theorem select_full_time_affine_sheet {α : Type*} [MeasurableSpace α]
    (ρ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (G : Set (α × ℝ)) (hG : MeasurableSet G) (I : Set ℝ) (L : Fin 3 → Fin 4 → ℝ)
    {E m : ℝ} (hmass : ENNReal.ofReal m ≤ ρ G)
    (hcover : ∀ᵐ z ∂ρ, z ∈ G → ∃ i : Fin 3, z.1 ∈ affineSheetLines b I (L i) E) :
    ∃ (i : Fin 3) (G' : Set (α × ℝ)), MeasurableSet G' ∧ G' ⊆ G ∧
      ENNReal.ofReal (m / 3) ≤ ρ G' ∧
      ∀ z ∈ G', z.1 ∈ affineSheetLines b I (L i) E := by
  classical
  let F : Fin 3 → Set (α × ℝ) := fun i =>
    G ∩ Prod.fst ⁻¹' affineSheetLines b I (L i) E
  have hsub : G ≤ᵐ[ρ] ⋃ i, F i := by
    filter_upwards [hcover] with z hz hzG
    obtain ⟨i, hi⟩ := hz hzG
    exact mem_iUnion.mpr ⟨i, hzG, hi⟩
  have hsum : ENNReal.ofReal m ≤ ∑ i : Fin 3, ρ (F i) :=
    hmass.trans ((measure_mono_ae hsub).trans (measure_iUnion_fintype_le ρ F))
  obtain ⟨i, -, hi⟩ :=
    Submission.Obl.k4_quadratic_atlas_normalization.exists_mass_ge_average
      Finset.univ (fun i : Fin 3 => ρ (F i)) m Finset.univ_nonempty hsum
  refine ⟨i, F i, ?_, inter_subset_left, ?_, fun z hz => hz.2⟩
  · exact hG.inter ((measurableSet_affineSheetLines hb I (L i) E).preimage measurable_fst)
  · simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using hi

/-- Three-sheet selection preserves a single subpower budget for both the
original row-event mass and the affine fitting error on its original block. -/
theorem select_subpower_affine_sheets {α : Type*} [MeasurableSpace α]
    (N M H a m : ℕ → ℝ) (hN : ∀ k, 0 < N k) (hNt : Tendsto N atTop atTop)
    (hM : ∀ k, 1 ≤ M k) (hH : ∀ k, 1 ≤ H k)
    (hMsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ N k ^ ε)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    (ha : ∀ k, 0 ≤ a k) (hm : ∀ k, 0 ≤ m k)
    (ρ : ℕ → Measure (α × ℝ)) (b : ℕ → α → Fin 6 → ℝ)
    (hb : ∀ k, Measurable (b k)) (G : ℕ → Set (α × ℝ))
    (hG : ∀ k, MeasurableSet (G k)) (I : ℕ → Set ℝ)
    (hcover : ∀ᶠ k in atTop, ENNReal.ofReal (m k / M k) ≤ ρ k (G k) ∧
      ∃ L : Fin 3 → Fin 4 → ℝ, ∀ᵐ z ∂ρ k, z ∈ G k →
        ∃ i : Fin 3, z.1 ∈ affineSheetLines (b k) (I k) (L i) (H k * a k)) :
    ∃ M' : ℕ → ℝ, (∀ k, 1 ≤ M' k) ∧ (∀ k, M k ≤ M' k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M' k ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, ∃ (L : Fin 4 → ℝ) (G' : Set (α × ℝ)),
        MeasurableSet G' ∧ G' ⊆ G k ∧ ENNReal.ofReal (m k / M' k) ≤ ρ k G' ∧
          ∀ z ∈ G', z.1 ∈ affineSheetLines (b k) (I k) L (M' k * a k) := by
  let M' : ℕ → ℝ := fun k => 3 * M k * H k
  have hM0 : ∀ k, 0 ≤ M k := fun k => zero_le_one.trans (hM k)
  have hH0 : ∀ k, 0 ≤ H k := fun k => zero_le_one.trans (hH k)
  have h31 : ∀ k, 1 ≤ 3 * M k := fun k => by linarith [hM k]
  have h3M0 : ∀ k, 0 ≤ 3 * M k := fun k => zero_le_one.trans (h31 k)
  have hM'1 : ∀ k, 1 ≤ M' k := fun k => by
    have h := mul_le_mul_of_nonneg_left (hH k) (h3M0 k)
    exact (h31 k).trans (by simpa only [mul_one] using h)
  have hMM' : ∀ k, M k ≤ M' k := fun k => by
    dsimp [M']
    have h := mul_le_mul_of_nonneg_left (hH k) (h3M0 k)
    nlinarith [hM k]
  have hHM' : ∀ k, H k ≤ M' k := fun k => by
    dsimp [M']
    have h := mul_le_mul_of_nonneg_right (h31 k) (hH0 k)
    simpa only [one_mul] using h
  have h3Msub := Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hN
    (fun _ => by norm_num : ∀ k : ℕ, (0 : ℝ) ≤ 3) hM0
    (Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hNt 3) hMsub
  have hM'sub := Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hN
    h3M0 hH0 h3Msub hHsub
  refine ⟨M', hM'1, hMM', hM'sub, ?_⟩
  filter_upwards [hcover] with k hk
  obtain ⟨L, hL⟩ := hk.2
  obtain ⟨i, G', hG'm, hG'sub, hG'mass, hG'fit⟩ := select_full_time_affine_sheet
    (ρ k) (b k) (hb k) (G k) (hG k) (I k) L hk.1 hL
  refine ⟨L i, G', hG'm, hG'sub, ?_, ?_⟩
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hG'mass
    have hMpos : 0 < M k := zero_lt_one.trans_le (hM k)
    have hden : 3 * M k ≤ M' k := by
      dsimp [M']
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hH k) (h3M0 k)
    have h := div_le_div_of_nonneg_left (hm k) (by positivity : 0 < 3 * M k) hden
    simpa only [div_div, mul_comm (M k) (3 : ℝ)] using h
  · intro z hz t ht
    exact (hG'fit z hz t ht).trans
      (mul_le_mul_of_nonneg_right (hHM' k) (ha k))

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
