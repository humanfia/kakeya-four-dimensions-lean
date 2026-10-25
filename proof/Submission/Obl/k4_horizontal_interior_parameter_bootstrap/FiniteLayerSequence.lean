import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.LayerSequence
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.PreparedRestriction
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

open MeasureTheory Filter
open scoped Topology

/-- A single fixed finite request has a witness with vanishing loss; the
hypothesis does not already assume simultaneous outputs for all list sizes. -/
theorem layer_sequence_of_fixed_request {α : Type} [MeasurableSpace α] {m : ℕ}
    {N : ℕ → ℝ} {d e₀ u : ℝ} {ρ : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} (hN : ∀ k, 1 ≤ N k) (s : Fin m → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∃ W : LayerWitness α m, W.Valid N d e₀ u ρ π b s k ε) :
    ∃ (δ : ℕ → ℝ) (W : ℕ → LayerWitness α m),
      (∀ k, 0 < δ k) ∧ Tendsto δ atTop (𝓝 0) ∧
      ((∀ k, 1 ≤ N k ^ δ k) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, N k ^ δ k ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, (W k).Valid N d e₀ u ρ π b s k (δ k) := by
  classical
  let P : ℕ → ℝ → ℕ → Prop := fun _ ε k =>
    ∃ W : LayerWitness α m, W.Valid N d e₀ u ρ π b s k ε
  obtain ⟨j, δ, -, -, hδ, -, hδlim, hevent⟩ :=
    Submission.Lib.K4ModelReduction.exists_slow_tolerance P (fun _ ε hε => h ε hε)
  let empty : LayerWitness α m :=
    ⟨0, fun _ => 0, fun _ i => i.elim0, fun _ i => i.elim0, fun _ i => i.elim0⟩
  let W : ℕ → LayerWitness α m := fun k => if H : P 0 (δ k) k then Classical.choose H else empty
  refine ⟨δ, W, hδ, hδlim,
    Submission.Obl.k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent
      N δ hN (fun k => (hδ k).le) hδlim, ?_⟩
  filter_upwards [hevent] with k hk
  have hPk : P 0 (δ k) k := hk 0 (Nat.zero_le _)
  dsimp only [W]
  rw [dif_pos hPk]
  exact Classical.choose_spec hPk

/-- A subpower dense family law is another prepared current law. Exceptional
initial samples use the original current law; the geometric law and priors stay fixed. -/
theorem prepare_layer_residual {α : Type} [MeasurableSpace α] {m : ℕ}
    {N K δ : ℕ → ℝ} {d e₀ u : ℝ} {ν : ℕ → Measure α}
    {μ ρ : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {P : ℕ → MvPolynomial (Fin 4) ℝ}
    (hN : ∀ k, 1 ≤ N k)
    (hK : (∀ k, 1 ≤ K k) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hδ : ∀ k, 0 < δ k) (hδlim : Tendsto δ atTop (𝓝 0))
    (hbasic : Hyp1 K ν μ ρ π b P)
    (s : Fin m → ℝ) (W : ℕ → LayerWitness α m)
    (hW : ∀ᶠ k in atTop, (W k).Valid N d e₀ u ρ π b s k (δ k)) :
    ∃ (H : ℕ → ℝ) (ρ' : ℕ → Measure (α × ℝ)),
      ((∀ k, 1 ≤ H k) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      (∀ k, K k ≤ H k) ∧ (∀ k, ρ' k ≤ ρ k) ∧
      Hyp1 H ν μ ρ' π b P ∧ ∀ᶠ k in atTop, ρ' k = (W k).law := by
  classical
  let H : ℕ → ℝ := fun k => max (K k) (N k ^ δ k)
  let ρ' : ℕ → Measure (α × ℝ) := fun k =>
    if (W k).Valid N d e₀ u ρ π b s k (δ k) then (W k).law else ρ k
  have hH : (∀ k, 1 ≤ H k) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hK
      (Submission.Obl.k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent
        N δ hN (fun k => (hδ k).le) hδlim)
  have hKH : ∀ k, K k ≤ H k := fun k => le_max_left _ _
  have hdom : ∀ k, ρ' k ≤ ρ k := by
    intro k
    dsimp only [ρ']
    split_ifs with hk
    · exact hk.1
    · exact le_rfl
  have hmass : ∀ k, ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k Set.univ := by
    intro k
    have hNp : 0 < N k := lt_of_lt_of_le (by norm_num) (hN k)
    dsimp only [ρ']
    split_ifs with hk
    · have hi : (H k)⁻¹ ≤ (N k ^ δ k)⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hNp _) (le_max_right _ _)
      have he : (N k ^ δ k)⁻¹ = N k ^ (-δ k) := (Real.rpow_neg hNp.le _).symm
      exact (ENNReal.ofReal_le_ofReal (hi.trans_eq he)).trans hk.2.1
    · have hi : (H k)⁻¹ ≤ (K k)⁻¹ := inv_anti₀ (by linarith [hK.1 k]) (hKH k)
      obtain ⟨-, -, -, -, -, -, hm, -⟩ := hbasic k
      exact (ENNReal.ofReal_le_ofReal hi).trans hm
  refine ⟨H, ρ', hH, hKH, hdom,
    hbasic.restrictCurrent (fun k => by linarith [hK.1 k]) hKH hdom hmass, ?_⟩
  filter_upwards [hW] with k hk
  exact if_pos hk

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
