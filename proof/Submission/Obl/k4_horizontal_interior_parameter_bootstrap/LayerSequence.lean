import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.Interface
import Submission.Lib.K4ModelReduction.Diagonal
import Submission.Obl.k4_scalar_mesh_block_reduction.Uniformity

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

open MeasureTheory Filter
open scoped Topology

/-- A simultaneous finite list of full-time layers, including its common current law. -/
structure LayerWitness (α : Type) [MeasurableSpace α] (m : ℕ) where
  law : Measure (α × ℝ)
  n : Fin m → ℕ
  A : (r : Fin m) → Fin (n r) → Set α
  q : (r : Fin m) → Fin (n r) → Fin 3 → ℤ
  h : (r : Fin m) → Fin (n r) → Fin 6 → ℝ

def LayerWitness.Valid {α : Type} [MeasurableSpace α] {m : ℕ}
    (W : LayerWitness α m) (N : ℕ → ℝ) (d e₀ u : ℝ)
    (ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ)
    (s : Fin m → ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  W.law ≤ ρ k ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ W.law Set.univ ∧
    ∀ r, LayerAt N d e₀ π b k ε W.law (N k ^ (-u * s r)) (N k ^ (-s r))
      (W.n r) (W.A r) (W.q r) (W.h r)

/-- A fixed finite layer request can be chosen with one vanishing loss exponent.
This is the form in which a dense output is an admissible input to the next preparation. -/
theorem layer_sequence_of_layers {α : Type} [MeasurableSpace α]
    {N : ℕ → ℝ} {d e₀ u sMax : ℝ} {ρ : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hL : LayersAt N d e₀ u sMax ρ π b) (m : ℕ) (s : Fin m → ℝ)
    (hs : ∀ r, 0 < s r ∧ s r < sMax) :
    ∃ (ε : ℕ → ℝ) (W : ℕ → LayerWitness α m),
      (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
      ((∀ k, 1 ≤ N k ^ ε k) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, N k ^ ε k ≤ N k ^ η) ∧
      ∀ᶠ k in atTop, (W k).Valid N d e₀ u ρ π b s k (ε k) := by
  classical
  let P : ℕ → ℝ → ℕ → Prop := fun _ ε k =>
    ∃ W : LayerWitness α m, W.Valid N d e₀ u ρ π b s k ε
  have hP : ∀ j ε, 0 < ε → ∀ᶠ k in atTop, P j ε k := by
    intro j ε hε
    filter_upwards [hL m s hs ε hε] with k hk
    obtain ⟨law, hlaw, hmass, n, A, q, h, hvalid⟩ := hk
    exact ⟨⟨law, n, A, q, h⟩, hlaw, hmass, hvalid⟩
  obtain ⟨j, ε, -, -, hε, -, hεlim, hevent⟩ :=
    Submission.Lib.K4ModelReduction.exists_slow_tolerance P hP
  let empty : LayerWitness α m :=
    ⟨0, fun _ => 0, fun _ i => i.elim0, fun _ i => i.elim0, fun _ i => i.elim0⟩
  let W : ℕ → LayerWitness α m := fun k => if H : P 0 (ε k) k then Classical.choose H else empty
  refine ⟨ε, W, hε, hεlim,
    Submission.Obl.k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent
      N ε hN (fun k => (hε k).le) hεlim, ?_⟩
  filter_upwards [hevent] with k hk
  have hPk : P 0 (ε k) k := hk 0 (Nat.zero_le _)
  dsimp only [W]
  rw [dif_pos hPk]
  exact Classical.choose_spec hPk

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
