/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/Losses.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Interface
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_tempered_grid_selection.SelectionMass

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open Filter

/-- One fixed polynomial in the incoming coefficient loss absorbs all record
support volumes and overlap counts. -/
abbrev geometryLoss (K : ℝ) : ℝ := 1000000 * K ^ 3

theorem geometryLoss_subpower {N K : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : Subpower N K) :
    Subpower N (fun k => geometryLoss (K k)) := by
  constructor
  · intro k
    have hpow : 1 ≤ K k ^ 3 := one_le_pow₀ (hK.1 k)
    dsimp [geometryLoss]
    linarith
  · intro ε hε
    have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      (N := N) (K := K) (fun k => by linarith [hN k]) hNt hK.1 hK.2 3
      (a := 0) (b := ε) hε (A := 1000000) (by norm_num)
    simpa only [Real.rpow_zero, mul_one, geometryLoss] using h.mono (fun _ h => h.le)

/-- Fixed positive constants are subpower in any diverging base. -/
theorem subpower_constant {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {C : ℝ} (hC : 1 ≤ C) : Subpower N (fun _ => C) := by
  refine ⟨fun _ => hC, ?_⟩
  intro ε hε
  exact ((tendsto_rpow_atTop hε).comp hN).eventually (eventually_ge_atTop C)

/-- Enlarging a loss by the finite type-selection factor and the discarded-mass
factor two preserves subpower growth. -/
theorem subpower_selection_loss {N K : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : Subpower N K)
    (B : ℕ → ℕ) (hB : Subpower N (fun k => (B k : ℝ))) :
    Subpower N (fun k => K k * ((2 * B k : ℕ) : ℝ)) := by
  have htwo := subpower_constant hNt (show (1 : ℝ) ≤ 2 by norm_num)
  have hprod := Submission.Obl.k4_tempered_grid_selection.subpower_mul
    (fun k => by linarith [hN k]) htwo hB
  simpa only [Subpower, Submission.Obl.k4_tempered_grid_selection.Subpower,
    Nat.cast_mul, Nat.cast_ofNat] using
      Submission.Obl.k4_tempered_grid_selection.subpower_mul
        (fun k => by linarith [hN k]) hK hprod

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
