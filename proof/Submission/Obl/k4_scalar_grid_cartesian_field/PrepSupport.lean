import Submission.Obl.k4_scalar_grid_cartesian_field.Interface
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketGeometry
import Submission.Obl.k4_scalar_grid_cartesian_field.RegisteredSupport

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- Extract exactly the hereditary physical support control from the frozen preparation data.
The coarse exponent one is always on its registered grid. -/
theorem prep_registered_support (data : Data)
    (H : ℕ → ℝ) (θ : (k : ℕ) → Fin (data.W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (data.W k) → Set Incidence) (hp : prepData data H θ E) :
    ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ data.N k ^ (1 / (M k : ℝ)) ≤ H k) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g : Fin (data.W k),
        RegisteredSupportControl ((data.ρ k g).restrict (E k g))
          (fun p => ![p.2, scalarY p.1 p.2]) (fun p => scalarX p.1 p.2)
          (data.N k) (H k) data.d (M k) R := by
  obtain ⟨_, M, hM, hprep⟩ := hp
  refine ⟨M, hM, fun R hR => ?_⟩
  filter_upwards [hprep R hR] with k hk
  intro g r hr hrR hreg
  have hRinv : R⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hR.le
  obtain ⟨_, _, _, _, _, _, _, hgrid, _⟩ := hk.2 g
  obtain ⟨hf, _, hhered, _, _⟩ := hgrid r (hRinv.trans hr) hrR hreg
  refine ⟨hf, ?_⟩
  have hMk : (M k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hM k).1))
  have hregone : ∃ m : ℕ, (1 : ℝ) = (m : ℝ) / M k := ⟨M k, by exact (div_self hMk).symm⟩
  exact hhered 1 hRinv hr hregone

end Submission.Obl.k4_scalar_grid_cartesian_field
