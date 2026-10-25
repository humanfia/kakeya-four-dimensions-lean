import Submission.Obl.k4_scalar_grid_cartesian_field.PreparationAt
import Submission.Obl.k4_scalar_grid_cartesian_field.FieldFromReady

namespace Submission.Obl.k4_scalar_grid_cartesian_field

/-- The full original field conclusion is reduced to the finite Cartesian interpolation theorem. -/
theorem field_of_cartesian_core
    (hcore : ∀ M : ℕ, 2 ≤ M → CartesianCoreStatement M)
    (data : Data) (hs : scaleHyp data) : FieldTheorem data := by
  intro hb hcap hpacket H₀ θ E₀ hp hq
  obtain ⟨M, Λ, B, hM, hΛ, hB, hready⟩ := exists_ready_packets data hs hb hcap hpacket H₀ θ E₀ hp hq
  exact field_of_ready_packets data hs M (hcore M hM) Λ hΛ B hB hready

end Submission.Obl.k4_scalar_grid_cartesian_field
