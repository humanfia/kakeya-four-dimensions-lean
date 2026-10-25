import Submission.Obl.k4_scalar_grid_cartesian_field.CorePacket
import Submission.Obl.k4_scalar_grid_cartesian_field.OriginalPacketFacts
import Submission.Obl.k4_scalar_grid_cartesian_field.ActiveCodes

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory

/-- The outer properties of a qualified packet that survive interpolation and final palette pruning.
All masses and floor codes refer to the unchanged original laws and assignment. -/
structure ReadyPacket (data : Data) (k M : ℕ) (Λ B R : ℝ) where
  i : Fin (data.n k 1)
  core : CorePacket M
  original : OriginalPacketFacts data k i
  original_N : core.N = data.N k
  original_Λ : core.Λ = Λ
  original_ρ : core.ρ = data.ρ k (data.γ k 1 i)
  original_ν : core.ν = data.ν k (data.γ k 1 i)
  original_π : core.π = data.π k (data.γ k 1 i)
  original_h : core.h = packetLength data k
  original_origin : (![core.a, core.y₀] : Fin 2 → ℝ) = originalOrigin data k i
  original_B : core.B = B
  original_error : core.εT = data.N k ^ (-1 : ℝ) * packetLength data k ^ (-(3 : ℝ) / 4)
  error_bound : core.εT ≤ data.N k ^ (-(1 : ℝ) / 8)
  original_prior : core.ν core.A = data.ν k (data.γ k 1 i) (data.A k 1 i)
  assignment_subset : core.A ⊆ data.A k 1 i
  original_budget : data.K k ≤ Λ
  base_ceiling : ∀ q : Fin 2 → ℤ, core.ρ.restrict core.S₀
    {p | (fun e : Fin 2 => (⌊normalizedBase (packetLength data k) (originalOrigin data k i) p e /
      data.N k ^ (-10 : ℝ)⌋ : ℤ)) = q} ≤
      ENNReal.ofReal ((Λ * packetLength data k) * data.N k ^ (-20 : ℝ)) *
        data.ν k (data.γ k 1 i) (data.A k 1 i)
  fine_cells : Finset (Fin 3 → ℤ)
  fine_cover : ∀ᵐ p ∂core.ρ.restrict core.S₀, physCube (data.N k) B p ∈ fine_cells
  fine_budget : ENNReal.ofReal ((data.N k ^ (-B)) ^ (2 + data.d)) * fine_cells.card ≤
    ENNReal.ofReal Λ * (ENNReal.ofReal (packetLength data k) *
      data.ν k (data.γ k 1 i) (data.A k 1 i))
  original_joint_cap : ∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin 3 → ℤ) (c : ℤ),
    core.ρ.restrict core.S₀ {p | physCube (data.N k) B p = q ∧
      p.1.2 1 ∈ vel data k r c} ≤
      ENNReal.ofReal (Λ * (data.N k ^ (-B)) ^ (2 + data.d)) *
        data.π k (data.γ k 1 i) (vel data k r c)
  angular_cap : ∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ c : ℤ,
    data.π k (data.γ k 1 i) (vel data k r c) ≤ ENNReal.ofReal (Λ * data.N k ^ (-data.S * r))
  joint_support : ∀ w : ℝ,
    data.N k ^ (-1 : ℝ) * packetLength data k ^ ((1 : ℝ) / 8) ≤ w →
    w ≤ data.N k ^ (-1 : ℝ) →
    (activeCodes (core.ρ.restrict core.S₀) (fun p =>
      ((fun e : Fin 2 => (⌊normalizedBase (packetLength data k) (originalOrigin data k i) p e /
        data.N k ^ (-10 : ℝ)⌋ : ℤ)), (⌊scalarX p.1 p.2 / w⌋ : ℤ)))).Finite ∧
    ((activeCodes (core.ρ.restrict core.S₀) (fun p =>
      ((fun e : Fin 2 => (⌊normalizedBase (packetLength data k) (originalOrigin data k i) p e /
        data.N k ^ (-10 : ℝ)⌋ : ℤ)), (⌊scalarX p.1 p.2 / w⌋ : ℤ)))).ncard : ℝ) ≤
      Λ * data.N k ^ (20 : ℝ) * (data.N k ^ (-1 : ℝ) / w) ^ data.d

/-- The original core mass budget converts to the lower-floor orientation used for pruning. -/
theorem mass_floor_of_original_budget {Λ : ℝ} (hΛ : 0 < Λ) {P mass : ENNReal}
    (hbudget : P ≤ ENNReal.ofReal Λ * mass) : ENNReal.ofReal (1 / Λ) * P ≤ mass := by
  have hnonzero : ENNReal.ofReal Λ ≠ 0 := (ENNReal.ofReal_pos.mpr hΛ).ne'
  calc
    _ ≤ ENNReal.ofReal (1 / Λ) * (ENNReal.ofReal Λ * mass) := mul_le_mul' le_rfl hbudget
    _ = mass := by
      rw [one_div, ENNReal.ofReal_inv_of_pos hΛ, ← mul_assoc,
        ENNReal.inv_mul_cancel hnonzero ENNReal.ofReal_ne_top, one_mul]

end Submission.Obl.k4_scalar_grid_cartesian_field
