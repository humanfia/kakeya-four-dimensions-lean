import Submission.Obl.k4_scalar_grid_cartesian_field.SourceCore
import Submission.Obl.k4_scalar_grid_cartesian_field.ReadyPacket

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft)

/-- Add the original exterior bounds to the prepared finite Cartesian input. -/
noncomputable def sourceReady {data : Data} {k M : ℕ}
    {G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (data.W k) → Set Incidence} {B ε L H H₀ : ℝ}
    (s : SourcePacket data k M G E B ε L H) {Band : Set ℝ}
    (r : SourceRefinement s H₀ Band) {Λ β rT R : ℝ} (θ : Measure Trajectory)
    (u : SourceCoreInput s r Λ β rT θ) (hrT : (1 : ℝ) / 8 ≤ rT)
    (hjoint : ∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin 3 → ℤ) (c : ℤ),
      data.ρ k (data.γ k 1 s.i) {x | physCube (data.N k) B x = q ∧ x.1.2 1 ∈ vel data k r c} ≤
        ENNReal.ofReal (data.K k * (data.N k ^ (-B)) ^ (2 + data.d)) *
          data.π k (data.γ k 1 s.i) (vel data k r c))
    (hangular : ∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ c : ℤ,
      data.π k (data.γ k 1 s.i) (vel data k r c) ≤
        ENNReal.ofReal (data.K k * data.N k ^ (-data.S * r)))
    (hsupport : ∀ w : ℝ,
      data.N k ^ (-1 : ℝ) * packetLength data k ^ ((1 : ℝ) / 8) ≤ w →
      w ≤ data.N k ^ (-1 : ℝ) →
      (activeCodes ((data.ρ k (data.γ k 1 s.i)).restrict r.S₀) (fun x =>
        ((fun e : Fin 2 => (⌊normalizedBase (packetLength data k) (originalOrigin data k s.i) x e /
          data.N k ^ (-10 : ℝ)⌋ : ℤ)), (⌊scalarX x.1 x.2 / w⌋ : ℤ)))).Finite ∧
      ((activeCodes ((data.ρ k (data.γ k 1 s.i)).restrict r.S₀) (fun x =>
        ((fun e : Fin 2 => (⌊normalizedBase (packetLength data k) (originalOrigin data k s.i) x e /
          data.N k ^ (-10 : ℝ)⌋ : ℤ)), (⌊scalarX x.1 x.2 / w⌋ : ℤ)))).ncard : ℝ) ≤
        (32000 * L ^ 3 * H₀ ^ 2) * data.N k ^ (20 : ℝ) * (data.N k ^ (-1 : ℝ) / w) ^ data.d) :
    ReadyPacket data k M Λ B R := by
  have hNp : 0 < data.N k := by linarith [u.hN]
  have hK := s.original.budget_one
  have hh := s.original.positive_horizon
  have hH : 0 < H := by linarith [u.hH]
  have hC : 100000 * data.K k ^ 7 ≤ Λ := by
    have hle : 100000 * data.K k ^ 7 ≤ 1600000 * data.K k ^ 7 * H := by
      have hp : 0 ≤ data.K k ^ 7 := by positivity
      nlinarith [u.hH]
    exact hle.trans u.budget.relative_base
  refine {
    i := s.i, core := sourceCore s r θ u, original := s.original
    original_N := rfl, original_Λ := rfl, original_ρ := rfl, original_ν := rfl, original_π := rfl
    original_h := rfl, original_origin := ?_, original_B := rfl, original_error := rfl
    error_bound := ?_, original_prior := boundedAssignment_mass s.original le_rfl
    assignment_subset := inter_subset_left, original_budget := u.budget.original
    base_ceiling := ?_, fine_cells := r.fine_cells, fine_cover := r.fine_cover, fine_budget := ?_
    original_joint_cap := ?_, angular_cap := ?_, joint_support := ?_ }
  · funext e
    fin_cases e <;> rfl
  · change fieldError (data.N k) (packetLength data k) ≤ _
    rw [u.error_eq]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [u.hN]) (by linarith)
  · intro q
    apply (u.base_ceiling q).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC s.original.positive_horizon.le) (Real.rpow_nonneg hNp.le _)
  · exact r.fine_budget.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal u.budget.fine) le_rfl)
  · intro t ht₀ ht₁ q c
    have hμ : (data.ρ k (data.γ k 1 s.i)).restrict r.S₀ ≤ data.ρ k (data.γ k 1 s.i) := Measure.restrict_le_self
    apply ((hμ _).trans (hjoint t ht₀ ht₁ q c)).trans
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right u.budget.original (by positivity))) le_rfl
  · intro t ht₀ ht₁ c
    exact (hangular t ht₀ ht₁ c).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right u.budget.original (Real.rpow_nonneg hNp.le _)))
  · intro w hw₀ hw₁
    have hw : 0 < w := (by positivity : 0 < data.N k ^ (-1 : ℝ) * packetLength data k ^ ((1 : ℝ) / 8)).trans_le hw₀
    obtain ⟨hf, hc⟩ := hsupport w hw₀ hw₁
    exact ⟨hf, hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right u.budget.joint (Real.rpow_nonneg hNp.le _)) (by positivity))⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
