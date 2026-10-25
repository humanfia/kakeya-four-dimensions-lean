import Submission.Obl.k4_scalar_grid_parameter_preparation.Statement
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarPacketAdapters
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarGridAdapters
import Submission.Obl.k4_scalar_grid_parameter_preparation.IncidenceFacts

/-!
# From the frozen hypotheses to the preparation interfaces

The frozen base, cap and packet hypotheses of o228, read in the forms that the preparation
kernels (x0317's regularized prior, physical support and palette floors) take.
-/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped ENNReal

theorem velBin_eq (N r : ℝ) (c : ℤ) : velBin N r c = scalarVelocityBin (N ^ (-r)) c := rfl

theorem timeBlock_eq (T : ℕ) (j : Fin (2 ^ T)) :
    timeBlock T j = Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block T j := rfl

theorem physTag_eq (N r : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) :
    physTag N r p = physicalScalarGridTag (N ^ (-r)) (scalarPacketPosition Prod.snd p) := rfl

section Adapters

variable {N K : ℕ → ℝ} {d κ S : ℝ} {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
  {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ))}
  {ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)}
  {π : (k : ℕ) → Fin (W k) → Measure ℝ}

theorem frozen_base_regularized (hbase : FrozenBase K W ω ν ρ π) :
    ∀ k g, IsProbabilityMeasure (ν k g) ∧ (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧
      ρ k g ≤ ENNReal.ofReal (K k) • (ν k g).prod volume ∧
      ρ k g {p | p.2 ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0 := by
  intro k g
  obtain ⟨-, -, hg, -⟩ := hbase k
  obtain ⟨h1, -, h3, h4, h5⟩ := hg g
  refine ⟨h1, h3, h4, ?_⟩
  have hset : {p : (ℕ × (Fin 5 → ℝ)) × ℝ | p.2 ∈ Set.Icc (0 : ℝ) 1} =
      Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp
  rw [hset]
  exact h5

theorem frozen_finite (hbase : FrozenBase K W ω ν ρ π) (k : ℕ) (g : Fin (W k)) :
    IsFiniteMeasure (ρ k g) := by
  obtain ⟨h1, -, h3, h4⟩ := frozen_base_regularized hbase k g
  exact finite_original_incidence (ν k g) (ρ k g) (K k) 0 1 h3 h4

theorem frozen_joint_caps (hcaps : FrozenCaps N K d S W ρ π) :
    ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r s b : ℝ),
      R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → ∀ i j a c : ℤ,
      ρ k g {p | (⌊p.2 / N k ^ (-r)⌋ : ℤ) = i ∧
        (⌊(p.1.2 0 + p.2 * p.1.2 1) / N k ^ (-r)⌋ : ℤ) = j ∧
        (⌊(p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4) / N k ^ (-s)⌋ : ℤ) = a ∧
        p.1.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} ≤
          ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) *
            π k g (scalarVelocityBin (N k ^ (-b)) c) := by
  intro R hR
  filter_upwards [hcaps R hR] with k hk
  intro g r s b hr1 hr2 hs1 hs2 hb1 hb2 i j a c
  refine le_trans (measure_mono ?_) ((hk g r s b hr1 hr2 hs1 hs2 hb1 hb2).2.2 ![i, j] a c)
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, h3, h4⟩
  funext e
  fin_cases e
  · simpa [baseTag] using h1
  · simpa [baseTag, trajY] using h2

theorem frozen_original_caps (hcaps : FrozenCaps N K d S W ρ π) :
    ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ScalarOriginalCapsAt N K W ρ π Prod.snd d S R k := by
  intro R hR
  filter_upwards [hcaps R hR, frozen_joint_caps hcaps R hR] with k hk hj
  intro g r s b hr1 hr2 hs1 hs2 hb1 hb2
  exact ⟨(hk g r s b hr1 hr2 hs1 hs2 hb1 hb2).1, hj g r s b hr1 hr2 hs1 hs2 hb1 hb2⟩

theorem frozen_pure_physical (hcaps : FrozenCaps N K d S W ρ π) :
    ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g r, R⁻¹ ≤ r → r ≤ R → ∀ q,
      ρ k g {p | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition Prod.snd p) = q} ≤
        ENNReal.ofReal (K k * N k ^ (-((2 + d) * r))) := by
  intro R hR
  filter_upwards [hcaps R hR] with k hk
  intro g r hr1 hr2 q
  have hexp : -((2 + d) * r) = -2 * r - d * r := by ring
  rw [hexp]
  exact pure_vector_grid_cap_physical (ρ k g) (fun p => p.2) (fun p => trajY p.1 p.2)
    (fun p => trajX p.1 p.2) (N k ^ (-r)) _
    (fun q a => (hk g r r r hr1 hr2 hr1 hr2 hr1 hr2).2.1 q a) q

theorem frozen_packet_sequence {T n : ℕ → ℝ → ℕ}
    {γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)}
    {j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)}
    {A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ))}
    {u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ}
    {F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ}
    (hN : ∀ k, 2 ≤ N k) (hK1 : ∀ k, 1 ≤ K k) (hκ1 : κ ≤ 1)
    (hpackets : FrozenPackets N K d κ W ν ρ T n γ j A u v F) :
    ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ScalarPacketSequenceAt N K W ν ρ Prod.snd d R k := by
  intro R hR
  filter_upwards [hpackets R hR] with k hk
  intro r hr1 hr2
  obtain ⟨-, hT2, hAm, hdisj, hpk, hcov⟩ := hk r hr1 hr2
  obtain ⟨D, hD1, hD2⟩ := scalar_packet_family_of_dyadic Prod.snd (K k) (N k ^ (-r))
    (N k ^ (-d * r)) (T k r) (n k r) (ν k) (ρ k) (γ k r) (j k r) (A k r) (u k r) (v k r) (F k r)
    hAm hdisj (fun i => (hpk i).1) (fun i => (hpk i).2.2.2.1) (fun i => (hpk i).2.2.2.2.1)
    (fun i => (hpk i).2.2.2.2.2.1) (fun i => (hpk i).2.2.2.2.2.2) hcov
  refine ⟨n k r, 2 ^ T k r, D, by positivity, ?_, hD1, hD2⟩
  have hrpos : 0 ≤ r := (inv_pos.mpr (by linarith : (0 : ℝ) < R)).le.trans hr1
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hpow : N k ^ (κ * r) ≤ N k ^ r :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have hK0 : 0 ≤ K k := zero_le_one.trans (hK1 k)
  push_cast
  exact hT2.trans (mul_le_mul_of_nonneg_left hpow hK0)

end Adapters

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
