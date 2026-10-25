/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/FiniteDensityMasks.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_balanced_native_packet_transport.UWE).
-/
import Submission.Obl.k4_balanced_native_packet_transport.UWE.Problems
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity

noncomputable section

namespace Submission.Obl.k4_balanced_native_packet_transport.UWE

open MeasureTheory Set Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles

def Problem.incidenceMeasure (p : Problem) (k : ℕ) (γ : Fin (p.W k)) : Measure Incidence :=
  ((p.ν k γ).prod volume).restrict (p.E k γ)

private theorem powerSmall_finset_sum {ι : Type*} {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) (s : Finset ι) (a : ι → ℕ → ENNReal)
    (ha : ∀ i ∈ s, IsPowerSmall N (a i)) :
    IsPowerSmall N (fun k => ∑ i ∈ s, a i k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, Eventually.of_forall (fun k => by simp)⟩
  | @insert i s hi ih =>
    have h := IsPowerSmall.add hN (ha i (Finset.mem_insert_self _ _))
      (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

/-- A finite set of original-world exceptions is still power-small BEFORE
any chart assignment, conditional prior, or packet enumeration is introduced. -/
theorem Problem.finite_original_exceptions {ι : Type*} (p : Problem)
    (hN : Tendsto p.N atTop atTop) (s : Finset ι)
    (A : (k : ℕ) → Fin (p.W k) → ι → Set Incidence)
    (ha : ∀ i ∈ s, IsPowerSmall p.N (fun k =>
      ∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ (A k γ i))) :
    IsPowerSmall p.N (fun k => ∑ γ, ENNReal.ofReal (p.ω k γ) *
      p.incidenceMeasure k γ (⋃ i ∈ s, A k γ i)) := by
  have hsum := powerSmall_finset_sum hN s
    (fun i k => ∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ (A k γ i)) ha
  apply hsum.mono
  apply Eventually.of_forall
  intro k
  calc
    _ ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) * ∑ i ∈ s, p.incidenceMeasure k γ (A k γ i) := by
      apply Finset.sum_le_sum
      intro γ _
      exact mul_le_mul' le_rfl (measure_biUnion_finset_le s (fun i => A k γ i))
    _ = _ := by simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

def pureDensityBad (p : Problem) (k : ℕ) (γ : Fin (p.W k)) (r τ : ℝ) : Set Incidence :=
  {z | p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) < ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ∨
    ENNReal.ofReal (p.N k ^ (-p.f r + τ)) < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z)}

def angularDensityBad (p : Problem) (S : ℝ) (k : ℕ) (γ : Fin (p.W k)) (u τ : ℝ) : Set Incidence :=
  {z | ENNReal.ofReal (p.N k ^ (-p.f p.L - S * u + τ)) <
    p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) z, fun j => ⌊v z.1 j / δ (p.N k) u⌋)}

def densityPreparationBad (p : Problem) (S : ℝ) (R A : Finset ℝ) (τ : ℝ)
    (k : ℕ) (γ : Fin (p.W k)) : Set Incidence :=
  (⋃ r ∈ insert p.L R, pureDensityBad p k γ r τ) ∪
    ⋃ u ∈ A, angularDensityBad p S k γ u τ

/-- All finitely many density masks needed by a scalar-depth and angular-depth
grid can be removed at power-small ORIGINAL weighted cost. -/
theorem Problem.Valid.finite_density_preparation {p : Problem} {S η : ℝ} (hp : p.Valid S η)
    (R A : Finset ℝ) (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L)
    (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L) {τ : ℝ} (hτ : 0 < τ) :
    IsPowerSmall p.N (fun k => ∑ γ, ENNReal.ofReal (p.ω k γ) *
      p.incidenceMeasure k γ (densityPreparationBad p S R A τ k γ)) := by
  classical
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  have hpure := p.finite_original_exceptions hNt (insert p.L R)
    (fun k γ r => pureDensityBad p k γ r τ) (by
      intro r hr
      have hr' : 0 ≤ r ∧ r ≤ p.L := by
        rcases Finset.mem_insert.mp hr with hr | hr
        · subst r; exact ⟨hL.le, le_rfl⟩
        · exact hR r hr
      exact htyp r τ hr'.1 hr'.2 hτ)
  have hang' := p.finite_original_exceptions hNt A
    (fun k γ u => angularDensityBad p S k γ u τ) (by
      intro u hu
      exact hang u τ (hA u hu).1 (hA u hu).2 hτ)
  apply (IsPowerSmall.add hNt hpure hang').mono
  apply Eventually.of_forall
  intro k
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro γ _
  rw [← mul_add]
  exact mul_le_mul' le_rfl (measure_union_le _ _)

end Submission.Obl.k4_balanced_native_packet_transport.UWE
