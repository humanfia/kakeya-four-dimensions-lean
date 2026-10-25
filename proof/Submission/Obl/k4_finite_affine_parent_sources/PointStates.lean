-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Lib.K4ListedExceptions.FrameCodes
import Submission.Lib.K4ContinuousKakeya.Continuous

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4ListedExceptions

noncomputable section

def stateVector {Ω : Type} (base : Ω → EuclideanSpace ℝ (Fin 3))
    (signal : Ω → ℝ) (p : Ω) : Fin 4 → ℝ :=
  ![base p 0, base p 1, base p 2, signal p]

def stateCode {Ω : Type} (base : Ω → EuclideanSpace ℝ (Fin 3))
    (signal : Ω → ℝ) (mesh : ℝ) (p : Ω) : Fin 4 → ℤ :=
  fun e => ⌊stateVector base signal p e / mesh⌋

/-- A small base group with controlled native-signal oscillation has at
most 81 exact point-state codes, independently of the absolute signal size. -/
theorem small_group_state_codes {Ω : Type}
    (base : Ω → EuclideanSpace ℝ (Fin 3)) (signal : Ω → ℝ)
    (E : Set Ω) (mesh M a d : ℝ) (hmesh : 0 < mesh) (hM : 0 ≤ M)
    (hdmesh : d ≤ mesh) (hsmall : M * (a + d) ≤ mesh)
    (hbase : ∀ p ∈ E, ∀ q ∈ E, ‖base p - base q‖ ≤ d)
    (hsignal : ∀ p ∈ E, ∀ q ∈ E,
      |signal p - signal q| ≤ M * (a + ‖base p - base q‖)) :
    ∃ V : Finset (Fin 4 → ℤ), V.card ≤ 81 ∧
      ∀ p ∈ E, stateCode base signal mesh p ∈ V := by
  classical
  by_cases hE : E.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hE
    refine ⟨integerCodeBox 1 (stateCode base signal mesh p₀), ?_, ?_⟩
    · norm_num [card_integerCodeBox]
    · intro p hp
      apply floor_code_mem_integerCodeBox 1 (stateVector base signal p)
        (stateVector base signal p₀) (fun _ => mesh) (fun _ => hmesh)
      intro e
      have hb := (hbase p hp p₀ hp₀).trans hdmesh
      have hs : |signal p - signal p₀| ≤ mesh := by
        calc
          _ ≤ M * (a + ‖base p - base p₀‖) := hsignal p hp p₀ hp₀
          _ ≤ M * (a + d) := mul_le_mul_of_nonneg_left (by linarith [hbase p hp p₀ hp₀]) hM
          _ ≤ _ := hsmall
      fin_cases e
      · simpa [stateVector] using
          (Submission.Lib.K4ContinuousKakeya.abs_apply_le_norm (base p - base p₀) 0).trans hb
      · simpa [stateVector] using
          (Submission.Lib.K4ContinuousKakeya.abs_apply_le_norm (base p - base p₀) 1).trans hb
      · simpa [stateVector] using
          (Submission.Lib.K4ContinuousKakeya.abs_apply_le_norm (base p - base p₀) 2).trans hb
      · simpa [stateVector] using hs
  · refine ⟨∅, by simp, fun p hp => ?_⟩
    exact (hE ⟨p, hp⟩).elim

/-- Finite oscillation groups give a short exact state list on every deep
label whose base diameter is sufficiently small. -/
theorem grouped_state_codes {Ω : Type} {n : ℕ}
    (base : Ω → EuclideanSpace ℝ (Fin 3)) (signal : Ω → ℝ)
    (E : Fin n → Set Ω) (D : Set Ω) (mesh M a d : ℝ)
    (hmesh : 0 < mesh) (hM : 0 ≤ M) (hdmesh : d ≤ mesh)
    (hsmall : M * (a + d) ≤ mesh)
    (hbase : ∀ p ∈ D, ∀ q ∈ D, ‖base p - base q‖ ≤ d)
    (hsignal : ∀ i p, p ∈ E i → ∀ q, q ∈ E i →
      |signal p - signal q| ≤ M * (a + ‖base p - base q‖)) :
    ∃ V : Finset (Fin 4 → ℤ), V.card ≤ 81 * n ∧
      ∀ p ∈ D, (∃ i, p ∈ E i) → stateCode base signal mesh p ∈ V := by
  classical
  have hlocal (i : Fin n) := small_group_state_codes base signal (E i ∩ D) mesh M a d
    hmesh hM hdmesh hsmall
    (fun p hp q hq => hbase p hp.2 q hq.2)
    (fun p hp q hq => hsignal i p hp.1 q hq.1)
  choose V hVcard hVmem using hlocal
  refine ⟨Finset.univ.biUnion V, ?_, ?_⟩
  · calc
      _ ≤ ∑ i : Fin n, (V i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin n, 81 := Finset.sum_le_sum fun i _ => hVcard i
      _ = 81 * n := by simp [Nat.mul_comm]
  · rintro p hp ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hVmem i p ⟨hi, hp⟩⟩

end

end Submission.Obl.k4_finite_affine_parent_sources
