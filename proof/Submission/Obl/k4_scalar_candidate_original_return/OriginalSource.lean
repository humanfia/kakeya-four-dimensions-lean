import Submission.Obl.k4_scalar_candidate_original_return.SourceControl
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Basic

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set

noncomputable section

/-- A formatted selected event in an exact scalar sample has uniform original
source bounds, regardless of its chosen candidate family or analytical list. -/
theorem original_source_certificate {p : Code} (hp : Exact p) (k : ℕ)
    (a : Fin (W p k)) (B : ℕ) (hM : M p ≤ B) (hD : D p ≤ B)
    (C : Set Inc) (hC : MeasurableSet C) (hCsub : C ⊆ E p k a)
    (hCformat : ∀ z, Format 6 (N p k ^ B) B
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C}) :
    Nonempty (SourceCertificate (ν p k a) C (N p k ^ (2 * B)) (3 * N p k ^ B)
      (2 * N p k ^ (2 * B)) (3 * B)) := by
  have hN : 2 ≤ N p k := hp.1.1 k
  have hN1 : 1 ≤ N p k := by linarith
  have hN0 : 0 < N p k := by linarith
  have hpow : N p k ^ (M p : ℝ) ≤ N p k ^ B := by
    simpa only [Real.rpow_natCast] using pow_le_pow_right₀ hN1 hM
  have hU : 1 ≤ N p k ^ B := one_le_pow₀ hN1
  obtain ⟨n, hn, c, copy, A, hA, hν⟩ := ((hp.2.1 k).2.2.2.1 a).2.1
  have hnU : (n : ℝ) ≤ N p k ^ B := hn.trans hpow
  have hAf (j : Fin n) : Format 5 (N p k ^ B) B (A j) :=
    k4_scalar_true_atlas_terminal_lists.Format.mono (hA j).2.2.2.1 hpow hD
  obtain ⟨src⟩ := source_certificate hU hU hU c
    (fun j => ⟨(hA j).1, (hA j).2.1.trans hpow⟩) copy A hAf
    (fun j x hx i => ((hA j).2.2.2.2 x hx i).trans hpow)
    (ν p k a) hν C hC
    (fun q hq => (k4_scalar_true_atlas_terminal_lists.Exact.event_time hp k a (hCsub hq)).2)
    hCformat
  have hsquare : N p k ^ B * N p k ^ B = N p k ^ (2 * B) := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨src.enlarge ?_ le_rfl ?_ ?_⟩
  · calc
      _ ≤ N p k ^ B * N p k ^ B := mul_le_mul_of_nonneg_right hnU (by positivity)
      _ = _ := hsquare
  · calc
      _ ≤ N p k ^ B * (N p k ^ B + N p k ^ B) :=
        mul_le_mul_of_nonneg_right hnU (by positivity)
      _ = _ := by rw [mul_add, hsquare]; ring
  · omega

end

end Submission.Obl.k4_scalar_candidate_original_return
