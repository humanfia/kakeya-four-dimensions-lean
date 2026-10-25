-- Adapted from this LOT tree, o080/x0272 commit 4d767e4, Submission/Obl/k4_matching_geometric_path_cover/CodedEndpoint.lean.
import Submission.Obl.k4_matching_switching_target_certificate.Endpoint
import Submission.Obl.k4_matching_switching_target_certificate.DetControls

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- The polynomial loss in the endpoint comparison, independent of the arm lists. -/
def endpointLoss (m : ℕ) : ℝ :=
  (2 : ℝ) ^ m * ((9 : ℝ) ^ (m + 1) * (162 * ((m : ℝ) + 1) + 18) + 65)

lemma endpointLoss_pos (m : ℕ) : 0 < endpointLoss m := by
  unfold endpointLoss
  positivity

lemma ntime_eq {n₁ n₂ : ℕ} (h : ℕ → ℕ) (k : ℕ)
    (a : (Fin n₁ × Fin n₂) × ℝ) (t : ℝ) :
    ntime h k a t = (t - dcenter h k a.2) * (2 : ℝ) ^ h k := by
  simp only [ntime, lamk, div_eq_mul_inv, inv_inv]

lemma abs_ntime_le {n₁ n₂ : ℕ} {h : ℕ → ℕ} {k : ℕ}
    {a e : (Fin n₁ × Fin n₂) × ℝ}
    (hfloor : Int.floor (a.2 * (2 : ℝ) ^ h k) = Int.floor (e.2 * (2 : ℝ) ^ h k)) :
    |ntime h k a e.2| ≤ 1 / 2 := by
  have h1 := abs_sub_dcenter_of_floor_eq hfloor
  rw [ntime, abs_div, abs_of_pos (lamk_pos h k), div_le_iff₀ (lamk_pos h k)]
  simpa only [lamk, div_eq_mul_inv, mul_comm, one_mul] using h1

lemma path_endpoint_error_le {m q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q)
    {N ε γ : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hγ : 4 ≤ γ * (q : ℝ))
    (j : Fin m) :
    9 ^ (m + 1) * (8 * (2 ^ m * (3 * (((m : ℝ) + 1) * (5 * N ^ ε + 1)) + 2 * N ^ ε) *
        N ^ (-(6 / (q : ℝ)))) +
      2 ^ m * (N ^ (-(2 / (q : ℝ))) +
        (3 * (((m : ℝ) + 1) * (5 * N ^ ε + 1)) + N ^ ε) * N ^ (-γ))) +
    2 ^ m * (3 + 2 * N ^ ε) * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))) +
    3 * (2 ^ m * (3 * (5 * N ^ ε + 1) + 2 * N ^ ε) * N ^ (-(6 / (q : ℝ)))) ≤
      endpointLoss m * N ^ ε * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hNe : 1 ≤ N ^ ε := Real.one_le_rpow hN hε
  have hj : ((j : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
  have hje : (((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ) ≤ 1 / (q : ℝ) := by
    apply div_le_div_of_nonneg_right _ hq0.le
    exact (div_le_one hm0).mpr hj
  let w := N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ)))
  have hw : 0 ≤ w := (Real.rpow_pos_of_pos (by linarith : 0 < N) _).le
  have h6 : N ^ (-(6 / (q : ℝ))) ≤ w := by
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hq6 : 1 / (q : ℝ) ≤ 6 / (q : ℝ) := by gcongr <;> norm_num
    linarith
  have h2 : N ^ (-(2 / (q : ℝ))) ≤ N ^ ε * w := by
    apply le_trans (b := w)
    · apply Real.rpow_le_rpow_of_exponent_le hN
      have hq2 : 1 / (q : ℝ) ≤ 2 / (q : ℝ) := by gcongr <;> norm_num
      linarith
    · exact le_mul_of_one_le_left hw hNe
  have hg : N ^ (-γ) ≤ w := by
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hγ' : 4 / (q : ℝ) ≤ γ := (div_le_iff₀ hq0).mpr hγ
    have hq4 : 1 / (q : ℝ) ≤ 4 / (q : ℝ) := by gcongr <;> norm_num
    linarith
  have hc2 : 3 * (((m : ℝ) + 1) * (5 * N ^ ε + 1)) + 2 * N ^ ε ≤
      (18 * ((m : ℝ) + 1) + 2) * N ^ ε := by
    have hm1 : 0 ≤ (m : ℝ) + 1 := by positivity
    nlinarith
  have hc1 : 3 * (((m : ℝ) + 1) * (5 * N ^ ε + 1)) + N ^ ε ≤
      (18 * ((m : ℝ) + 1) + 1) * N ^ ε := by
    have hm1 : 0 ≤ (m : ℝ) + 1 := by positivity
    nlinarith
  have hc0 : 3 + 2 * N ^ ε ≤ 5 * N ^ ε := by linarith
  have hcs : 3 * (5 * N ^ ε + 1) + 2 * N ^ ε ≤ 20 * N ^ ε := by linarith
  calc
    _ ≤ 9 ^ (m + 1) *
        (8 * (2 ^ m * ((18 * ((m : ℝ) + 1) + 2) * N ^ ε) * w) +
          2 ^ m * (N ^ ε * w + ((18 * ((m : ℝ) + 1) + 1) * N ^ ε) * w)) +
        2 ^ m * (5 * N ^ ε) * w + 3 * (2 ^ m * (20 * N ^ ε) * w) := by
      gcongr
    _ = _ := by unfold endpointLoss w; ring

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

/-- The record/palette controls put the exact endpoint inside a tube of the
final child record, uniformly over all admissible paths. -/
lemma coded_path_endpoint (hεq : ε ≤ 1 / (q : ℝ)) (hroot : 32 ≤ N ^ (1 / (q : ℝ)))
    {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) (j : Fin m) :
    |(endpointMap m
        (fun p => codedControl J m k z q β N (dcenter h k (E 0).2) (cref f₁ h k (E 0) m)
          h F S f₁ f₂ (F k (W p)) (referencePalette m z q β N h f₁ f₂ (W p)) (!(κ p)))
        (ntime h k (E 0) (E 0).2)
        (ntime h k (E 0) (E (m + 1)).2, fun p => ntime h k (E 0) (E ((p : ℕ) + 1)).2)).2 j -
      tcen J β q k m N f₁ f₂ h (E 0) (E (m + 1)) (κ m) j
        (ntime h k (E 0) (E (m + 1)).2)| ≤
      endpointLoss m * N ^ ε * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))) := by
  let u : ℕ → ℝ := fun p =>
    codedControl J m k z q β N (dcenter h k (E 0).2) (cref f₁ h k (E 0) m)
      h F S f₁ f₂ (F k (W p)) (referencePalette m z q β N h f₁ f₂ (W p)) (!(κ p))
  have hu : ∀ p, p ≤ m → |N ^ β m * (iteratedDeriv m (arm f₁ f₂ (κ p) (W p))
      (dcenter h k (E 0).2) - cref f₁ h k (E 0) m) - u p| ≤ N ^ (-(2 / (q : ℝ))) := by
    intro p hp
    have herr := H.coded_control_error_small hεq hroot (hP.memE 0 (by omega))
      (hP.memW p hp) ((H.path_floor hP).2 p hp).symm (cref f₁ h k (E 0) m) (!(κ p))
    cases hc : κ p <;> simpa [arm, hc, u] using herr
  exact (H.path_endpoint hP u (Real.rpow_pos_of_pos H.N_pos _).le hu j).trans
    (path_endpoint_error_le H.hm H.hq H.hN H.hε.le H.hγq j)

end Det

end Submission.Obl.k4_matching_switching_target_certificate
