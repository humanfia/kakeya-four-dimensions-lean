import Submission.Obl.k4_balanced_native_packet_transport.NativeCoordinates
import Submission.Obl.k4_balanced_native_packet_transport.WindowTransport

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Set
noncomputable section

/-- Native subblocks retain the original window certificate. The tangent is
the physical tangent with one constant center subtracted; no center velocity
is subtracted, so only `q ≤ 1` is needed for the window contraction. -/
theorem WindowCertificate.native_subblocks
    {N χ d s m : ℝ} {C C' : ℕ}
    (P : Fin C → MvPolynomial (Fin 4) ℝ) (hP : ∀ a, (P a).totalDegree ≤ 2)
    (offset : Fin C → ℝ) (tangent : Fin C → Fin 3 → ℝ)
    (A : Fin C → Set Traj) (R : Fin C → ENNReal) (μ : Fin C → Measure Inc)
    (hcert : WindowCertificate N χ d s m C R μ
      (fun a => nativeCoeff (P a) 0 1 (offset a) (tangent a) (A a)))
    (parent : Fin C' → Fin C) (A' : Fin C' → Set Traj)
    (hA' : ∀ i, MeasurableSet (A' i)) (hsub : ∀ i, A' i ⊆ A (parent i))
    (t₀ center : Fin C' → ℝ) (q : ℝ) (hq : 0 < q) (hq₁ : q ≤ 1)
    (R' : Fin C' → ENNReal) (μ' : Fin C' → Measure Inc)
    (hpositive : ∀ i, 0 < R' i)
    (hsupport : ∀ i, μ' i (A' i ×ˢ (univ : Set ℝ))ᶜ = 0)
    (hdom : ∀ B : Fin C → Set Inc, (∀ a, MeasurableSet (B a)) →
      (∑ i, R' i * μ' i ((fun p : Inc => (p.1, t₀ i + q * p.2)) ⁻¹' B (parent i))) ≤
        ∑ a, R a * μ a (B a)) :
    WindowCertificate N χ d s m C' R' μ'
      (fun i => nativeCoeff (P (parent i)) (t₀ i) q
        ((offset (parent i) - center i) / q)
        (fun j => tangent (parent i) j / q) (A' i)) := by
  apply hcert.transport parent (fun i p => (p.1, t₀ i + q * p.2))
    (fun _ => by fun_prop) R' μ' _ (fun i => A' i ×ˢ univ)
    (fun i => (hA' i).prod MeasurableSet.univ) hsupport hpositive hdom
    t₀ center (fun _ => q) (fun _ => by rwa [abs_of_pos hq])
  · intro i p hp
    refine ⟨rfl, ?_⟩
    exact nativeCoeff_retime_tangent (P (parent i)) (t₀ i) q
      (offset (parent i)) (center i) hq.ne' (tangent (parent i))
      (hsub i) hp.1 p.2
  · intro i p hp
    exact nativeCoeff_retime_value (P (parent i)) (hP (parent i)) (t₀ i) q
      (offset (parent i)) ((offset (parent i) - center i) / q)
      (tangent (parent i)) (fun j => tangent (parent i) j / q) (hsub i) hp.1 p.2

end
end Submission.Obl.k4_balanced_native_packet_transport
