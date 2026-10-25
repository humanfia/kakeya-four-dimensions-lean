import Submission.Obl.k4_balanced_native_packet_transport.NativeCoordinates

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Set
noncomputable section

/-- Read unit block time and the centered physical tangent from a source base. -/
def normalizeScalarBase (t₀ q center : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(z 0 - t₀) / q, (z 1 - center) / q]

theorem measurable_normalizeScalarBase (t₀ q center : ℝ) :
    Measurable (normalizeScalarBase t₀ q center) := by
  unfold normalizeScalarBase
  fun_prop

theorem normalizeScalarBase_apply (t₀ q center τ y : ℝ) (hq : q ≠ 0) :
    normalizeScalarBase t₀ q center (WithLp.toLp 2 ![t₀ + q * τ, center + q * y]) =
      WithLp.toLp 2 ![τ, y] := by
  simp [normalizeScalarBase, hq]

/-- A child keeps the original terminal observation and signal reader. Its
base reader changes only by the exact affine scalar coordinate map. -/
theorem native_subblock_observation
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (offset : ℝ) (tangent : Fin 3 → ℝ) {A C : Set Traj} (hAC : A ⊆ C)
    (t₀ q center ε : ℝ) (hq : q ≠ 0)
    (O : Inc → Obs) (Y : Obs → EuclideanSpace ℝ (Fin 2)) (X : Obs → ℝ)
    (hY : Measurable Y) (hX : Measurable X)
    (μ ρ : Measure Inc)
    (hdom : Measure.map (fun p : Inc => (p.1, t₀ + q * p.2)) ρ ≪ μ)
    (hsupport : ∀ᵐ p ∂ρ, p.1 ∈ A)
    (hsource : ∀ᵐ p ∂μ,
      Y (O p) = WithLp.toLp 2
          ![p.2, scalarY (nativeCoeff P 0 1 offset tangent C p.1) p.2] ∧
      |scalarX (nativeCoeff P 0 1 offset tangent C p.1) p.2 - X (O p)| ≤ ε) :
    let b := nativeCoeff P t₀ q ((offset - center) / q) (fun j => tangent j / q) A
    Measurable (normalizeScalarBase t₀ q center ∘ Y) ∧ Measurable X ∧
      ∀ᵐ p ∂ρ,
        (normalizeScalarBase t₀ q center ∘ Y) (O (p.1, t₀ + q * p.2)) =
          WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∧
        |scalarX (b p.1) p.2 - X (O (p.1, t₀ + q * p.2))| ≤ ε := by
  dsimp only
  refine ⟨(measurable_normalizeScalarBase t₀ q center).comp hY, hX, ?_⟩
  have hexpand : Measurable (fun p : Inc => (p.1, t₀ + q * p.2)) := by fun_prop
  have hpull := ae_of_ae_map hexpand.aemeasurable (hdom.ae_le hsource)
  filter_upwards [hsupport, hpull] with p hp hobs
  constructor
  · change normalizeScalarBase t₀ q center (Y (O (p.1, t₀ + q * p.2))) = _
    rw [hobs.1]
    change normalizeScalarBase t₀ q center
      (WithLp.toLp 2 ![t₀ + q * p.2,
        scalarY (nativeCoeff P 0 1 offset tangent C p.1) (t₀ + q * p.2)]) = _
    rw [nativeCoeff_retime_tangent P t₀ q offset center hq tangent hAC hp p.2]
    exact normalizeScalarBase_apply t₀ q center p.2 _ hq
  · rw [nativeCoeff_retime_value P hP t₀ q offset ((offset - center) / q)
      tangent (fun j => tangent j / q) hAC hp p.2]
    exact hobs.2

end
end Submission.Obl.k4_balanced_native_packet_transport
