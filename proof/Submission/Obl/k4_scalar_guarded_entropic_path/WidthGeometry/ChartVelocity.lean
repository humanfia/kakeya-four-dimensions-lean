/-
Adapted from this LOT tree, obligation o134, session x0438, commit 2e990309978b,
Submission/Obl/k4_scalar_guarded_tangent_obstruction/ChartVelocity.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.VelocityLists
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.Accessors
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

open MeasureTheory Set

variable {p : RawData} {B k T n : ℕ} {r b h ε : ℝ} {isTrue : Bool}
  {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)}
  {A : Fin n → Set Coeff} {C : Fin n → Set Incidence}
  {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
  {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}

/-- Spatial fitting on the full original block controls the unchanged
trajectory velocity. This uses the accepted scalar packet geometry. -/
theorem ChartData.velocity_bound
    (hc : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (i : Fin n) (l : Coeff) (hl : l ∈ A i) :
    |l.2 1 - v i| ≤ 2 * p.N k ^ ε * J i * (2 : ℝ) ^ T := by
  rcases hc.2.2.2.2.2.1 i with ⟨_, _, _, _, _, _, _, _, _, _, hfit, _⟩
  have hq : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hconf : ∀ t ∈ Icc (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
      (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹),
      |Submission.Obl.k4_scalar_terminal_chart_packet_extraction.spatial l t -
        (u i + v i * t)| ≤ p.N k ^ ε * J i := by
    intro t ht
    have ht' : t ∈ I T (j i) := by
      simpa only [I, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I,
        add_div, one_div] using ht
    convert (hfit l hl t ht').1 using 1 <;>
      simp only [Submission.Obl.k4_scalar_terminal_chart_packet_extraction.spatial,
        Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y, RawData.N,
        Submission.Obl.k4_scalar_linear_critical_extremizers.Split.N, sub_sub, mul_comm]
  have hv := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.velocity_near_of_conf
    hq hconf
  have hv' := (le_div_iff₀ hq).2 hv
  simpa only [div_inv_eq_mul, mul_assoc] using hv'

/-- The terminal list remains a velocity list after restricting the
incidence law; its exceptional set is measured in the original law. -/
theorem ChartData.velocity_list_ae
    (hc : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (g : Fin (p.1 k)) (ρ : Measure Incidence) (hρ : ρ ≤ mu p k g)
    {δ : ℝ} (hδ : 0 < δ)
    (hcover : ∀ᵐ z ∂ρ, ∃ i, γ i = g ∧ z ∈ C i ∧
      2 * p.N k ^ ε * J i * (2 : ℝ) ^ T ≤ δ) :
    ∀ᵐ z ∂ρ, (⌊z.1.2 1 / δ⌋ : ℤ) ∈ velocityList (Λ g) v δ
      ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / p.N k ^ (-b)⌋ : ℤ)) := by
  have hlisted (i : Fin n) : ∀ᵐ z ∂ρ, γ i = g → z ∈ C i →
      i ∈ Λ g ((![z.2, y z.1 z.2] : Fin 2 → ℝ),
        (⌊x z.1 z.2 / p.N k ^ (-b)⌋ : ℤ)) := by
    by_cases hg : γ i = g
    · have hz := hc.2.2.2.2.2.2.2.2.1 i
      have hz' : ∀ᵐ z ∂mu p k (γ i), z ∈ C i →
          i ∈ Λ (γ i) ((![z.2, y z.1 z.2] : Fin 2 → ℝ),
            (⌊x z.1 z.2 / p.N k ^ (-b)⌋ : ℤ)) := by
        apply ae_iff.mpr
        simpa only [not_imp, mu, y, x, RawData.N,
          Submission.Obl.k4_scalar_linear_critical_extremizers.Split.N] using hz
      rw [hg] at hz'
      filter_upwards [ae_mono hρ hz'] with z hz
      exact fun _ => hz
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hg h))
  have hall : ∀ᵐ z ∂ρ, ∀ i, γ i = g → z ∈ C i →
      i ∈ Λ g ((![z.2, y z.1 z.2] : Fin 2 → ℝ),
        (⌊x z.1 z.2 / p.N k ^ (-b)⌋ : ℤ)) := ae_all_iff.mpr hlisted
  filter_upwards [hcover, hall] with z hz hlist
  obtain ⟨i, hgi, hCi, hnarrow⟩ := hz
  have hAi : z.1 ∈ A i := ((hc.2.2.2.2.1 i) hCi).2.1
  exact velocity_bin_mem_list (Λ g) v hδ _ i (hlist i hgi hCi) _
    ((ChartData.velocity_bound hc i z.1 hAi).trans hnarrow)

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
