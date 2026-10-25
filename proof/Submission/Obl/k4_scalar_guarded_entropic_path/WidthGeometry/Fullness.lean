/-
Adapted from this LOT tree, obligation o134, session x0438, commit 2e990309978b,
Submission/Obl/k4_scalar_guarded_tangent_obstruction/Fullness.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.ChartVelocity
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.AngularListBudget

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

open MeasureTheory Set

/-- Narrow charts can carry only the mass allowed by the original joint
angular cap and their terminal list. The current law is an unnormalized
submeasure of the original incidence law. -/
theorem ChartData.narrow_mass_le
    {p : RawData} {B k T n : ℕ} {r b h ε : ℝ} {isTrue : Bool}
    {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Coeff} {C : Fin n → Set Incidence}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hc : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (g : Fin (p.1 k)) [IsFiniteMeasure (mu p k g)]
    (ρ : Measure Incidence) (hρ : ρ ≤ mu p k g)
    {δ : ℝ} (hδ : 0 < δ) (c : ENNReal)
    (hdom : ρ.map (fun z =>
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-b)) z,
        (⌊z.1.2 1 / δ⌋ : ℤ))) ≤
      c • (((mu p k g).map
        (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-b)))).prod
          Measure.count))
    (hcover : ∀ᵐ z ∂ρ, ∃ i, γ i = g ∧ z ∈ C i ∧
      2 * p.N k ^ ε * J i * (2 : ℝ) ^ T ≤ δ) :
    ρ Set.univ ≤ (3 * c * ENNReal.ofReal (p.N k ^ ε)) * mu p k g Set.univ := by
  let observe := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-b))
  let bin : Incidence → ℤ := fun z => ⌊z.1.2 1 / δ⌋
  have hobs : Measurable observe :=
    Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL _
  have hbin : Measurable bin := by dsimp [bin]; fun_prop
  have hlist : ∀ᵐ z ∂ρ, bin z ∈ velocityList (Λ g) v δ (observe z) :=
    ChartData.velocity_list_ae hc g ρ hρ hδ hcover
  have hmeas : ∀ q, MeasurableSet {z | q ∈ velocityList (Λ g) v δ z} :=
    measurable_velocityList (Λ g) v δ (hc.2.2.2.2.2.2.2.1 g)
  have hcard (z : (Fin 2 → ℝ) × ℤ) :
      ((velocityList (Λ g) v δ z).card : ENNReal) ≤
        3 * ENNReal.ofReal (p.N k ^ ε) := by
    calc
      _ ≤ ((3 * (Λ g z).card : ℕ) : ENNReal) := by
        exact_mod_cast card_velocityList_le (Λ g) v δ z
      _ = 3 * ENNReal.ofReal ((Λ g z).card : ℝ) := by simp
      _ ≤ 3 * ENNReal.ofReal (p.N k ^ ε) := by
        gcongr
        exact hc.2.2.2.2.2.2.1 g z
  have hbound := original_mass_le_list_budget (mu p k g) ρ observe bin hobs hbin
    (velocityList (Λ g) v δ) hmeas c (3 * ENNReal.ofReal (p.N k ^ ε)) hcard hdom hlist
  calc
    ρ Set.univ ≤ (c * (3 * ENNReal.ofReal (p.N k ^ ε))) * mu p k g Set.univ := hbound
    _ = _ := by ring

/-- The fullness estimate directly from the original Radon--Nikodym
densities, after an arbitrary further incidence restriction. -/
theorem ChartData.narrow_mass_le_density
    {p : RawData} {B k T n : ℕ} {r b h ε : ℝ} {isTrue : Bool}
    {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Coeff} {C : Fin n → Set Incidence}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hc : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (g : Fin (p.1 k)) [IsFiniteMeasure (mu p k g)]
    (ρ : Measure Incidence) {δ : ℝ} (hδ : 0 < δ)
    (ref : Measure ((Fin 2 → ℝ) × ℤ))
    (f : ((Fin 2 → ℝ) × ℤ) → ENNReal)
    (F : (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal) (hf : Measurable f)
    (hpure : (mu p k g).map
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-b))) =
        ref.withDensity f)
    (hjoint : (mu p k g).map (fun z =>
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-b)) z,
        (⌊z.1.2 1 / δ⌋ : ℤ))) = (ref.prod Measure.count).withDensity F)
    (G : Set (((Fin 2 → ℝ) × ℤ) × ℤ)) (hG : MeasurableSet G) (c : ENNReal)
    (hcap : ∀ z ∈ G, F z ≤ c * f z.1)
    (hρ : ρ ≤ (mu p k g).restrict ((fun z =>
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-b)) z,
        (⌊z.1.2 1 / δ⌋ : ℤ))) ⁻¹' G))
    (hcover : ∀ᵐ z ∂ρ, ∃ i, γ i = g ∧ z ∈ C i ∧
      2 * p.N k ^ ε * J i * (2 : ℝ) ^ T ≤ δ) :
    ρ Set.univ ≤ (3 * c * ENNReal.ofReal (p.N k ^ ε)) * mu p k g Set.univ := by
  let observe := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-b))
  let bin : Incidence → ℤ := fun z => ⌊z.1.2 1 / δ⌋
  have hobs : Measurable observe :=
    Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL _
  have hbin : Measurable bin := by dsimp [bin]; fun_prop
  apply ChartData.narrow_mass_le hc g ρ (hρ.trans Measure.restrict_le_self) hδ c ?_ hcover
  exact (Measure.map_mono hρ (hobs.prodMk hbin)).trans
    (restricted_joint_map_le (mu p k g) ref observe bin hobs hbin f F hf
      hpure hjoint G hG c hcap)

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
