-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/PaletteAssembly.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.SubpowerEnvelope
import Submission.Obl.k4_marked_scalar_grid_selection.MassTrimming

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open MeasureTheory Set Filter
open scoped ENNReal

/-- The event covered by a palette on a single depth. Each predictor fits the
entire assigned time block, including times outside the incidence event. -/
def paletteEvent {α : Type*} (x : α → ℝ → Fin 4 → ℝ) {n M : ℕ}
    (B : Fin n → Set α) (I : Fin n → Set ℝ)
    (L : Fin n → Fin M → Fin 4 → ℝ) (a H : ℝ) : Set (α × ℝ) :=
  {p | ∃ i u, p.1 ∈ B i ∧ p.2 ∈ I i ∧ ∀ t ∈ I i,
    |x p.1 t 3 - (L i u 0 + L i u 1 * t +
      L i u 2 * x p.1 t 1 + L i u 3 * x p.1 t 2)| ≤ H * a}

theorem paletteEvent_mono {α : Type*} (x : α → ℝ → Fin 4 → ℝ) {n M : ℕ}
    (B : Fin n → Set α) (I : Fin n → Set ℝ)
    (L : Fin n → Fin M → Fin 4 → ℝ) {a H H' : ℝ}
    (ha : 0 ≤ a) (hH : H ≤ H') :
    paletteEvent x B I L a H ⊆ paletteEvent x B I L a H' := by
  rintro p ⟨i, u, hB, hI, hfit⟩
  exact ⟨i, u, hB, hI, fun t ht =>
    (hfit t ht).trans (mul_le_mul_of_nonneg_right hH ha)⟩

/-- A finite collection of palettes retains half the original residual floor
if the sum of their failures fits that budget in the dominating incidence law. -/
theorem simultaneous_half_mass {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ ρ : Measure Ω) (hρ : ρ ≤ μ) (E : ι → Set Ω) {K : ℝ} (hK : 0 < K)
    (hfloor : ENNReal.ofReal K⁻¹ ≤ ρ univ)
    (hbad : (∑ h, μ (E h)ᶜ) ≤ ENNReal.ofReal (K⁻¹ / 2)) :
    ENNReal.ofReal (K⁻¹ / 2) ≤ ρ {p | ∀ h, p ∈ E h} := by
  have hbad' : ρ {p | ∀ h, p ∈ E h}ᶜ ≤ ENNReal.ofReal (K⁻¹ / 2) := by
    have hsub : {p | ∀ h, p ∈ E h}ᶜ ⊆ ⋃ h, (E h)ᶜ := by
      classical
      simp only [compl_ofPred, not_forall, mem_iUnion, mem_compl_iff, mem_ofPred_eq,
        subset_def]
      exact fun _ h => h
    exact (measure_mono hsub).trans
      ((hρ _).trans ((measure_iUnion_fintype_le μ _).trans hbad))
  have heq : K⁻¹ / 2 = (2 * K)⁻¹ := by ring
  rw [heq] at hbad' ⊢
  exact k4_marked_scalar_grid_selection.half_mass_floor ρ univ _ hK hfloor
    ((measure_univ_le_add_compl _).trans (add_le_add_right hbad' _))

/-- Convert fixed positive exponent palette bounds directly to the conclusion's
single subpower error and cardinality allowance. -/
theorem palette_subpower_assembly {α : Type*} [MeasurableSpace α]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (ρ : ℕ → Measure (α × ℝ)) (x : ℕ → α → ℝ → Fin 4 → ℝ)
    {m : ℕ} (n : ℕ → Fin m → ℕ)
    (B : (k : ℕ) → (h : Fin m) → Fin (n k h) → Set α)
    (I : (k : ℕ) → (h : Fin m) → Fin (n k h) → Set ℝ)
    (a : ℕ → Fin m → ℝ)
    (hfixed : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∃ (M : Fin m → ℕ)
        (L : (h : Fin m) → Fin (n k h) → Fin (M h) → Fin 4 → ℝ),
        (∀ h, (M h : ℝ) ≤ N k ^ ε) ∧
        ENNReal.ofReal ((K k)⁻¹ / 2) ≤
          ρ k {p | ∀ h, p ∈ paletteEvent (x k) (B k h) (I k h) (L h) (a k h)
            (N k ^ ε)}) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, ∃ (M : Fin m → ℕ)
        (L : (h : Fin m) → Fin (n k h) → Fin (M h) → Fin 4 → ℝ),
        (∀ h, (M h : ℝ) ≤ H k) ∧
        ENNReal.ofReal ((K k)⁻¹ / 2) ≤
          ρ k {p | ∀ h, p ∈ paletteEvent (x k) (B k h) (I k h) (L h) (a k h)
            (H k)} := by
  exact exists_subpower_envelope N hN (fun k H => ∃ (M : Fin m → ℕ)
    (L : (h : Fin m) → Fin (n k h) → Fin (M h) → Fin 4 → ℝ),
    (∀ h, (M h : ℝ) ≤ H) ∧ ENNReal.ofReal ((K k)⁻¹ / 2) ≤
      ρ k {p | ∀ h, p ∈ paletteEvent (x k) (B k h) (I k h) (L h) (a k h) H}) hfixed

/-- It suffices to prepare each of finitely many depths with an arbitrarily
small prescribed fraction of the original residual floor as its failure mass. -/
theorem finite_depth_assembly {α : Type*} [MeasurableSpace α]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hK : ∀ k, 0 < K k)
    (μ ρ : ℕ → Measure (α × ℝ)) (hρ : ∀ k, ρ k ≤ μ k)
    (hfloor : ∀ k, ENNReal.ofReal (K k)⁻¹ ≤ ρ k univ)
    (x : ℕ → α → ℝ → Fin 4 → ℝ)
    {m : ℕ} (n : ℕ → Fin m → ℕ)
    (B : (k : ℕ) → (h : Fin m) → Fin (n k h) → Set α)
    (I : (k : ℕ) → (h : Fin m) → Fin (n k h) → Set ℝ)
    (a : ℕ → Fin m → ℝ)
    (hdepth : ∀ (h : Fin m) (ε η : ℝ), 0 < ε → 0 < η → ∀ᶠ k in atTop,
      ∃ (M : ℕ) (L : Fin (n k h) → Fin M → Fin 4 → ℝ),
        (M : ℝ) ≤ N k ^ ε ∧
        μ k (paletteEvent (x k) (B k h) (I k h) L (a k h) (N k ^ ε))ᶜ ≤
          ENNReal.ofReal (η * (K k)⁻¹)) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, ∃ (M : Fin m → ℕ)
        (L : (h : Fin m) → Fin (n k h) → Fin (M h) → Fin 4 → ℝ),
        (∀ h, (M h : ℝ) ≤ H k) ∧
        ENNReal.ofReal ((K k)⁻¹ / 2) ≤
          ρ k {p | ∀ h, p ∈ paletteEvent (x k) (B k h) (I k h) (L h) (a k h)
            (H k)} := by
  apply palette_subpower_assembly N K hN ρ x n B I a
  intro ε hε
  let η : ℝ := 1 / (2 * ((m : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hall : ∀ᶠ k in atTop, ∀ h : Fin m,
      ∃ (M : ℕ) (L : Fin (n k h) → Fin M → Fin 4 → ℝ),
        (M : ℝ) ≤ N k ^ ε ∧
        μ k (paletteEvent (x k) (B k h) (I k h) L (a k h) (N k ^ ε))ᶜ ≤
          ENNReal.ofReal (η * (K k)⁻¹) :=
    Filter.eventually_all.mpr (fun h => hdepth h ε η hε hη)
  filter_upwards [hall] with k hk
  choose M L hM hbad using hk
  refine ⟨M, L, hM, simultaneous_half_mass (μ k) (ρ k) (hρ k)
    (fun h => paletteEvent (x k) (B k h) (I k h) (L h) (a k h) (N k ^ ε))
    (hK k) (hfloor k) ?_⟩
  calc
    _ ≤ ∑ _h : Fin m, ENNReal.ofReal (η * (K k)⁻¹) :=
      Finset.sum_le_sum (fun h _ => hbad h)
    _ = ENNReal.ofReal ((m : ℝ) * (η * (K k)⁻¹)) := by
      simp [ENNReal.ofReal_mul, mul_comm]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hm : (m : ℝ) * η ≤ 1 / 2 := by
        rw [show (m : ℝ) * η = (m : ℝ) / (2 * ((m : ℝ) + 1)) by dsimp [η]; ring]
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith
      calc
        (m : ℝ) * (η * (K k)⁻¹) = ((m : ℝ) * η) * (K k)⁻¹ := by ring
        _ ≤ (1 / 2) * (K k)⁻¹ :=
          mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr (hK k).le)
        _ = (K k)⁻¹ / 2 := by ring

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
