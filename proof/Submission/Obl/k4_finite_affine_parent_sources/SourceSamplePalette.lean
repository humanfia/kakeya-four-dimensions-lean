import Submission.Obl.k4_finite_affine_parent_sources.SourceParentPalette
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionSample
import Submission.Obl.k4_finite_affine_parent_sources.SamplePaletteNumerics

/-!
The palette at an actual selection sample. The reference restriction is
chosen before the likelihood deletion, and every later numerator is read
against that unchanged original law. The sample budget pays the parent
packet floor and bounds the palette coefficient by its sixth power.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Lib.K4AngularCharge

noncomputable section

section Problem

variable {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Trajectory}
    {E : (k : ℕ) → Fin (W k) → Set Incidence}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → Observation × (Fin 2 → ℤ) → ENNReal}
    (hprob : prob N K L d S η W ω ν E P B f g G)

include hprob

/-- The original prior and its incidence restriction have the same
unconditioned velocity radius from the problem's native jet bound. -/
theorem prob_original_velocity_bound (k : ℕ) (w : Fin (W k)) :
    (∀ᵐ l ∂ν k w, ∀ e : Fin 2, |v l e| ≤ K k) ∧
      (∀ᵐ z ∂(((ν k w).prod volume).restrict (E k w)),
        ∀ e : Fin 2, |worldVel (w, z) e| ≤ K k) := by
  obtain ⟨_, _, _, _, _, _, _, _, ⟨M, D, hdata⟩, _⟩ := hprob
  obtain ⟨hν, _, _, _, _, _, _, _, _, _, _, hjet, _⟩ := (hdata k).2.2.2.1 w
  letI : IsProbabilityMeasure (ν k w) := hν
  have hvel : ∀ᵐ l ∂ν k w, ∀ e : Fin 2, |v l e| ≤ K k := by
    filter_upwards [hjet] with l hl e
    have hnorm : ‖v l‖ ≤ K k := by
      have ht := (hl 0 (by constructor <;> norm_num)).1
      linarith [norm_nonneg (y l 0)]
    have hcoord : |v l e| ≤ ‖v l‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v l) e
    exact hcoord.trans hnorm
  refine ⟨hvel, ?_⟩
  have hprod : ∀ᵐ (z : Incidence) ∂((ν k w).prod (volume : Measure ℝ)),
      ∀ e : Fin 2, |v z.1 e| ≤ K k :=
    (Measure.quasiMeasurePreserving_fst (μ := ν k w) (ν := (volume : Measure ℝ))).ae hvel
  exact ae_restrict_of_ae hprod

variable {k m Mp Dp : ℕ} {p : PathData (W k)} {ℓ κ₁ δ₀ σ : ℝ}
    {sg : ℕ → ℝ}
    (hp : p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The actual masked original parent supplies its fixed probability
palette, with coefficient at most the sixth power of the sample budget.
The only retained-set floor is measured against the full original packet. -/
theorem sample_parent_palette
    [∀ w : Fin (W k), IsFiniteMeasure (((ν k w).prod volume).restrict (E k w))]
    (n : ℕ) (unit ρ β ma τd τa : ℝ)
    (hm : 0 < m) (hu : 0 < unit) (hNt : 8 ≤ N k ^ (unit * L))
    (hℓ : 0 ≤ ℓ) (hS1 : S ≤ 1) (hβ : β ≤ 1) (hma0 : 0 ≤ ma)
    (hunit : unit * ((n : ℝ) + 2) ≤ ℓ / 8) (hδ : 2 * δ₀ ≤ unit)
    (hτd : τd ≤ selectionBudget n ρ unit L)
    (hτa : τa ≤ selectionBudget n ρ unit L)
    (hma : ma ≤ selectionBudget n ρ unit L)
    (hbig : (10 : ℝ) ^ 40 * p.κ ^ 20 * K k ^ 4 * ((m : ℝ) + 2) ^ 4 ≤
      N k ^ selectionBudget n ρ unit L)
    (b₀ : Fin p.C) (hband : 1 / 8 ≤ sg (p.lev b₀))
    (hfull : (((2 : ℝ) ^ p.T (p.lev b₀))⁻¹) / N k ^ (unit * L * β) ≤
      Submission.Obl.k4_compatible_pair_frame_preparation.Construction.r₁ (p.frame b₀))
    (Qa Qd : Finset ℝ) (hQa : ∀ r ∈ Qa, 0 < r ∧ r ≤ η * L)
    (hmenu : ∀ t : ℝ, unit * L / n ≤ t → t ≤ unit * L * n →
      ∃ r ∈ Qa, t - ma ≤ r ∧ r ≤ t)
    (R S1 : Set Incidence) (hRm : MeasurableSet R) (hRF : R ⊆ p.counted b₀)
    (hS1R : S1 ⊆ R) (hS1pos : 0 < ((ν k (p.world b₀)).prod volume) S1)
    (hpacket : ENNReal.ofReal (1 / (64 * (m : ℝ) * p.κ ^ 2)) *
        ((ν k (p.world b₀)).prod volume) (p.packet b₀) ≤
      ((ν k (p.world b₀)).prod volume) S1)
    (hshare : ∀ z ∈ R,
      ENNReal.ofReal ((N k ^ selectionBudget n ρ unit L)⁻¹) ≤
        labelShare (((ν k (p.world b₀)).prod volume).restrict (E k (p.world b₀)))
          (obs (B k (p.world b₀)) (δ (N k) L)) (p.counted b₀) z)
    (hmask : ∀ z ∈ R, SelectionMask (N k) L S τd τa f (B k (p.world b₀))
      (g k (p.world b₀)) (G k (p.world b₀)) Qd Qa z) :
    ∃ π : Measure ℝ, IsProbabilityMeasure π ∧
      0 < sourcePaletteMesh n (N k) unit L ∧
      0 < sourcePaletteBlur n (N k) unit L β ∧
      2 * sourcePaletteBlur n (N k) unit L β ≤ (N k ^ (unit * L)) ^ (-(n : ℝ)) ∧
      (∀ v : ℝ, (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ a : ℤ,
        π {w | ⌊w / (N k ^ (unit * L)) ^ (-v)⌋ = a} ≤
          ENNReal.ofReal ((N k ^ selectionBudget n ρ unit L) ^ 6 *
            (N k ^ (unit * L)) ^ (-S * v))) ∧
      (∀ (ρ' : Measure Incidence),
        ρ' ≤ nuE (((ν k (p.world b₀)).prod volume).restrict (E k (p.world b₀))) R →
        ∀ (V : Set Incidence) (C : ENNReal) (width : ℝ),
          2 * sourcePaletteBlur n (N k) unit L β ≤ width →
          (∀ z : Fin 2 → ℤ,
            ρ' (V ∩ {x | worldBin (sourcePaletteMesh n (N k) unit L) (p.world b₀, x) = z}) ≤
              C * nuE (((ν k (p.world b₀)).prod volume).restrict (E k (p.world b₀))) R
                {x | worldBin (sourcePaletteMesh n (N k) unit L) (p.world b₀, x) = z}) →
          ∀ e : ℤ,
            ρ' (V ∩ {z | ⌊(labelFrame p b₀ (B k (p.world b₀))
              (δ (N k) (p.r (p.lev b₀)))).eb z.1 3 / width⌋ = e}) ≤
              4 * C * π {w | ⌊w / width⌋ = e}) := by
  have hprob' := hprob
  obtain ⟨hN, _, hK, hL, _, _, hS, _, hdata, hpure, hangular, _⟩ := hprob'
  have hNk : 1 ≤ N k := le_trans (by norm_num) (hN k)
  have hNk0 : 0 < N k := by linarith
  have hκ : 1 ≤ p.κ := hp.one_le_slack
  have hκ0 : 0 < p.κ := by linarith
  obtain ⟨hcoef, hcost⟩ := sample_palette_floor_budget m hκ (hK.1 k) hbig
  have hpower := sample_palette_power_budget hNk hτa hτd hma hcoef
  have hinv := sample_palette_inverse_floor hNk0 hm hκ0 hcost
  let μ := ((ν k (p.world b₀)).prod volume).restrict (E k (p.world b₀))
  letI : IsFiniteMeasure μ := Submission.Lib.K4ExactProblemOps.prob_world_finite hprob k _
  have hRE : R ⊆ E k (p.world b₀) := fun z hz => (hp.counted_support b₀ z (hRF hz)).1
  have hμR : μ R = ((ν k (p.world b₀)).prod volume) R := by
    dsimp only [μ]
    rw [Measure.restrict_apply hRm, inter_eq_left.mpr hRE]
  have hR0 : μ R ≠ 0 := by
    rw [hμR]
    exact ne_of_gt (hS1pos.trans_le (measure_mono hS1R))
  have hpacket_upper : μ (p.counted b₀) ≤
      ((ν k (p.world b₀)).prod volume) (p.packet b₀) := by
    have hsubset : p.counted b₀ ⊆ p.packet b₀ := by
      intro z hz
      change z.1 ∈ p.assigned b₀ ∧ z.2 ∈
        Icc ((p.bin b₀ : ℝ) / (2 : ℝ) ^ p.T (p.lev b₀))
          (((p.bin b₀ : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b₀))
      exact ⟨(hp.counted_support b₀ z hz).2.1, (hp.counted_support b₀ z hz).2.2.1⟩
    calc μ (p.counted b₀) ≤ ((ν k (p.world b₀)).prod volume) (p.counted b₀) :=
        Measure.restrict_le_self _
      _ ≤ _ := measure_mono hsubset
  have hfloor : ENNReal.ofReal (N k ^ (-selectionBudget n ρ unit L)) *
      μ (p.counted b₀) ≤ μ R := by
    calc ENNReal.ofReal (N k ^ (-selectionBudget n ρ unit L)) * μ (p.counted b₀)
        ≤ ENNReal.ofReal (1 / (64 * (m : ℝ) * p.κ ^ 2)) *
            ((ν k (p.world b₀)).prod volume) (p.packet b₀) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hinv) hpacket_upper
      _ ≤ ((ν k (p.world b₀)).prod volume) S1 := hpacket
      _ ≤ ((ν k (p.world b₀)).prod volume) R := measure_mono hS1R
      _ = μ R := hμR.symm
  have hmenus : ∀ v : ℝ, (n : ℝ)⁻¹ ≤ v → v ≤ n →
      ∃ r ∈ Qa, unit * L * v - ma ≤ r ∧ r ≤ unit * L * v := by
    intro v hv hvn
    apply hmenu (unit * L * v)
    · simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ unit * L)
    · exact mul_le_mul_of_nonneg_left hvn (by positivity)
  obtain ⟨π, hπ, hfine, hblur, hsmall, hpal, _, hdom⟩ :=
    hp.source_parent_palette n unit β S ma τd τa
      (selectionBudget n ρ unit L) (selectionBudget n ρ unit L) (K k)
      hNk hL hu hNt hℓ hS.le hS1 hβ hma0 hunit hδ b₀ hband hfull μ
      (g k (p.world b₀) L) (hpure k _ L hL.le le_rfl).1
      (hpure k _ L hL.le le_rfl).2 (G k (p.world b₀)) Qa
      (fun r hr => (hangular k _ r (hQa r hr).1 (hQa r hr).2).1)
      (fun r hr => (hangular k _ r (hQa r hr).1 (hQa r hr).2).2)
      hmenus R hRm hR0 hRF
      (fun z hz => by simpa only [Real.rpow_neg hNk0.le] using hshare z hz)
      (fun z hz => (hmask z hz).2.1) (fun r hr z hz => (hmask z hz).2.2 r hr)
      hfloor (le_trans (by norm_num) (hK.1 k)) (prob_original_velocity_bound hprob k _).2
  refine ⟨π, hπ, hfine, hblur, hsmall, ?_, hdom⟩
  intro v hv hvn a
  apply (hpal v hv hvn a).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right hpower (by positivity)

end Problem

end
end Submission.Obl.k4_finite_affine_parent_sources
