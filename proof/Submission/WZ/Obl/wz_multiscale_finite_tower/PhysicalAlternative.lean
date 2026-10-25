-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.PhysicalAlternative.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Physical
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.LocalAlternative

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (ConvexCount SlabBound doubled FibreCover coverScale convexCount_mono slabBound_mono)

theorem OneScale.to_alternative {σ ω : ℝ} (hOne : OneScale σ ω) :
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.OneScaleAlternative σ ω := by
  intro ζ hζ
  obtain ⟨α, hα, κ, hκ, η, hη, H⟩ := hOne ζ hζ
  refine ⟨α, hα, κ, hκ, η, hη, ?_⟩
  intro d hd hd100 n x v Y hA
  have hA' : Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y := by
    simpa only [Admissible, KatzTao, Frostman,
      WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Admissible, ConvexCount,
      WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slab, true_and] using hA
  rcases H d hd hd100 n x v Y hA' with hV | hF
  · exact Or.inl hV
  · right
    simpa only [Factorization, WangZahlLot.Obl.wz_rescaled_fibre_alternatives.GlobalCover,
      KatzTao, Frostman, ConvexCount, SlabBound, doubled,
      WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slab, true_and, and_assoc] using hF

/-- The rescaled one-step cover, with density and counting losses measured at the
bottom scale of the whole hierarchy. -/
def PhysicalCover (d r s ζ C ω : ℝ) (y w : Space) (n : ℕ)
    (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  ∃ (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ)
    (y' w' : Fin N → Space) (f : Fin n → Fin N),
    (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
    ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i) ∧
    r * (s / r) ^ (1 - ω / 100) ≤ C * ρ ∧ ρ ≤ C * (r * (s / r) ^ (ω / 100)) ∧
    (∀ k, ‖w' k‖ = 1 ∧ Tube ρ (y' k) (w' k) ⊆ Tube (2 * r) y w) ∧
    (∀ i ∈ S, Tube s (x i) (v i) ⊆ doubled ρ (y' (f i)) (w' (f i))) ∧
    ConvexCount ρ (d ^ (-ζ)) (fun _ => True) (fun k => Tube ρ (y' k) (w' k)) ∧
    SlabBound (doubled r y w) (d ^ (-ζ)) (fun _ => True) (fun k => Tube ρ (y' k) (w' k)) ∧
    ∀ k, SlabBound (doubled ρ (y' k) (w' k)) (d ^ (-ζ))
      (fun i => i ∈ S ∧ f i = k) (fun i => Tube s (x i) (v i))

lemma physicalCover_of_fibreCover {d r s ζ C ω : ℝ} {y w : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : FibreCover r s ζ C ω y w x v Y)
    (hd : 0 < d) (hdr : d ≤ s / r) (hζ : 0 ≤ ζ) :
    PhysicalCover d r s ζ C ω y w n x v Y := by
  obtain ⟨S, Z, ρ, N, y', w', f, hZ, hmass, hlo, hhi, hw, hsub, hK, hF, hf⟩ := hF
  have hp : d ^ ζ ≤ (s / r) ^ ζ := Real.rpow_le_rpow hd.le hdr hζ
  have hn : (s / r) ^ (-ζ) ≤ d ^ (-ζ) :=
    Real.rpow_le_rpow_of_nonpos hd hdr (neg_nonpos.mpr hζ)
  exact ⟨S, Z, ρ, N, y', w', f, hZ,
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hp) le_rfl).trans hmass,
    hlo, hhi, hw, hsub, convexCount_mono hn hK, slabBound_mono hn hF,
    fun k => slabBound_mono hn (hf k)⟩

/-- A large physical gap admits a uniform improvement-or-insertion alternative.
Its improvement factor is already in the form used by the telescoping product. -/
theorem OneScale.physical_on_large_gap {σ ω : ℝ} (hOne : OneScale σ ω)
    (hσ : 0 ≤ σ) (hω : 0 < ω) (hω1 : ω ≤ 1)
    {ζ h : ℝ} (hζ : 0 < ζ) (hh : 0 < h) :
    ∃ α κ θ c : ℝ, 0 < α ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ 1 ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ d r s : ℝ, 0 < d → d ≤ 1 → 0 < r → 0 < s → d * r ≤ s →
      s ≤ c * r → r ≤ 1 → s / r ≤ d ^ h → ∀ y w : Space, ‖w‖ = 1 → ∀ n x v Y,
      PhysicalFrame d r s θ y w n x v Y →
      ENNReal.ofReal (κ * r ^ 2 * volumeFactor σ ω (s / r) n * (s / r) ^ (-α)) ≤
        volume (⋃ i, Y i) ∨ PhysicalCover d r s ζ coverScale ω y w n x v Y := by
  obtain ⟨α, κ, hα, hκ, η, c, hη, hc, hc1, HP⟩ :=
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.local_alternative
      hσ hω hω1 hOne.to_alternative hζ
  refine ⟨α, κ, min 1 (h * η), c, hα, hκ, lt_min zero_lt_one (mul_pos hh hη),
    min_le_left _ _, hc, hc1, ?_⟩
  intro d r s hd hd1 hr hs hdr hsr hr1 hgap y w hw n x v Y hF
  have hF' := hF.to_fibre hd hd1 hr hs hη.le hgap (min_le_right _ _)
  rcases HP η r s hη le_rfl hs hsr hr1 y w hw n x v Y hF' with hV | hC
  · left
    convert hV using 1
    congr 1
    dsimp [volumeFactor]
    rw [sub_eq_add_neg, Real.rpow_add (div_pos hs hr)]
    field_simp
  · exact Or.inr (physicalCover_of_fibreCover hC hd ((le_div_iff₀ hr).mpr hdr) hζ.le)

end WangZahlLot.Obl.wz_multiscale_finite_tower
