-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Local.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Products

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- A normalized local arrangement whose errors are measured at a separate bottom scale. -/
def FrameAdmissible (d r θ : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧
    (∀ i, ‖v i‖ = 1 ∧ Tube r (x i) (v i) ⊆ Metric.ball 0 1 ∧
      MeasurableSet (Y i) ∧ Y i ⊆ Tube r (x i) (v i)) ∧
    (∀ i j, i ≠ j → volume (Tube r (x i) (v i) ∩ Tube r (x j) (v j)) ≤
      1 / 2 * volume (Tube r (x i) (v i))) ∧
    ENNReal.ofReal (d ^ θ * n * r ^ 2) ≤ ∑ i, volume (Y i) ∧
    KatzTao r (d ^ (-θ)) n x v ∧ Frostman r (d ^ (-θ)) n x v

theorem FrameAdmissible.to_admissible {d r θ η : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : FrameAdmissible d r θ n x v Y)
    (hden : r ^ η ≤ d ^ θ) : Admissible r η (d ^ (-θ)) (d ^ (-θ)) n x v Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2⟩
  apply le_trans (ENNReal.ofReal_le_ofReal _) h.2.2.2.1
  gcongr

/-- A large logarithmic gap converts bottom-scale errors to local-scale errors. -/
theorem local_density_power {d r h θ η : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hr : 0 ≤ r) (hη : 0 ≤ η) (hgap : r ≤ d ^ h) (hθη : θ ≤ h * η) :
    r ^ η ≤ d ^ θ := by
  calc
    r ^ η ≤ (d ^ h) ^ η := Real.rpow_le_rpow hr hgap hη
    _ = d ^ (h * η) := (Real.rpow_mul hd.le _ _).symm
    _ ≤ d ^ θ := Real.rpow_le_rpow_of_exponent_ge hd hd1 hθη

theorem FrameAdmissible.to_local {d r h θ η : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hA : FrameAdmissible d r θ n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hη : 0 ≤ η) (hgap : r ≤ d ^ h) (hθη : θ ≤ h * η) :
    Admissible r η (r ^ (-η)) (r ^ (-η)) n x v Y := by
  have hp := local_density_power hd hd1 hr.le hη hgap hθη
  have hi : d ^ (-θ) ≤ r ^ (-η) := by
    rw [Real.rpow_neg hd.le, Real.rpow_neg hr.le]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hr η) hp
  exact (hA.to_admissible hp).mono hr hr1 le_rfl hi hi

/-- The geometric conclusion of the one-scale hypothesis with separate local and bottom scales. -/
def Factorization (d r ζ ω : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  ∃ (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ)
    (y w : Fin N → Space) (f : Fin n → Fin N),
    (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
    ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i) ∧
    r ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ r ^ (ω / 100) ∧
    (∀ k, ‖w k‖ = 1) ∧
    (∀ i ∈ S, Tube r (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i))) ∧
    KatzTao ρ (d ^ (-ζ)) N y w ∧ Frostman ρ (d ^ (-ζ)) N y w ∧
    ∀ k (u : Space) (t s : ℝ), ‖u‖ = 1 → 0 < s →
      ENNReal.ofReal (Set.ncard {i | i ∈ S ∧ f i = k ∧
        Tube r (x i) (v i) ⊆ Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩
          {p | |inner ℝ u p - t| ≤ s}} : ℝ) *
        volume (Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤
      ENNReal.ofReal (d ^ (-ζ) * Set.ncard {i | i ∈ S ∧ f i = k}) *
        volume (Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩
          {p | |inner ℝ u p - t| ≤ s})

def OneScale (σ ω : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ r : ℝ, 0 < r → r ≤ 1 / 100 → ∀ n x v Y,
    Admissible r η (r ^ (-η)) (r ^ (-η)) n x v Y →
      VolumeBound σ ω κ α r n Y ∨ Factorization r r ζ ω n x v Y

theorem Factorization.change_base {d d' r ζ ω : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Factorization d r ζ ω n x v Y) (hd' : 0 < d') (hdd : d' ≤ d) (hζ : 0 ≤ ζ) :
    Factorization d' r ζ ω n x v Y := by
  obtain ⟨S, Z, ρ, N, y, w, f, hZ, hmass, hlo, hhi, hw, hsub, hK, hF, hfiber⟩ := h
  have hp : d' ^ ζ ≤ d ^ ζ := Real.rpow_le_rpow hd'.le hdd hζ
  have hn : d ^ (-ζ) ≤ d' ^ (-ζ) :=
    Real.rpow_le_rpow_of_nonpos hd' hdd (neg_nonpos.mpr hζ)
  refine ⟨S, Z, ρ, N, y, w, f, hZ, ?_, hlo, hhi, hw, hsub, hK.mono hn, hF.mono hn, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hp) (by positivity)).trans hmass
  · intro k u t s hu hs
    exact (hfiber k u t s hu hs).trans (by gcongr)

/-- Apply the one-scale hypothesis uniformly to all normalized arrangements on a large gap. -/
theorem OneScale.on_large_gap {σ ω : ℝ} (hOne : OneScale σ ω)
    {ζ h : ℝ} (hζ : 0 < ζ) (hh : 0 < h) :
    ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
    ∀ d r : ℝ, 0 < d → d ≤ 1 → d ≤ r → r ≤ 1 / 100 → r ≤ d ^ h →
      ∀ n x v Y, FrameAdmissible d r θ n x v Y →
      VolumeBound σ ω κ α r n Y ∨ Factorization d r ζ ω n x v Y := by
  obtain ⟨α, hα, κ, hκ, η, hη, hloc⟩ := hOne ζ hζ
  refine ⟨α, hα, κ, hκ, min 1 (h * η), lt_min zero_lt_one (mul_pos hh hη),
    min_le_left _ _, ?_⟩
  intro d r hd hd1 hdr hr100 hgap n x v Y hA
  have hr : 0 < r := hd.trans_le hdr
  have hlocal := hA.to_local hd hd1 hr (by linarith) hη.le hgap (min_le_right _ _)
  rcases hloc r hr hr100 n x v Y hlocal with hV | hF
  · exact Or.inl hV
  · exact Or.inr (hF.change_base hd hdr hζ.le)

end WangZahlLot.Obl.wz_multiscale_finite_tower
