import Submission.Obl.k4_raw_localized_native_systems.Problems
import Submission.Obl.k4_raw_critical_segment_forests
import Submission.Obl.k4_true_forest_own_depth_preparation
import Submission.Obl.k4_known_atlas_normalization_composition

/-
Adapted from this LOT tree, o197, session x0690, `SourceForests.lean` (commit
f7206748), renamed into this obligation's namespace.
-/

/-! Extract nested true sources using accepted o192. Their assignments and
incidence floors precede every subsequent analytical deletion. -/

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Uniform finite widths are exactly what the failure of the frozen bounded
width conclusion provides. -/
theorem raw_uniformWidth {ds kr S η w : ℝ}
    (hnb : ¬ widthRaw ds kr S η) (hw : 0 ≤ w) : unif ds kr S η w := by
  have h := uniformWidth_of_not_bounded
    (fun hb => hnb ((widthRaw_iff ds kr S η).mpr hb)) hw
  intro a ha
  obtain ⟨t, ht, hall⟩ := h a ha
  refine ⟨t, ht, fun N K d W ω ν E P B f g G hp hd hH => ?_⟩
  exact hall ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
    hp rfl rfl rfl hd hH

/-- Fixed formats and a fixed list of actual depths work at every sample
accuracy, in the original resolution sequence. -/
theorem exists_raw_source {ds kr S η w ε q t ζ : ℝ}
    (hi : initialRaw) (hS : 0 < S) (hη : 0 < η) (hes : es ds kr S η)
    (hnb : ¬ widthRaw ds kr S η) (hw : 0 ≤ w)
    (m : ℕ) (s : ℕ → ℝ)
    (hgrid : 0 < m ∧ 0 < s 0 ∧
      (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) (ht : 0 < t) (hζ : 0 < ζ) :
    ∃ p : Data, Near ds kr S η t p ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ 1 → |p.f r - p.f 0 - ds * r| ≤ ζ) ∧
      ∃ (r : ℕ → ℝ) (M D : ℕ), r (m - 1) = 1 ∧
        (∀ i, i < m → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ 1) ∧
        ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
          k4_raw_critical_segment_forests.RawAt p kr w ε q σ m s r M D k := by
  obtain ⟨tf, htf, hfamily⟩ := Submission.k4_raw_critical_segment_forests
    Submission.k4_true_forest_own_depth_preparation
    Submission.k4_known_atlas_normalization_composition hi
    ds kr S η w hS hη hes hw (raw_uniformWidth hnb hw)
    m s hgrid ε q hε hε1 hq
  let tol : ℝ := min t (min ζ tf)
  have htol : 0 < tol := lt_min ht (lt_min hζ htf)
  have htolt : tol ≤ t := min_le_left _ _
  have htolζ : tol ≤ ζ := (min_le_right _ _).trans (min_le_left _ _)
  have htolf : tol ≤ tf := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨p, hp, -, -, -, hprofile⟩ := exists_prepared_near (extremal_of_raw hes)
    (fun hb => hnb ((widthRaw_iff ds kr S η).mpr hb))
    (a := 1) (w := w) (t := tol) zero_lt_one hw htol
  have hp' := hp
  obtain ⟨hv, hL, hpS, hpη, hd, hH⟩ := hp'
  obtain ⟨r, M, D, hrfinal, hr, hraw⟩ := hfamily
    p.N p.K p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
    (by
      change prob p.N p.K 1 p.d S η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      simpa only [Valid, hL, hpS, hpη] using hv)
    (hd.trans_le (by linarith))
    (by
      change kr - tf < H p.N p.K 1 p.W p.ω p.ν p.E p.B p.f
      simpa only [Horizon, hL] using lt_of_le_of_lt (by linarith : kr - tf ≤ kr - tol) hH)
  refine ⟨p, hp.mono htolt, fun r hr hr1 => (hprofile r hr hr1).trans htolζ,
    r, M, D, hrfinal, hr, fun σ hσ => ?_⟩
  apply (hraw σ hσ).mono
  rintro k ⟨κ, T, C, lev, par, γ, j, c, u, Q, R, A, F, vwidth, hκ, hcore, htime, hwidth⟩
  exact ⟨⟨κ, T, C, lev, par, γ, j, c, u, Q, R, A, F⟩,
    vwidth, hκ, hcore, htime, hwidth⟩

/-- Adapter of accepted o191 to the finite forest record of accepted o192.
It retains the whole original assignment of each selected label. -/
theorem forest_preparation : k4_raw_critical_segment_forests.Preparation := by
  intro p hp m r hm hr M D
  obtain ⟨M', D', hM, hD, hprep⟩ := Submission.k4_true_forest_own_depth_preparation
    p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp m r hm hr M D
  refine ⟨M', D', hM, hD, fun σ hσ => ?_⟩
  obtain ⟨ρ, hρ, hρσ, hlate⟩ := hprep σ hσ
  refine ⟨ρ, hρ, hρσ, hlate.mono ?_⟩
  intro k hk a hκ hT hcore
  have hcore' := hcore
  unfold k4_raw_critical_segment_forests.Forest.Core at hcore'
  rw [hκ] at hcore'
  obtain ⟨C', emb, par', F', lst, hC, hnew, hsub, hlist, hprior, -, -⟩ :=
    hk a.T a.C a.lev a.par a.γ a.j a.c a.u a.Q a.R a.A a.F hT hcore'
  exact ⟨⟨C', emb, par', F'⟩, lst, hC, hnew, hsub, hlist, hprior⟩

/-- Simultaneously prepare all source layers along a strict subsequence.
The returned lists and floors refer to the actual retained forests, while
relative profiles remain those of the exact original problem. -/
theorem exists_prepared_sources {ds kr S η w ε q t ζ : ℝ}
    (hi : initialRaw) (hS : 0 < S) (hη : 0 < η) (hes : es ds kr S η)
    (hnb : ¬ widthRaw ds kr S η) (hw : 0 ≤ w)
    (m : ℕ) (s : ℕ → ℝ)
    (hgrid : 0 < m ∧ 0 < s 0 ∧
      (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) (ht : 0 < t) (hζ : 0 < ζ) :
    ∃ p : Data, Near ds kr S η t p ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ 1 → |p.f r - p.f 0 - ds * r| ≤ ζ) ∧
      ∃ (r : ℕ → ℝ) (M D : ℕ), r (m - 1) = 1 ∧
        (∀ i, i < m → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ 1) ∧
        ∃ (φ : ℕ → ℕ) (a : (n : ℕ) → k4_raw_critical_segment_forests.Forest p (φ n))
          (width : (n : ℕ) → Fin (a n).C → ℝ)
          (lst : (n : ℕ) → ℕ → Fin (p.W (φ n)) → Observation → Finset (Fin (a n).C)),
          StrictMono φ ∧ ∀ n,
            (a n).RawData (width n) kr w ε q (1 / ((n : ℝ) + 1)) m s r M D ∧
            (a n).Prepared r (lst n) := by
  obtain ⟨p, hp, hprofile, r, M, D, hrfinal, hr, hfamily⟩ :=
    exists_raw_source hi hS hη hes hnb hw m s hgrid hε hε1 hq ht hζ
  have hrL : ∀ i, i < m → 0 < r i ∧ r i ≤ p.L := by
    intro i hi
    exact ⟨(hr i hi).2.1, by simpa only [hp.2.1] using (hr i hi).2.2⟩
  obtain ⟨M', D', -, -, φ, a, width, lst, hφ, hcert⟩ :=
    k4_raw_critical_segment_forests.prepared_raw_sequence forest_preparation hp.1
      hgrid.1 hrL hfamily
  exact ⟨p, hp, hprofile, r, M', D', hrfinal, hr, φ, a, width, lst, hφ, hcert⟩

end
end Submission.Obl.k4_raw_localized_native_systems
