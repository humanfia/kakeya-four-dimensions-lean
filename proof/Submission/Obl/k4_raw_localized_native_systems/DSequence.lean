import Submission.Obl.k4_raw_localized_native_systems.DSourcePrepared
import Submission.Obl.k4_raw_localized_native_systems.DSourceData
import Submission.Obl.k4_raw_localized_native_systems.Sequence

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Window

noncomputable section

theorem exists_source_d_steps {p : Data} (hp : Valid p) (hL : p.L = 1)
    {kr w ε q band : ℝ} {M D : ℕ} {sd r : ℕ → ℝ}
    (src : HomogeneousSourceSequence p kr w ε q band 2 M D sd r)
    {χ ds s vGap : ℝ} (hχ : 0 < χ) (hds : 0 ≤ ds) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hr0 : 0 ≤ r 0) (hgap : r 0 + vGap ≤ s) (hclose : s - r 0 + 2 * vGap ≤ 2 * χ)
    (hvGap : 0 < vGap) (hband0 : 0 ≤ band) (hbandχ : band ≤ χ / 1000)
    (hband1 : band ≤ 1 / 80)
    (hprofile : |p.f (r 0) - p.f 0 - ds * r 0| ≤ χ / 1000)
    (htime : kr * sd 0 + ε ≤ 1) :
    DSide p src χ ds s (s + 4) 4 := by
  obtain ⟨d⟩ := exists_source_d_data hp hL src hχ hds hs0 hs1 hr0 hgap hclose
    hvGap hband0 hbandχ hband1 hprofile htime
  have hrL : r 0 ≤ p.L := by rw [hL]; linarith only [hgap, hvGap, hs1]
  refine ⟨d.a₀, d.ell, d.a₀_pos, d.ell_pos, ?_⟩
  intro loss hloss hsmall
  filter_upwards [d.events loss hloss hsmall] with n hn
  intro MC DC Λ g hg _hg1 hrel
  apply source_d_step (nw := src.levelWidth n 0) hp hL (src.forest n) (src.core n) (src.prepared n) hχ hs0 hs1
    hr0 hrL d.u_pos d.u_eta hband0 d.packing_u (hsmall.trans d.ell_four)
    hn.1 hn.2.1 d.profile (d.time n)
    (src.width n) ?_ ?_ hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2 hg hrel MC DC Λ
  · intro b hb
    simpa only [hb] using src.width_exact n b
  · intro b hb
    simpa only [hb] using src.width_band n b

/-- The concrete global choices of the source factory satisfy every
requirement of the D-side theorem. -/
theorem d_side_of_choice {p : Data} (hp : Valid p) (hL : p.L = 1)
    {ds kr S η χ w' : ℝ} (hds : 0 ≤ ds) (hkr0 : 0 ≤ kr) (hkr1 : kr ≤ 1)
    (hS : 0 < S) (hη : 0 < η) (hχ : 0 < χ)
    {M D : ℕ} {r : ℕ → ℝ}
    (hr : ∀ i, i < 2 → |r i - sdOf kr S η χ i| ≤ epsOf kr S η χ ∧
      0 < r i ∧ r i ≤ sdOf kr S η χ i)
    (hprofile : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      |p.f z - p.f 0 - ds * z| ≤ tolOf kr S η χ)
    (src : HomogeneousSourceSequence p kr w' (epsOf kr S η χ)
      (tolOf kr S η χ) (tolOf kr S η χ) 2 M D (sdOf kr S η χ) r) :
    DSide p src χ ds (sExp kr S η) (mExp kr S η) 4 := by
  have hν := nuOf_pos hkr0 hS hη hχ
  have hs := sExp_pos hkr0 hS hη
  have hsOne : sExp kr S η ≤ 1 := sExp_lt_one.le
  have htol := tolOf_pos hkr0 hS hη hχ
  have hr₀ := hr 0 (by omega)
  have hrAbs : |r 0 - (sExp kr S η - 2 * nuOf kr S η χ)| ≤ epsOf kr S η χ := by
    simpa only [sdOf_zero] using hr₀.1
  have hrUpper : r 0 ≤ sExp kr S η - 2 * nuOf kr S η χ := by
    simpa only [sdOf_zero] using hr₀.2.2
  obtain ⟨hgap, hclose, hbandχ, hband1, htime⟩ := source_recipe_bounds hχ
    hsOne hν nuOf_le_s nuOf_le_chi
    (le_rfl : epsOf kr S η χ ≤ nuOf kr S η χ / 2)
    (le_rfl : tolOf kr S η χ ≤ nuOf kr S η χ / 10) hkr1 hrAbs hrUpper
  have hrOne : r 0 ≤ 1 := by linarith only [hgap, hν, hsOne]
  have hprof : |p.f (r 0) - p.f 0 - ds * r 0| ≤ χ / 1000 :=
    (hprofile _ hr₀.2.1.le hrOne).trans hbandχ
  change DSide p src χ ds (sExp kr S η) (sExp kr S η + 4) 4
  exact exists_source_d_steps hp hL src hχ hds hs.le hsOne hr₀.2.1.le
    hgap hclose hν htol.le hbandχ hband1 hprof (by simpa only [sdOf_zero] using htime)

end
end Submission.Obl.k4_raw_localized_native_systems
