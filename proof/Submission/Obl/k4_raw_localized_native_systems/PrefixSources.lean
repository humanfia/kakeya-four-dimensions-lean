import Submission.Obl.k4_raw_localized_native_systems.SourceLists

/-
Adapted from this LOT tree, o197, session x0690, `PrefixSources.lean` (commit
f7206748), renamed into this obligation's namespace.
-/

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Package accepted o151 for the exact-problem records used by the accepted
prefix construction. -/
theorem normalization_composition : Composition := by
  intro p hp r h w hr hrL hk
  obtain ⟨N', K', W', ω', ν', E', P', B', f', g', G', hv, ht, hn⟩ :=
    Submission.k4_known_atlas_normalization_composition
      p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp
      r h w hr hrL (by
        obtain ⟨M, D, hk⟩ := hk
        refine ⟨M, D, fun ε hε => (hk ε hε).mono ?_⟩
        rintro k ⟨κ, hκ, hκε, a, hT, hw, ⟨hC, hd, hchart, hmass⟩, hlst⟩
        exact ⟨κ, hκ, hκε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F,
          a.lst, hT, hw, hC, hd, hlst, hchart, hmass⟩)
  exact ⟨⟨N', K', p.L - r, p.d, p.S, p.η, W', ω', ν', E', P', B', f', g', G'⟩,
    hv, rfl, rfl, rfl, rfl, ht, hn⟩

/-- The accepted induction constructs any finite early prefix, so the last
source depth can be kept strictly below one. -/
theorem exists_raw_prefix {ds kr S η w ε q t ζ : ℝ}
    (hi : initialRaw) (hes : es ds kr S η) (hnb : ¬ widthRaw ds kr S η)
    (hw : 0 ≤ w) (m : ℕ) (s : ℕ → ℝ) (hm : 0 < m)
    (hs : ∀ i, i < m → 0 < s i ∧ s i ≤ 1)
    (hstep : ∀ i, i + 1 < m → s i < s (i + 1))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) (ht : 0 < t) (hζ : 0 < ζ) :
    ∃ p : Data, Near ds kr S η t p ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ 1 → |p.f r - p.f 0 - ds * r| ≤ ζ) ∧
      ∃ (r : ℕ → ℝ) (M D : ℕ),
        (∀ i, i < m → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ s i) ∧
        ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
          k4_raw_critical_segment_forests.RawAt p kr w ε q σ m s r M D k := by
  have he := extremal_of_raw hes
  have hb : ¬ BoundedWidth ds kr S η :=
    fun hb => hnb ((widthRaw_iff ds kr S η).mpr hb)
  obtain ⟨tf, htf, hfamily⟩ := k4_raw_critical_segment_forests.prefix_construction
    k4_raw_critical_segment_forests.nestedNormalizationPrepared
    forest_preparation normalization_composition (initialRaw_iff.mp hi)
    ds kr S η w he hw (uniformWidth_of_not_bounded hb hw)
    m s hm hs hstep ε q hε hε1 hq
  let tol : ℝ := min t (min ζ tf)
  have htol : 0 < tol := lt_min ht (lt_min hζ htf)
  have htolt : tol ≤ t := min_le_left _ _
  have htolζ : tol ≤ ζ := (min_le_right _ _).trans (min_le_left _ _)
  have htolf : tol ≤ tf := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨p, hp, -, -, -, hprofile⟩ := exists_prepared_near he hb
    (a := 1) (w := w) (t := tol) zero_lt_one hw htol
  have hpf := hp.mono htolf
  obtain ⟨r, M, D, hr, hraw⟩ := hfamily p hpf.1 hpf.2.1 hpf.2.2.1 hpf.2.2.2.1
    hpf.2.2.2.2.1 hpf.2.2.2.2.2
  exact ⟨p, hp.mono htolt, fun r hr hr1 => (hprofile r hr hr1).trans htolζ,
    r, M, D, fun i hi => ⟨(hr i hi).1, (hr i hi).2.1, (hr i hi).2.2.1⟩, hraw⟩

/-- A strict original-resolution subsequence of prepared early source forests.
Formats and depths are fixed before every eventual slack bound. -/
theorem exists_prepared_prefix {ds kr S η w ε q t ζ : ℝ}
    (hi : initialRaw) (hes : es ds kr S η) (hnb : ¬ widthRaw ds kr S η)
    (hw : 0 ≤ w) (m : ℕ) (s : ℕ → ℝ) (hm : 0 < m)
    (hs : ∀ i, i < m → 0 < s i ∧ s i ≤ 1)
    (hstep : ∀ i, i + 1 < m → s i < s (i + 1))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) (ht : 0 < t) (hζ : 0 < ζ) :
    ∃ p : Data, Near ds kr S η t p ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ 1 → |p.f r - p.f 0 - ds * r| ≤ ζ) ∧
      ∃ (r : ℕ → ℝ) (M D : ℕ),
        (∀ i, i < m → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ s i) ∧
        ∃ (φ : ℕ → ℕ) (a : (n : ℕ) → k4_raw_critical_segment_forests.Forest p (φ n))
          (width : (n : ℕ) → Fin (a n).C → ℝ)
          (lst : (n : ℕ) → ℕ → Fin (p.W (φ n)) → Observation → Finset (Fin (a n).C)),
          StrictMono φ ∧ ∀ n,
            (a n).RawData (width n) kr w ε q (1 / ((n : ℝ) + 1)) m s r M D ∧
            (a n).Prepared r (lst n) ∧
            (∀ i γ b, MeasurableSet {o | b ∈ lst n i γ o}) := by
  obtain ⟨p, hp, hprofile, r, M, D, hr, hfamily⟩ :=
    exists_raw_prefix hi hes hnb hw m s hm hs hstep hε hε1 hq ht hζ
  have hrL : ∀ i, i < m → 0 < r i ∧ r i ≤ p.L := by
    intro i hi
    refine ⟨(hr i hi).2.1, ?_⟩
    rw [hp.2.1]
    exact (hr i hi).2.2.trans (hs i hi).2
  obtain ⟨M', D', -, -, φ, a, width, old, hφ, hcert⟩ :=
    k4_raw_critical_segment_forests.prepared_raw_sequence forest_preparation hp.1 hm hrL hfamily
  refine ⟨p, hp, hprofile, r, M', D', hr, φ, a, width,
    fun n => sourceLists (a n) r, hφ, fun n => ?_⟩
  exact ⟨(hcert n).1, sourceLists_prepared (hcert n).2,
    fun i γ b => sourceLists_measurable (hcert n).1.2.1 i γ b⟩

end
end Submission.Obl.k4_raw_localized_native_systems
