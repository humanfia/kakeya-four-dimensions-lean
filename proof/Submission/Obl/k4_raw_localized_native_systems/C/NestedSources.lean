import Submission.Obl.k4_raw_localized_native_systems.C.PacketInterfaces
import Submission.Obl.k4_raw_localized_native_systems.C.Problems
import Submission.Obl.k4_raw_critical_segment_forests.AnalyticLists
import Submission.Obl.k4_raw_critical_segment_forests.Prefix
import Submission.Obl.k4_raw_critical_segment_forests.AngularCompletion
import Submission.Obl.k4_true_forest_own_depth_preparation.Preparation
import Submission.Obl.k4_known_atlas_normalization_composition

/-
Adapted from this LOT tree, o178, session x0596, `NestedSources.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_raw_critical_segment_forests

noncomputable section

set_option maxRecDepth 4096

/-- Measurable incidence supports have a measurable finite-list decoder
with the same pointwise cardinality bound as any given decoder. -/
theorem measurable_decoder_of_source_images {C : ℕ}
    (F : Fin C → Set Inc) (hF : ∀ b, MeasurableSet (F b))
    (O : Inc → Obs) (hO : Measurable O) (κ : ℝ)
    (L : Obs → Finset (Fin C)) (hL : ∀ o, ((L o).card : ℝ) ≤ κ)
    (hknown : ∀ b p, p ∈ F b → b ∈ L (O p)) :
    ∃ Λ : Obs → Finset (Fin C),
      (∀ b, MeasurableSet {o | b ∈ Λ o}) ∧
      (∀ o, ((Λ o).card : ℝ) ≤ κ) ∧
      ∀ b p, p ∈ F b → b ∈ Λ (O p) := by
  obtain ⟨Λ, hm, hc, hs⟩ := analytic_measurable_lists
    (fun b => O '' F b) (fun b => (hF b).analyticSet_image hO) κ L hL
    (fun b o ho => by
      obtain ⟨p, hp, rfl⟩ := ho
      exact hknown b p hp)
  exact ⟨Λ, hm, hc, fun b p hp => hs b (O p) ⟨p, hp, rfl⟩⟩

/-- The accepted preparation theorem, on the raw-forest record interface. -/
theorem raw_forest_preparation :
    Submission.Obl.k4_raw_critical_segment_forests.Preparation := by
  intro p hp m r hm hr M D
  obtain ⟨M', D', hM, hD, H⟩ :=
    Submission.Obl.k4_true_forest_own_depth_preparation.preparation
      p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp
      m r hm hr M D
  refine ⟨M', D', hM, hD, ?_⟩
  intro σ hσ
  obtain ⟨ρ, hρ, hρσ, H⟩ := H σ hσ
  refine ⟨ρ, hρ, hρσ, H.mono ?_⟩
  intro k hk a hκ hT hcore
  unfold Submission.Obl.k4_raw_critical_segment_forests.Forest.Core at hcore
  rw [hκ] at hcore
  obtain ⟨C', emb, par, F, lst, hC, hnew, hsub, hlist, hprior, _, _⟩ :=
    hk a.T a.C a.lev a.par a.γ a.j a.c a.u a.Q a.R a.A a.F hT hcore
  exact ⟨⟨C', emb, par, F⟩, lst, hC, hnew, hsub, hlist, hprior⟩

/-- Accepted native normalization and finite lifting give the composition
input of the raw-prefix construction. -/
theorem raw_known_composition : Composition := by
  intro p hp r h w hr hrL hk
  obtain ⟨M, D, hk⟩ := hk
  have hknown : ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ p.N k ^ ε ∧
        ∃ (T C : ℕ) (γ : Fin C → Fin (p.W k)) (j : Fin C → Fin (2 ^ T))
          (c u : Fin C → EuclideanSpace ℝ (Fin 2))
          (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
          (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set Traj)
          (F : Fin C → Set Inc) (lst : Fin (p.W k) → Obs → Finset (Fin C)),
        (2 : ℝ) ^ T ≤ p.N k ^ (h + ε) ∧
        (∀ b, |(Q b).det| * (4 : ℝ) ^ T ≤ p.N k ^ (-w + ε)) ∧
        (C : ℝ) ≤ p.N k ^ M ∧
        (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
        (∀ γ o, ((lst γ o).card : ℝ) ≤ κ) ∧
        (∀ b, chart (p.N k) M D κ T ((j b : ℕ) : ℝ) r (p.B k (γ b))
          (p.E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b)
          (∀ z ∈ F b, b ∈ lst (γ b) (obs (p.B k (γ b)) (δ (p.N k) p.L) z))) ∧
        ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (p.ω k (γ b)) *
          ((p.ν k (γ b)).prod volume) (F b) := by
    refine ⟨M, D, fun ε hε => (hk ε hε).mono ?_⟩
    rintro k ⟨κ, hκ, hκε, a, hT, hw, ⟨hC, hsep, hchart, hmass⟩, hlst⟩
    exact ⟨κ, hκ, hκε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F,
      a.lst, hT, hw, hC, hsep, hlst, hchart, hmass⟩
  obtain ⟨N, K, W, ω, ν, E, P, B, f, g, G, hv, ht, hn⟩ :=
    Submission.k4_known_atlas_normalization_composition
      p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      hp r h w hr hrL hknown
  exact ⟨⟨N, K, p.L - r, p.d, p.S, p.η, W, ω, ν, E, P, B, f, g, G⟩,
    hv, rfl, rfl, rfl, rfl, ht, hn⟩

theorem uniform_width_of_not_bounded {ds kr S η w : ℝ}
    (hn : ¬ BoundedWidth ds kr S η) (hw : 0 ≤ w) : UniformWidth ds kr S η w := by
  intro a ha
  obtain ⟨t, ht, hall⟩ := (not_boundedWidth_iff ds kr S η).mp hn a ha w hw
  exact ⟨t, ht, fun p hp hL hS hη hd hH => hall p ⟨hp, hL, hS, hη, hd, hH⟩⟩

/-- Any finite positive depth prefix, even one ending below one, has nested
true source systems of arbitrarily large relative width under failure of BW.
The actual depths and formats are fixed before every inner chart loss. -/
theorem nested_raw_prefix (hi : initialRaw) {ds kr S η w : ℝ}
    (hes : Extremal ds kr S η) (hn : ¬ BoundedWidth ds kr S η) (hw : 0 ≤ w)
    (m : ℕ) (s : ℕ → ℝ) (hm : 0 < m)
    (hs : ∀ i, i < m → 0 < s i ∧ s i ≤ 1)
    (hstep : ∀ i, i + 1 < m → s i < s (i + 1))
    {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) :
    ∃ t : ℝ, 0 < t ∧ ∀ p : Data, Near ds kr S η t p →
      ∃ (r : ℕ → ℝ) (M D : ℕ),
        (∀ i, i < m → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ s i ∧
          (s i = 1 → r i = 1)) ∧
        ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
          Submission.Obl.k4_raw_critical_segment_forests.RawAt p kr w ε q σ m s r M D k := by
  have hi' : Initial := fun p hp h hh =>
    hi p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp h hh
  obtain ⟨t, ht, H⟩ :=
    Submission.Obl.k4_raw_critical_segment_forests.prefix_construction
      Submission.Obl.k4_raw_critical_segment_forests.nestedNormalizationPrepared
      raw_forest_preparation raw_known_composition hi' ds kr S η w hes hw
      (uniform_width_of_not_bounded hn hw) m s hm hs hstep ε q hε hε1 hq
  exact ⟨t, ht, fun p hp => H p hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
    hp.2.2.2.2.1 hp.2.2.2.2.2⟩

/-- Preparation of the actual nested family supplies full-prior saturation
and own-depth lists along one common cofinal sequence. Every frame, world and
full assignment is retained, and the selected events remain nested. -/
theorem prepared_nested_prefix (hi : initialRaw) {ds kr S η w : ℝ}
    (hes : Extremal ds kr S η) (hn : ¬ BoundedWidth ds kr S η) (hw : 0 ≤ w)
    (m : ℕ) (s : ℕ → ℝ) (hm : 0 < m)
    (hs : ∀ i, i < m → 0 < s i ∧ s i ≤ 1)
    (hstep : ∀ i, i + 1 < m → s i < s (i + 1))
    {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) :
    ∃ t : ℝ, 0 < t ∧ ∀ p : Data, Near ds kr S η t p →
      ∃ (r : ℕ → ℝ) (M D : ℕ),
        (∀ i, i < m → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ s i ∧
          (s i = 1 → r i = 1)) ∧
        ∃ (φ : ℕ → ℕ) (a : (n : ℕ) → Forest p (φ n))
          (width : (n : ℕ) → Fin (a n).C → ℝ)
          (lst : (n : ℕ) → ℕ → Fin (p.W (φ n)) → Observation → Finset (Fin (a n).C)),
          StrictMono φ ∧ ∀ n,
            (a n).RawData (width n) kr w ε q (1 / ((n : ℝ) + 1)) m s r M D ∧
            (a n).Prepared r (lst n) := by
  obtain ⟨t, ht, H⟩ := nested_raw_prefix hi hes hn hw m s hm hs hstep hε hε1 hq
  refine ⟨t, ht, ?_⟩
  intro p hp
  obtain ⟨r, M, D, hr, hraw⟩ := H p hp
  have hdepth : ∀ i, i < m → 0 < r i ∧ r i ≤ p.L := by
    intro i hi
    refine ⟨(hr i hi).2.1, ?_⟩
    rw [hp.2.1]
    exact (hr i hi).2.2.1.trans (hs i hi).2
  obtain ⟨M', D', _, _, φ, a, width, lst, hφ, hseq⟩ :=
    prepared_raw_sequence raw_forest_preparation hp.1 hm hdepth hraw
  exact ⟨r, M', D', hr, φ, a, width, lst, hφ, hseq⟩

end
end Submission.Obl.k4_raw_localized_native_systems.C
