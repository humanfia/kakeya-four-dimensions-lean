-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalPrismPieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPrismDensity
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismNeighborhood

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- A uniform planar shading localized to a ball yields actual prism pieces with
average density, mass retention, exact crossings, and coarse containment.
All angular and scale conditions remain explicit. -/
theorem local_planar_prism_piece_refinement :
    ∃ D : ℕ, 0 < D ∧ ∀ (δ ρ a b c lam density t r : ℝ), 0 < δ →
      0 < r → b ≤ r → c ≤ r →
      16 * δ ≤ a → a ≤ b → 16 * δ ≤ c → c ≤ 1 / 2 →
      2 * b ≤ ρ → ρ ≤ 1 → 2560 * c ≤ lam → 0 ≤ density →
      ∀ (e : V ≃ₗᵢ[ℝ] V) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (y w p₀ : V),
      (∀ i, ‖v i‖ = 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
      (∀ i, T δ (x i) (v i) ⊆ T ρ y w) →
      (⋃ i, Y i) ⊆ ball p₀ r ∩ {p | |e (p - p₀) 0 - t| ≤ 2 * δ} →
      o (lam * n * δ ^ 2) ≤ ∑ i, μ (Y i) →
      o (density * a * r ^ 2) ≤ μ (⋃ i, Y i) →
      (∀ i, 1 / 2 ≤ |e (v i) 2| ∧ c * |e (v i) 0| ≤ a / 16 ∧
        c * |e (v i) 1| ≤ b / 16) →
      ∀ M : ENNReal, M ≠ 0 → M ≠ ⊤ →
      (∀ p ∈ ⋃ i, Y i, M ≤ multiplicity Y p) →
      (∀ p, multiplicity Y p ≤ 2 * M) →
      ∃ (F : Finset V) (Z : Fin n → Set V) (H : V → Set V),
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        (↑F : Set V).PairwiseDisjoint (fun z => P a b c z e) ∧
        (∀ z ∈ F, MeasurableSet (H z) ∧ H z ⊆ P a b c z e ∧
          (H z).Nonempty ∧ P a b c z e ⊆ T (2 * ρ) y w) ∧
        (⋃ z ∈ F, H z) = ⋃ i, Z i ∧
        (∑ i, μ (Y i)) ≤ (D : ENNReal) * ∑ i, μ (Z i) ∧
        o (density * F.card * (a * b * c)) ≤ (D : ENNReal) * ∑ z ∈ F, μ (H z) ∧
        (∀ i z, z ∈ F → (Z i ∩ H z).Nonempty →
          Z i ∩ P a b c z e ⊆ H z ∧
          (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a b c z e), |e (p - z) 2| = c / 2) ∧
          (∀ s ∈ ({-c / 2, c / 2} : Set ℝ),
            ∃ p ∈ T δ (x i) (v i) ∩ P a b c z e, e (p - z) 2 = s)) := by
  classical
  obtain ⟨D, hD, hgeom⟩ := geometric_prism_piece_refinement
  refine ⟨128 * D, by omega, ?_⟩
  intro δ ρ a b c lam density t r hδ hr hbr hcr hδa hab hδc hc hbρ hρ1 hbudget hdensity
    e n x v Y y w p₀ hY hcover hslab hdense hvol hdir M hM0 hMtop hlower hupper
  have ha : 0 < a := by linarith
  have hb : 0 < b := ha.trans_le hab
  have hc0 : 0 < c := by linarith
  have hbounded : TotallyBounded (⋃ i, Y i) :=
    (isCompact_closedBall p₀ r).totallyBounded.subset
      ((hslab.trans inter_subset_left).trans ball_subset_closedBall)
  obtain ⟨F₀, Z, H, hZ, hdisj, hH, hunion, hmass, hcross⟩ :=
    hgeom δ a b c lam hδ hδa (hδa.trans hab) hδc hc hbudget e n x v Y hY hbounded hdense hdir
  let F := F₀.filter (fun z => (H z).Nonempty)
  have hFF (z : V) (hz : z ∈ F) : z ∈ F₀ := (Finset.mem_filter.mp hz).1
  have hnonempty (z : V) (hz : z ∈ F) : (H z).Nonempty := (Finset.mem_filter.mp hz).2
  have hunion' : (⋃ z ∈ F, H z) = ⋃ i, Z i := by
    rw [← hunion]
    ext p
    constructor
    · intro hp
      obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
      exact mem_iUnion₂.mpr ⟨z, hFF z hz, hpz⟩
    · intro hp
      obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
      exact mem_iUnion₂.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, ⟨p, hpz⟩⟩, hpz⟩
  have hdisj' : (↑F : Set V).PairwiseDisjoint (fun z => P a b c z e) :=
    fun z hz z' hz' hne => hdisj (hFF z hz) (hFF z' hz') hne
  have hcontained (z : V) (hz : z ∈ F) : P a b c z e ⊆ T (2 * ρ) y w := by
    obtain ⟨p, hpH⟩ := hnonempty z hz
    have hpZ : p ∈ ⋃ i, Z i := hunion' ▸ mem_iUnion₂.mpr ⟨z, hz, hpH⟩
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hpZ
    have hi := hcross i z (hFF z hz) ⟨p, hpi, hpH⟩
    exact crossing_prism_subset_expanded_coarse ha.le hab hb hc0 hbρ e (hcover i) hi.2.2
  have hH' (z : V) (hz : z ∈ F) :
      MeasurableSet (H z) ∧ H z ⊆ P a b c z e ∧ (H z).Nonempty :=
    ⟨(hH z (hFF z hz)).1, (hH z (hFF z hz)).2, hnonempty z hz⟩
  have hden := local_prism_piece_average_density ha.le hb.le hc0.le (by positivity : 0 ≤ 2 * δ)
    (by linarith : 2 * δ ≤ a) hr.le hbr hcr
    hdensity e F Y Z H (fun i => (hY i).2.1) hZ hdisj' hH' hslab hunion'
    hM0 hMtop hlower hupper hmass hvol
  refine ⟨F, Z, H, hZ, hdisj', (fun z hz => ⟨(hH' z hz).1,
    (hH' z hz).2.1, (hH' z hz).2.2, hcontained z hz⟩), hunion', ?_, ?_, ?_⟩
  · exact hmass.trans (mul_le_mul_left (show (D : ENNReal) ≤ ((128 * D : ℕ) : ENNReal) from
      Nat.cast_le.mpr (by omega)) _)
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hden
  · intro i z hz hmeet
    exact hcross i z (hFF z hz) hmeet

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
