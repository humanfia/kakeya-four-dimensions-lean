-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreRowLists.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.PolynomialBinPower
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.NeighborhoodPalettes

/-!
# Few polynomial bins along one fiber

The witness polynomials of the states of one grid fiber agree, on their own
long time rows, with graph values listed in the coarse lists of nearby coarse
cubes. Sampling times (x0212's `PolynomialBinPower`) then bounds the number of
their coefficient bins by a power of the budget.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set

/-- Coefficient bins of a vector of polynomials. -/
noncomputable def polyBins (M : ℕ) (ε : ℝ) (P : Fin 2 → Polynomial ℝ) : Fin 2 → Fin (M + 1) → ℤ :=
  fun e k => ⌊(P e).coeff k / ε⌋

/-- A finite set of vectors over `Fin 2` is at most the product of its two projections. -/
theorem card_le_card_proj_mul {β : Type*} [DecidableEq β] (S : Finset (Fin 2 → β)) :
    (S.card : ℝ) ≤ ((S.image fun c => c 0).card : ℝ) * ((S.image fun c => c 1).card : ℝ) := by
  classical
  have hinj : Set.InjOn (fun c : Fin 2 → β => (c 0, c 1)) S := by
    intro c _ c' _ h
    simp only [Prod.mk.injEq] at h
    funext e
    fin_cases e
    · exact h.1
    · exact h.2
  have hsub : S.image (fun c : Fin 2 → β => (c 0, c 1)) ⊆
      (S.image fun c => c 0) ×ˢ (S.image fun c => c 1) := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hc, Finset.mem_image_of_mem _ hc⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_product] at h1
  exact_mod_cast h1

/-- The fiber list bound. `Q` is the set of states of the fiber; `Pn q` the
normalized witness polynomial of `q`, `Tw q ⊆ [0,1]` its witness time row,
`phys q τ` the physical point of its witness at time `τ`, `lab q τ` the row bin
of the graph there, listed in the coarse list `Lc` of its coarse cube. -/
theorem fiber_bins_card_le (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Fin 3 → ℤ)) (Pn : (Fin 3 → ℤ) → Fin 2 → Polynomial ℝ)
      (Tw : (Fin 3 → ℤ) → Set ℝ) (phys : (Fin 3 → ℤ) → ℝ → Fin 3 → ℝ)
      (lab : (Fin 3 → ℤ) → ℝ → Fin 2 → ℤ) (center : ℝ → Fin 3 → ℝ)
      (Lc : (Fin 3 → ℤ) → Finset (Fin 2 → ℤ)) (ε R Λ Hp K₀ : ℝ),
      0 < ε → 0 ≤ R → 1 ≤ Λ → 0 ≤ Hp → 1 ≤ K₀ →
      (∀ q, ((Lc q).card : ℝ) ≤ Λ) →
      (∀ q ∈ Q, ∀ e, (Pn q e).natDegree ≤ M ∧ ∀ k, |(Pn q e).coeff k| ≤ Hp) →
      (∀ q ∈ Q, MeasurableSet (Tw q) ∧ Tw q ⊆ Icc (0 : ℝ) 1 ∧
        ENNReal.ofReal K₀⁻¹ ≤ volume (Tw q)) →
      (∀ q ∈ Q, ∀ τ ∈ Tw q, lab q τ ∈ Lc (fun j => ⌊phys q τ j / ε⌋)) →
      (∀ q ∈ Q, ∀ τ ∈ Tw q, ∀ e, |(Pn q e).eval τ - ε * (lab q τ e : ℝ)| ≤ 2 * ε) →
      (∀ q ∈ Q, ∀ τ ∈ Tw q, ∀ j, |phys q τ j - center τ j| ≤ R * ε) →
      ∃ S : Finset (Fin 2 → Fin (M + 1) → ℤ),
        (∀ q ∈ Q, polyBins M ε (Pn q) ∈ S) ∧
        (S.card : ℝ) ≤ (C * (max K₀ ((4 * R + 11) ^ 3 * Λ + 2)) ^
          (3 * (M + 1) + (M + 1) ^ 2 * M)) ^ 2 := by
  classical
  obtain ⟨C, hC, hbin⟩ := Cart.exists_original_polynomial_bin_power_constant M
  refine ⟨C, hC, ?_⟩
  intro Q Pn Tw phys lab center Lc ε R Λ Hp K₀ hε hR hΛ hHp hK₀ hLc hPn hTw hknown hfit hnear
  -- the local field palettes along the fiber
  obtain ⟨F, hFcard, hFmem⟩ := Cart.exists_neighborhood_field_palettes 3
    {x : (Fin 3 → ℤ) × ℝ | x.1 ∈ Q ∧ x.2 ∈ Tw x.1} (fun x => x.2) (fun x => phys x.1 x.2)
    center (fun x => lab x.1 x.2) ε R Λ hε hR (by linarith) Lc hLc
    (fun x hx => hknown x.1 hx.1 x.2 hx.2) (fun x hx j => hnear x.1 hx.1 x.2 hx.2 j)
  set K : ℝ := max K₀ ((4 * R + 11) ^ 3 * Λ + 2) with hK
  have hK1 : 1 ≤ K := le_max_of_le_left hK₀
  -- all bins of the fiber form a finite set
  have hbox : ∀ q ∈ Q, polyBins M ε (Pn q) ∈
      (Fintype.piFinset fun _ : Fin 2 => Fintype.piFinset fun _ : Fin (M + 1) =>
        Finset.Icc ⌊-Hp / ε⌋ ⌊Hp / ε⌋) := by
    intro q hq
    rw [Fintype.mem_piFinset]
    intro e
    rw [Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_Icc]
    have hc := (hPn q hq e).2 k
    constructor
    · apply Int.floor_mono
      rw [div_le_div_iff_of_pos_right hε]
      exact (neg_le_of_abs_le hc)
    · apply Int.floor_mono
      rw [div_le_div_iff_of_pos_right hε]
      exact (le_of_abs_le hc)
  set S : Finset (Fin 2 → Fin (M + 1) → ℤ) :=
    (Fintype.piFinset fun _ : Fin 2 => Fintype.piFinset fun _ : Fin (M + 1) =>
        Finset.Icc ⌊-Hp / ε⌋ ⌊Hp / ε⌋).filter (fun c => ∃ q ∈ Q, polyBins M ε (Pn q) = c)
    with hS
  have hSmem : ∀ q ∈ Q, polyBins M ε (Pn q) ∈ S := by
    intro q hq
    rw [hS, Finset.mem_filter]
    exact ⟨hbox q hq, q, hq, rfl⟩
  -- one component at a time
  have hcomp : ∀ e : Fin 2, (((S.image fun c => c e).card : ℝ)) ≤
      C * K ^ (3 * (M + 1) + (M + 1) ^ 2 * M) := by
    intro e
    set Se := S.image fun c => c e with hSe
    -- a representative state for every component bin
    have hrep : ∀ c ∈ Se, ∃ q ∈ Q, polyBins M ε (Pn q) e = c := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
      rw [hS, Finset.mem_filter] at hc'
      obtain ⟨q, hq, hqc⟩ := hc'.2
      exact ⟨q, hq, by rw [hqc]⟩
    choose! rep hrepQ hrepbin using hrep
    have hcount := hbin K ε hK1 hε Se (fun c => Pn (rep c) e)
      (fun c hc => (hPn (rep c) (hrepQ c hc) e).1)
      (fun c hc k => by
        have := congrFun (hrepbin c hc) k
        simpa [polyBins] using this)
      (fun c => Tw (rep c))
      (fun c hc => (hTw (rep c) (hrepQ c hc)).1)
      (fun c hc => (hTw (rep c) (hrepQ c hc)).2.1)
      (fun c hc => by
        have h := (hTw (rep c) (hrepQ c hc)).2.2
        exact (ENNReal.ofReal_le_ofReal (inv_anti₀ (by linarith) (le_max_left _ _))).trans h)
      (fun τ => (F τ).image fun w => w e)
      (fun τ _ => by
        have h1 : (((F τ).image fun w => w e).card : ℝ) ≤ (F τ).card := by
          exact_mod_cast Finset.card_image_le
        exact h1.trans ((hFcard τ).trans (by
          have : (4 * R + 11) ^ 3 * Λ ≤ K := (by linarith : (4 * R + 11) ^ 3 * Λ ≤
            (4 * R + 11) ^ 3 * Λ + 2).trans (le_max_right _ _)
          exact this)))
      (fun c hc τ hτ => by
        refine ⟨lab (rep c) τ e, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨lab (rep c) τ, hFmem ⟨rep c, τ⟩ ⟨hrepQ c hc, hτ⟩, rfl⟩
        · have h := hfit (rep c) (hrepQ c hc) τ hτ e
          have h2 : 2 * ε ≤ K * ε := by
            have : (2 : ℝ) ≤ K := (by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 4 * R + 11) 3] :
              (2 : ℝ) ≤ (4 * R + 11) ^ 3 * Λ + 2).trans (le_max_right _ _)
            nlinarith
          exact h.trans h2)
    exact hcount
  refine ⟨S, hSmem, ?_⟩
  have h := card_le_card_proj_mul S
  have h0 := hcomp 0
  have h1 := hcomp 1
  calc (S.card : ℝ) ≤ _ := h
    _ ≤ (C * K ^ (3 * (M + 1) + (M + 1) ^ 2 * M)) * (C * K ^ (3 * (M + 1) + (M + 1) ^ 2 * M)) :=
        mul_le_mul h0 h1 (by positivity) (by positivity)
    _ = _ := by rw [sq, mul_pow]; ring

end Submission.Obl.k4_scalar_grid_cartesian_field
