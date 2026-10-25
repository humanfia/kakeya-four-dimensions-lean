import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.FrameBasics
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.PoolBasics

/-!
# Deep original labels split by native-signal groups

Adapted from accepted o248 (`k4_wide_velocity_lists_scalar_preparation/Pool.lean`).
In the horizontal model a deep true label has small four-coordinate diameter. Here
the three base coordinates of a deep label are confined by the true assignment
geometry at the deep depth, and the native signal is confined by
`Parent.DeepConfinement`, which splits every deep label into two groups after
deleting a small bad frame set. The pooling pieces are therefore the deep label
regions intersected with one group.
-/

set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_wide_velocity_lists_scalar_preparation
  (floor_div_near stateBox card_stateBox mem_stateBox dyadic_Ico_disjoint dyadic_parent_eq
    quadratic_background_variation)

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- The original horizontal velocity bin at mesh `N^(-m)`. -/
def velBin (p : Parent α) (k : ℕ) (m : ℝ) (ω : α × ℝ) : ℤ :=
  ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋

/-- Two times of one dyadic block differ by at most its length. -/
theorem block_sub_le {T : ℕ} {j : Fin (2 ^ T)} {τ τ' : ℝ}
    (hτ : τ ∈ block T j) (hτ' : τ' ∈ block T j) :
    |τ - τ'| ≤ ((2 : ℝ) ^ T)⁻¹ := by
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  have hlen : (((j : ℕ) : ℝ) + 1) / 2 ^ T - ((j : ℕ) : ℝ) / 2 ^ T = ((2 : ℝ) ^ T)⁻¹ := by
    field_simp
    ring
  have h1 : ((j : ℕ) : ℝ) / 2 ^ T ≤ τ ∧ τ ≤ (((j : ℕ) : ℝ) + 1) / 2 ^ T := hτ
  have h2 : ((j : ℕ) : ℝ) / 2 ^ T ≤ τ' ∧ τ' ≤ (((j : ℕ) : ℝ) + 1) / 2 ^ T := hτ'
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private theorem abs_three_le {A B C a b c : ℝ} (hA : |A| ≤ a) (hB : |B| ≤ b)
    (hC : |C| ≤ c) : |A - B + C| ≤ a + b + c := by
  rw [abs_le] at hA hB hC ⊢
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]

private theorem abs_four_le {A B C E a b c e : ℝ} (hA : |A| ≤ a) (hB : |B| ≤ b)
    (hC : |C| ≤ c) (hE : |E| ≤ e) : |A - B + C + E| ≤ a + b + c + e := by
  rw [abs_le] at hA hB hC hE ⊢
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2, hE.1, hE.2]

/-- The true assignment geometry confines the original base of a deep label:
its three base coordinates vary by at most `6 K^2` block lengths. -/
theorem AtDepth.base_diameter {k : ℕ} {s R : ℝ} (hat : p.AtDepth k s R)
    (hN : 1 ≤ p.N k) (hK : 1 ≤ p.K k) (hℓ : 0 < p.ℓ) (hs : 0 ≤ s)
    (i : Fin (p.n k s)) {l l' : α} (hl : l ∈ p.A k s i) (hl' : l' ∈ p.A k s i)
    {τ τ' : ℝ} (hτ : τ ∈ block (p.T k s) (p.j k s i))
    (hτ' : τ' ∈ block (p.T k s) (p.j k s i)) (e : Fin 3) :
    |p.base k l τ e - p.base k l' τ' e| ≤ 6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k s)⁻¹ := by
  have hq0 : 0 < ((2 : ℝ) ^ p.T k s)⁻¹ := by positivity
  have hg1 : p.N k ^ (-p.ℓ * s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
  have hg0 : 0 ≤ p.N k ^ (-p.ℓ * s) := Real.rpow_nonneg (by linarith) _
  have hK0 : 0 ≤ p.K k := by linarith
  have hrow := hat.2.2.2.2.1 i
  have hc := hrow.2.2.2.1
  have hgeo := hrow.2.2.2.2.2.1 l hl τ hτ
  have hgeo' := hrow.2.2.2.2.2.1 l' hl' τ' hτ'
  simp only [zpow_neg, zpow_natCast] at hgeo hgeo'
  set q : ℝ := ((2 : ℝ) ^ p.T k s)⁻¹ with hq
  have hdt : |τ - τ'| ≤ q := block_sub_le hτ hτ'
  have hKK : p.K k ≤ p.K k ^ 2 := by nlinarith
  have hKq : p.K k * q ≤ p.K k ^ 2 * q := mul_le_mul_of_nonneg_right hKK hq0.le
  have hqg : p.K k * q * p.N k ^ (-p.ℓ * s) ≤ p.K k * q := by
    have := mul_le_mul_of_nonneg_left hg1 (mul_nonneg hK0 hq0.le)
    linarith
  have hprod (a : ℝ) (ha : |a| ≤ p.K k) : |(τ - τ') * a| ≤ p.K k * q := by
    rw [abs_mul]
    calc |τ - τ'| * |a| ≤ q * p.K k := mul_le_mul hdt ha (abs_nonneg _) hq0.le
      _ = p.K k * q := by ring
  have h1 : |p.x k l τ 1 - p.x k l' τ' 1| ≤ 3 * (p.K k * q) := by
    have e1 : p.x k l τ 1 - p.x k l' τ' 1 =
        (p.x k l τ 1 - p.c k s i 0 - τ * p.c k s i 1) -
          (p.x k l' τ' 1 - p.c k s i 0 - τ' * p.c k s i 1) + (τ - τ') * p.c k s i 1 := by
      ring
    rw [e1]
    have := abs_three_le hgeo.1 hgeo'.1 (hprod _ (hc 1))
    linarith
  have h2 : |p.x k l τ 2 - p.x k l' τ' 2| ≤ 6 * p.K k ^ 2 * q := by
    have e2 : p.x k l τ 2 - p.x k l' τ' 2 =
        (p.x k l τ 2 - p.c k s i 2 - τ * p.c k s i 3 - p.c k s i 4 * p.x k l τ 1) -
          (p.x k l' τ' 2 - p.c k s i 2 - τ' * p.c k s i 3 - p.c k s i 4 * p.x k l' τ' 1) +
          (τ - τ') * p.c k s i 3 + p.c k s i 4 * (p.x k l τ 1 - p.x k l' τ' 1) := by
      ring
    rw [e2]
    have h4 : |p.c k s i 4 * (p.x k l τ 1 - p.x k l' τ' 1)| ≤ p.K k * (3 * (p.K k * q)) := by
      rw [abs_mul]
      exact mul_le_mul (hc 4) h1 (abs_nonneg _) hK0
    have := abs_four_le hgeo.2.1 hgeo'.2.1 (hprod _ (hc 3)) h4
    nlinarith
  have hq6 : q ≤ 6 * p.K k ^ 2 * q := by nlinarith
  fin_cases e
  · change |τ - τ'| ≤ 6 * p.K k ^ 2 * q
    exact hdt.trans hq6
  · change |p.x k l τ 1 - p.x k l' τ' 1| ≤ 6 * p.K k ^ 2 * q
    linarith
  · change |p.x k l τ 2 - p.x k l' τ' 2| ≤ 6 * p.K k ^ 2 * q
    exact h2

namespace ListFrame

variable {k : ℕ} {r v m ε : ℝ} (f : p.ListFrame k r v m ε)

/-- The region of a deep original true label, in normalized block time and
with the half-open time piece of its label. -/
def region (s : ℝ) (i : Fin (p.n k s)) : Set (α × ℝ) :=
  {ω | ω.1 ∈ p.B k s i ∧ f.t₀ + f.q * ω.2 ∈
    Ico (((p.j k s i : ℕ) : ℝ) / 2 ^ p.T k s)
      ((((p.j k s i : ℕ) : ℝ) + 1) / 2 ^ p.T k s)}

/-- Events on good trajectories before the end of the block, with bounded
base coordinates; almost every frame event is of this kind. -/
def goodSet : Set (α × ℝ) :=
  {ω | ω.1 ∈ f.good ∧ ω.2 ∈ Ico (0 : ℝ) 1 ∧
    ∀ e : Fin 3, |p.base k ω.1 (f.t₀ + f.q * ω.2) e| ≤ 2 * p.K k}

/-- The output state: scalar base cell and residual scalar bin. -/
def outState (ω : α × ℝ) : (Fin 2 → ℤ) × ℤ :=
  (scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)),
    ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-r - v)⌋)

/-- A pooling piece: a deep label region inside one signal group. -/
def piece (s : ℝ) (grp : α × ℝ → Fin 2) (x : Fin (p.n k s) × Fin 2) : Set (α × ℝ) :=
  f.region s x.1 ∩ grp ⁻¹' {x.2}

/-- The listed output states of a piece: one step around any of its good events
outside the bad set, and none when it has none. -/
def pieceOptions (s : ℝ) (grp : α × ℝ → Fin 2) (bad : Set (α × ℝ))
    (x : Fin (p.n k s) × Fin 2) : Finset ((Fin 2 → ℤ) × ℤ) := by
  classical
  exact if hx : ∃ ω, ω ∈ f.piece s grp x ∧ ω ∈ f.goodSet ∧ ω ∉ bad then
    stateBox (f.outState (Classical.choose hx)) else ∅

theorem pieceOptions_card_le (s : ℝ) (grp : α × ℝ → Fin 2) (bad : Set (α × ℝ))
    (x : Fin (p.n k s) × Fin 2) :
    (f.pieceOptions s grp bad x).card ≤ 27 ∧
      ((f.pieceOptions s grp bad x).Nonempty →
        ∃ ω, ω ∈ f.region s x.1 ∧ ω ∈ f.goodSet) := by
  classical
  by_cases hx : ∃ ω, ω ∈ f.piece s grp x ∧ ω ∈ f.goodSet ∧ ω ∉ bad
  · have heq : f.pieceOptions s grp bad x = stateBox (f.outState (Classical.choose hx)) := by
      simp only [pieceOptions, hx, ↓reduceDIte]
    rw [heq, card_stateBox]
    refine ⟨le_rfl, fun _ => ?_⟩
    obtain ⟨ω, hω, hG, -⟩ := hx
    exact ⟨ω, hω.1, hG⟩
  · have heq : f.pieceOptions s grp bad x = ∅ := by
      simp only [pieceOptions, hx, ↓reduceDIte]
    rw [heq]
    exact ⟨by simp, fun h => absurd h Finset.not_nonempty_empty⟩

/-- A deep label meets only one step of output states inside one signal group:
the three base coordinates are confined by the deep true geometry and the native
signal by the deep confinement. -/
theorem outState_mem_stateBox {s : ℝ} (hK : 1 ≤ p.K k) (hNpos : 0 < p.N k)
    {D : ℝ} (hD0 : 0 ≤ D)
    (hdiam : ∀ i : Fin (p.n k s), ∀ l ∈ p.B k s i, ∀ l' ∈ p.B k s i,
      ∀ τ ∈ block (p.T k s) (p.j k s i), ∀ τ' ∈ block (p.T k s) (p.j k s i),
      ∀ e : Fin 3, |p.base k l τ e - p.base k l' τ' e| ≤ D)
    (hN2 : 2 * D * (p.N k ^ (m / 10)) ^ 2 ≤ p.N k ^ (-m))
    (hN3 : 216 * p.N k ^ (m / 10) * (2 * p.K k) ^ 2 * D ≤ p.N k ^ (-(r + v)) / 2)
    (hN4 : D ≤ 1)
    {i : Fin (p.n k s)} {ω ω₀ : α × ℝ}
    (hω : ω ∈ f.region s i) (hωG : ω ∈ f.goodSet)
    (hω₀ : ω₀ ∈ f.region s i) (hω₀G : ω₀ ∈ f.goodSet)
    (hsig : |p.signal k ω.1 (f.t₀ + f.q * ω.2) - p.signal k ω₀.1 (f.t₀ + f.q * ω₀.2)| ≤
      p.N k ^ (-(r + v)) / 2) :
    f.outState ω ∈ stateBox (f.outState ω₀) := by
  set H := p.N k ^ (m / 10) with hHdef
  set t := f.t₀ + f.q * ω.2 with ht
  set t' := f.t₀ + f.q * ω₀.2 with ht'
  have hq := f.q_pos
  have hqi : 0 < f.q⁻¹ := inv_pos.mpr hq
  obtain ⟨hqinv, hzv⟩ := f.frame_component_bounds
  have hH1 : 1 ≤ H := ((one_le_inv₀ hq).mpr f.q_le_one).trans hqinv
  have hH0 : 0 ≤ H := by linarith
  have hIt : t ∈ block (p.T k s) (p.j k s i) := Ico_subset_Icc_self hω.2
  have hIt' : t' ∈ block (p.T k s) (p.j k s i) := Ico_subset_Icc_self hω₀.2
  have hx := fun e => hdiam i ω.1 hω.1 ω₀.1 hω₀.1 t hIt t' hIt' e
  have hdt : |t - t'| ≤ D := hx 0
  have hdx : |p.x k ω.1 t 1 - p.x k ω₀.1 t' 1| ≤ D := hx 1
  have hDH : D * H ≤ D * H ^ 2 := by
    have := mul_le_mul_of_nonneg_left hH1 (mul_nonneg hD0 hH0)
    nlinarith
  have hDH2 : D * H ^ 2 ≤ 2 * D * H ^ 2 := by nlinarith [sq_nonneg H]
  -- normalized time
  have hu : |ω.2 - ω₀.2| ≤ p.N k ^ (-m) := by
    have he : ω.2 - ω₀.2 = (t - t') * f.q⁻¹ := by
      rw [ht, ht']; field_simp; ring
    rw [he, abs_mul, abs_of_pos hqi]
    calc |t - t'| * f.q⁻¹ ≤ D * H := mul_le_mul hdt hqinv hqi.le hD0
      _ ≤ _ := hDH.trans (hDH2.trans hN2)
  -- normalized horizontal coordinate
  have hY : |scalarY (f.coeff ω.1) ω.2 - scalarY (f.coeff ω₀.1) ω₀.2| ≤ p.N k ^ (-m) := by
    rw [f.scalarY_eq ω.1 hωG.1 ω.2, f.scalarY_eq ω₀.1 hω₀G.1 ω₀.2]
    have he : (p.x k ω.1 t 1 - f.z₀ - f.zv * t) / f.q -
        (p.x k ω₀.1 t' 1 - f.z₀ - f.zv * t') / f.q =
        ((p.x k ω.1 t 1 - p.x k ω₀.1 t' 1) - f.zv * (t - t')) * f.q⁻¹ := by
      field_simp; ring
    rw [he, abs_mul, abs_of_pos hqi]
    have hnum : |(p.x k ω.1 t 1 - p.x k ω₀.1 t' 1) - f.zv * (t - t')| ≤ D + H * D := by
      calc _ ≤ |p.x k ω.1 t 1 - p.x k ω₀.1 t' 1| + |f.zv * (t - t')| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul]
          exact add_le_add hdx (mul_le_mul hzv hdt (abs_nonneg _) hH0)
    calc _ ≤ (D + H * D) * H := mul_le_mul hnum hqinv hqi.le (by positivity)
      _ = D * H + D * H ^ 2 := by ring
      _ ≤ 2 * D * H ^ 2 := by linarith
      _ ≤ _ := hN2
  -- residual scalar
  have hX : |scalarX (f.coeff ω.1) ω.2 - scalarX (f.coeff ω₀.1) ω₀.2| ≤
      p.N k ^ (-r - v) := by
    rw [f.scalarX_eq ω.1 hωG.1 ω.2, f.scalarX_eq ω₀.1 hω₀G.1 ω₀.2]
    have hbg := quadratic_background_variation f.background f.background_degree
      (M := H) (R := 2 * p.K k) (δ := D) f.background_coeff_bound (by linarith)
      hD0 hN4 (p.base k ω₀.1 t') (p.base k ω.1 t) hω₀G.2.2 (fun e => hx e)
    have hexp : p.N k ^ (-r - v) = p.N k ^ (-(r + v)) := by congr 1; ring
    rw [hexp]
    calc _ ≤ |p.signal k ω.1 t - p.signal k ω₀.1 t'| +
          |MvPolynomial.eval (p.base k ω.1 t) f.background -
            MvPolynomial.eval (p.base k ω₀.1 t') f.background| := by
          have := abs_sub (p.signal k ω.1 t - p.signal k ω₀.1 t')
            (MvPolynomial.eval (p.base k ω.1 t) f.background -
              MvPolynomial.eval (p.base k ω₀.1 t') f.background)
          convert this using 2
          ring
      _ ≤ p.N k ^ (-(r + v)) / 2 + 216 * H * (2 * p.K k) ^ 2 * D := add_le_add hsig hbg
      _ ≤ p.N k ^ (-(r + v)) / 2 + p.N k ^ (-(r + v)) / 2 := add_le_add le_rfl hN3
      _ = _ := by ring
  have hσm : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hNpos _
  have hσr : 0 < p.N k ^ (-r - v) := Real.rpow_pos_of_pos hNpos _
  apply mem_stateBox
  · intro e
    fin_cases e
    · simpa [outState, scalarCell, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCell]
        using floor_div_near hσm hu
    · simpa [outState, scalarCell, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCell]
        using floor_div_near hσm hY
  · simpa [outState] using floor_div_near hσr hX

/-- A deep label with a good event descends from the frame's parent. -/
theorem descends {s : ℝ}
    (hAr : ∀ i i', i ≠ i' → p.j k r i = p.j k r i' →
      Disjoint (p.A k r i) (p.A k r i'))
    (hBAr : ∀ i, p.B k r i ⊆ p.A k r i) (hBAs : ∀ i, p.B k s i ⊆ p.A k s i)
    (hnest : ∀ i : Fin (p.n k s), ∃ h : Fin (p.n k r), p.A k s i ⊆ p.A k r h ∧
      block (p.T k s) (p.j k s i) ⊆ block (p.T k r) (p.j k r h))
    {i : Fin (p.n k s)} {ω : α × ℝ} (hω : ω ∈ f.region s i) (hωG : ω ∈ f.goodSet) :
    p.A k s i ⊆ p.A k r f.parent ∧
      block (p.T k s) (p.j k s i) ⊆ Icc f.t₀ (f.t₀ + f.q) := by
  obtain ⟨h, hA, hI⟩ := hnest i
  have hlh : ω.1 ∈ p.A k r h := hA (hBAs i hω.1)
  have hlp : ω.1 ∈ p.A k r f.parent := hBAr _ (f.good_subset hωG.1)
  have hhp : h = f.parent := by
    by_cases hj : p.j k r h = p.j k r f.parent
    · by_contra hne
      exact Set.disjoint_left.mp (hAr h f.parent hne hj) hlh hlp
    · exfalso
      apply hj
      apply Fin.ext
      have hu := hωG.2.1
      have hq := f.q_pos
      exact dyadic_parent_eq f.time_eq hq
        (by nlinarith [hu.1]) (by nlinarith [hu.2]) hω.2 hI
  subst hhp
  exact ⟨hA, f.time_eq ▸ hI⟩

/-- The deep reference weights of labels with good events sum to at most `K`,
measured against the original parent reference. -/
theorem deep_weight_budget {s : ℝ}
    (hAr : ∀ i i', i ≠ i' → p.j k r i = p.j k r i' →
      Disjoint (p.A k r i) (p.A k r i'))
    (hBAr : ∀ i, p.B k r i ⊆ p.A k r i) (hBAs : ∀ i, p.B k s i ⊆ p.A k s i)
    (hmeasA : ∀ i, MeasurableSet (p.A k s i))
    (hdisjs : ∀ i i', i ≠ i' → p.j k s i = p.j k s i' →
      Disjoint (p.A k s i) (p.A k s i'))
    (hnest : ∀ i : Fin (p.n k s), ∃ h : Fin (p.n k r), p.A k s i ⊆ p.A k r h ∧
      block (p.T k s) (p.j k s i) ⊆ block (p.T k r) (p.j k r h))
    (hK : 0 ≤ p.K k) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤)
    (S : Finset (Fin (p.n k s)))
    (hS : ∀ i ∈ S, ∃ ω, ω ∈ f.region s i ∧ ω ∈ f.goodSet) :
    ∑ i ∈ S, f.weight⁻¹ * ENNReal.ofReal (p.K k * ((2 : ℝ) ^ p.T k s)⁻¹) *
      p.ν k (p.A k s i) ≤ ENNReal.ofReal (p.K k) := by
  set q' : ℝ := ((2 : ℝ) ^ p.T k s)⁻¹ with hq'
  have hT : (0 : ℝ) < 2 ^ p.T k s := by positivity
  let piece : Fin (p.n k s) → Set (α × ℝ) := fun i =>
    p.A k s i ×ˢ Ico (((p.j k s i : ℕ) : ℝ) / 2 ^ p.T k s)
      ((((p.j k s i : ℕ) : ℝ) + 1) / 2 ^ p.T k s)
  have hpiece : ∀ i, (p.ν k).prod volume (piece i) =
      ENNReal.ofReal q' * p.ν k (p.A k s i) := by
    intro i
    simp only [piece]
    rw [Measure.prod_prod, Real.volume_Ico, mul_comm]
    congr 2
    rw [hq']; field_simp; ring
  have hdisjS : (S : Set (Fin (p.n k s))).PairwiseDisjoint piece := by
    intro i _ i' _ hii'
    simp only [Function.onFun, piece]
    by_cases hj : p.j k s i = p.j k s i'
    · exact Set.disjoint_prod.mpr (Or.inl (hdisjs i i' hii' hj))
    · exact Set.disjoint_prod.mpr (Or.inr (dyadic_Ico_disjoint
        (fun h => hj (Fin.ext h))))
  have hsub : (⋃ i ∈ S, piece i) ⊆ p.A k r f.parent ×ˢ Icc f.t₀ (f.t₀ + f.q) := by
    intro x hx
    obtain ⟨i, hiS, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨ω, hω, hωG⟩ := hS i hiS
    obtain ⟨hA, hI⟩ := f.descends hAr hBAr hBAs hnest hω hωG
    exact ⟨hA hxi.1, hI (Ico_subset_Icc_self hxi.2)⟩
  have hsum : ∑ i ∈ S, (p.ν k).prod volume (piece i) ≤ f.weight := by
    rw [← measure_biUnion_finset hdisjS (fun i _ => (hmeasA i).prod measurableSet_Ico)]
    calc _ ≤ (p.ν k).prod volume (p.A k r f.parent ×ˢ Icc f.t₀ (f.t₀ + f.q)) :=
          measure_mono hsub
      _ = f.weight := by
          rw [Measure.prod_prod, Real.volume_Icc, weight, mul_comm]
          congr 2
          ring
  calc _ = f.weight⁻¹ * ENNReal.ofReal (p.K k) *
        ∑ i ∈ S, (p.ν k).prod volume (piece i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hpiece, ENNReal.ofReal_mul hK]
        ring
    _ ≤ f.weight⁻¹ * ENNReal.ofReal (p.K k) * f.weight := by gcongr
    _ = ENNReal.ofReal (p.K k) := by
        rw [mul_comm (f.weight⁻¹), mul_assoc, ENNReal.inv_mul_cancel h0 ht, mul_one]

theorem measurable_outState : Measurable f.outState := by
  have hc : ∀ e, Measurable (fun ω : α × ℝ => f.coeff ω.1 e) := fun e =>
    (measurable_pi_apply e).comp (f.coeff_measurable.comp measurable_fst)
  have hY : Measurable (fun ω : α × ℝ => scalarY (f.coeff ω.1) ω.2) := by
    simp only [scalarY, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarY]
    exact (hc 0).add (measurable_snd.mul (hc 1))
  have hX : Measurable (fun ω : α × ℝ => scalarX (f.coeff ω.1) ω.2) := by
    simp only [scalarX, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarX]
    exact ((hc 2).add (measurable_snd.mul (hc 3))).add ((measurable_snd.pow_const 2).mul (hc 4))
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro e
    fin_cases e
    · simpa [scalarCell, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCell] using
        (measurable_snd.div_const _).floor
    · simpa [scalarCell, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCell] using
        (hY.div_const _).floor
  · exact (hX.div_const _).floor

theorem measurableSet_region {s : ℝ} (hB : ∀ i, MeasurableSet (p.B k s i))
    (i : Fin (p.n k s)) : MeasurableSet (f.region s i) :=
  ((hB i).preimage measurable_fst).inter
    (measurableSet_Ico.preimage (measurable_const.add (measurable_const.mul measurable_snd)))

theorem region_disjoint {s : ℝ} (hBA : ∀ i, p.B k s i ⊆ p.A k s i)
    (hdisj : ∀ i i', i ≠ i' → p.j k s i = p.j k s i' →
      Disjoint (p.A k s i) (p.A k s i')) :
    Pairwise (fun i i' => Disjoint (f.region s i) (f.region s i')) := by
  intro i i' hii'
  rw [Set.disjoint_left]
  intro ω hω hω'
  by_cases hj : p.j k s i = p.j k s i'
  · exact Set.disjoint_left.mp (hdisj i i' hii' hj) (hBA i hω.1) (hBA i' hω'.1)
  · exact Set.disjoint_left.mp (dyadic_Ico_disjoint (fun h => hj (Fin.ext h))) hω.2 hω'.2

theorem measurableSet_piece {s : ℝ} (hB : ∀ i, MeasurableSet (p.B k s i))
    {grp : α × ℝ → Fin 2} (hgrp : Measurable grp) (x : Fin (p.n k s) × Fin 2) :
    MeasurableSet (f.piece s grp x) :=
  (f.measurableSet_region hB x.1).inter (hgrp (measurableSet_singleton x.2))

theorem piece_disjoint {s : ℝ} (hBA : ∀ i, p.B k s i ⊆ p.A k s i)
    (hdisj : ∀ i i', i ≠ i' → p.j k s i = p.j k s i' →
      Disjoint (p.A k s i) (p.A k s i'))
    (grp : α × ℝ → Fin 2) :
    Pairwise (fun x x' => Disjoint (f.piece s grp x) (f.piece s grp x')) := by
  intro x x' hxx'
  rw [Set.disjoint_left]
  intro ω hω hω'
  by_cases hi : x.1 = x'.1
  · have hg : x.2 ≠ x'.2 := fun hg => hxx' (Prod.ext hi hg)
    have h1 : grp ω = x.2 := hω.2
    have h2 : grp ω = x'.2 := hω'.2
    exact hg (h1.symm.trans h2)
  · exact Set.disjoint_left.mp (f.region_disjoint hBA hdisj hi) hω.1 hω'.1

end ListFrame

end Parent

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
