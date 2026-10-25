/-
The finite original-resolution guard.

Adapted from this LOT tree (g-oai-074), obligation o134
`k4_scalar_guarded_tangent_obstruction`, branch x0438 (session x0438, own code of this
tree), files `.../Relax.lean`, `.../Exclusion.lean` and `.../FiniteGuard.lean`, renamed
into this namespace. Here the chart calculus is an explicit hypothesis `Split.Calculus`
(it is the theorem of o131), and the extremal class bound is an explicit hypothesis, so
that the guard applies to any genuine exact parent in the critical class.
-/
import Submission.Obl.k4_scalar_guarded_tangent_preparation.Interface

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers
open Filter
open scoped Topology

theorem exact_N_ge_two {p : Code} (hp : Split.Exact p) (k : ℕ) : 2 ≤ p.N k :=
  hp.1.1 k

theorem exact_N_ge_one {p : Code} (hp : Split.Exact p) (k : ℕ) : 1 ≤ p.N k := by
  linarith [exact_N_ge_two hp k]

theorem exact_N_gt_one {p : Code} (hp : Split.Exact p) (k : ℕ) : 1 < p.N k := by
  linarith [exact_N_ge_two hp k]

theorem exact_length_pos {p : Code} (hp : Split.Exact p) : 0 < p.L :=
  hp.1.2.2.2.2.2.1

theorem exact_cap_nonneg {p : Code} (hp : Split.Exact p) : 0 ≤ p.d :=
  hp.1.2.2.2.2.2.2.1

theorem exact_cap_lt_one {p : Code} (hp : Split.Exact p) : p.d < 1 :=
  hp.1.2.2.2.2.2.2.2.1

theorem exact_terminal_cap {p : Code} (hp : Split.Exact p) {s : ℝ}
    (hs : 0 ≤ s) (hsL : s ≤ p.L) :
    p.profile p.L - p.profile s ≤ p.d * (p.L - s) :=
  hp.2.2.2.2.2.2.1 s hs hsL

/-- False-flag chart data are monotone in depth, time and slack. -/
theorem ChartData.relax_false {p : Code} {B k T n : ℕ}
    {r r' b h h' ε ε' : ℝ}
    {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Coeff} {C : Fin n → Set Incidence}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hN : 1 ≤ p.N k) (hr : r' ≤ r) (hh : h ≤ h') (hε : ε ≤ ε')
    (hc : Split.ChartData p B r b h ε false k T n γ j A C u v J P Λ) :
    Split.ChartData p B r' b h' ε' false k T n γ j A C u v J P Λ := by
  obtain ⟨hT, hn, hmeas, hdisj, hsubset, hcharts, hcard, hmlist, hknown, hmass⟩ := hc
  have hεpow : p.N k ^ ε ≤ p.N k ^ ε' := Real.rpow_le_rpow_of_exponent_le hN hε
  have hrpow : p.N k ^ (-r) ≤ p.N k ^ (-r') :=
    Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hr)
  have hNpos : 0 < p.N k := lt_of_lt_of_le zero_lt_one hN
  refine ⟨hT.trans (Real.rpow_le_rpow_of_exponent_le hN hh), hn, hmeas, hdisj,
    hsubset, ?_, ?_, hmlist, hknown, ?_⟩
  · intro i
    obtain ⟨hmpos, hJpos, hJinv, hJub, huv, hdeg, hcoeff, hcoord,
      hFA, hFC, happrox, _⟩ := hcharts i
    refine ⟨hmpos, hJpos, hJinv,
      hJub.trans (div_le_div_of_nonneg_right hεpow (by positivity)),
      huv.trans hεpow, hdeg, hcoeff, ?_, hFA, hFC, ?_, ?_⟩
    · intro l hl
      exact ⟨(hcoord l hl).1, fun e => ((hcoord l hl).2 e).trans hεpow⟩
    · intro l hl t ht
      obtain ⟨hy, hx⟩ := happrox l hl t ht
      refine ⟨hy.trans (mul_le_mul_of_nonneg_right hεpow hJpos.le), hx.trans ?_⟩
      exact mul_le_mul hεpow hrpow (Real.rpow_nonneg hNpos.le _)
        (Real.rpow_nonneg hNpos.le _)
    · intro hfalse
      cases hfalse
  · intro a z
    exact (hcard a z).trans hεpow
  · exact (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hε))).trans hmass

/-- False-flag charts are monotone in depth, time and slack. -/
theorem Chart.relax_false {p : Code} {B k : ℕ} {r r' b h h' ε ε' : ℝ}
    (hN : 1 ≤ p.N k) (hr : r' ≤ r) (hh : h ≤ h') (hε : ε ≤ ε')
    (hc : Split.Chart p B r b h ε false k) : Split.Chart p B r' b h' ε' false k := by
  obtain ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hc⟩ := hc
  exact ⟨T, n, γ, j, A, C, u, v, J, P, Λ, ChartData.relax_false hN hr hh hε hc⟩

/-- Charts have nonnegative time exponent. -/
theorem Chart.time_nonneg {p : Code} {B k : ℕ} {r b h ε : ℝ}
    {truth : Bool} (hN : 1 < p.N k) (hc : Split.Chart p B r b h ε truth k) : 0 ≤ h := by
  obtain ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hc⟩ := hc
  have hT : (2 : ℝ) ^ T ≤ p.N k ^ h := hc.1
  have hone : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  by_contra hh
  have hlt : p.N k ^ h < 1 :=
    (Real.rpow_lt_one_iff_of_pos (by linarith)).2 (Or.inl ⟨hN, lt_of_not_ge hh⟩)
  linarith

/-- If a fixed atlas cost is not available, one fixed positive tolerance
already excludes that cost at every sufficiently late original sample. -/
theorem eventually_not_chart_of_not_known {p : Code} (hp : Split.Exact p)
    {r b h : ℝ} (hnot : ¬Split.Known p r b h) (B : ℕ) (hB : 1 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, ¬Split.Chart p B r b h ε false k := by
  by_cases hh : 0 ≤ h
  · by_contra! hbad
    apply hnot
    refine ⟨hh, B, hB, ?_⟩
    intro ε hε
    exact (hbad ε hε).mono fun k hk => Chart.relax_false
      (exact_N_ge_one hp k) le_rfl (by linarith) le_rfl hk
  · refine ⟨1, zero_lt_one, Eventually.of_forall ?_⟩
    intro k hk
    exact hh (Chart.time_nonneg (exact_N_gt_one hp k) hk)

/-- A fixed finite family of forbidden costs has one common tolerance and
one common original-sample cutoff. -/
theorem finite_family_chart_exclusion {p : Code} (hp : Split.Exact p)
    {α : Type*} (s : Finset α) (r h : α → ℝ) (b : ℝ)
    (hnot : ∀ a ∈ s, ¬Split.Known p (r a) b (h a)) (B : ℕ) (hB : 1 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop,
      ∀ a ∈ s, ¬Split.Chart p B (r a) b (h a) ε false k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨εa, hεa, hka⟩ := eventually_not_chart_of_not_known hp
      (hnot a (Finset.mem_insert_self _ _)) B hB
    obtain ⟨εs, hεs, hks⟩ := ih (fun a ha => hnot a (Finset.mem_insert_of_mem ha))
    refine ⟨min εa εs, lt_min hεa hεs, ?_⟩
    filter_upwards [hka, hks] with k hka hks a' ha' hc
    have hN : 1 ≤ p.N k := exact_N_ge_one hp k
    rcases Finset.mem_insert.mp ha' with rfl | ha'
    · exact hka (Chart.relax_false hN le_rfl le_rfl (min_le_left _ _) hc)
    · exact hks a' ha' (Chart.relax_false hN le_rfl le_rfl (min_le_right _ _) hc)

/-- A fixed-complexity exclusion inside any genuine exact problem. The
known-atlas lower bound is established before choosing the sample. -/
theorem finite_guard_of_known_exclusion {p : Code} (hp : Split.Exact p)
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hknown : ∀ r h : ℝ, 0 ≤ r → r < p.L → Split.Known p r p.L h → κ * r - δ / 4 < h)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, ∀ r h : ℝ, 0 ≤ r → r < p.L →
      h ≤ κ * r - δ → ¬Split.Chart p B r p.L h ε false k := by
  classical
  let t : ℝ := δ / (4 * κ)
  have ht : 0 < t := div_pos hδ (mul_pos (by norm_num) hκ)
  have hκt : κ * t = δ / 4 := by
    dsimp [t]
    field_simp [hκ.ne']
  let s : Finset ℕ :=
    (Finset.range (⌊p.L / t⌋₊ + 1)).filter (fun (j : ℕ) => (j : ℝ) * t < p.L)
  have hnot : ∀ j ∈ s, ¬Split.Known p ((j : ℝ) * t) p.L
      (κ * ((j : ℝ) * t) - δ / 2) := by
    intro j hj hk
    have hcost := hknown ((j : ℝ) * t) (κ * ((j : ℝ) * t) - δ / 2)
      (mul_nonneg (Nat.cast_nonneg _) ht.le) (Finset.mem_filter.mp hj).2 hk
    linarith
  obtain ⟨ε, hε, hk⟩ := finite_family_chart_exclusion hp s
    (fun j => (j : ℝ) * t) (fun j => κ * ((j : ℝ) * t) - δ / 2) p.L hnot B hB
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hk] with k hk r h hr hr1 hh hc
  let j : ℕ := ⌊r / t⌋₊
  have hjle : (j : ℝ) * t ≤ r := by
    have hf := Nat.floor_le (div_nonneg hr ht.le)
    exact (le_div_iff₀ ht).mp hf
  have hjlt : r < (j : ℝ) * t + t := by
    have hf := Nat.lt_floor_add_one (r / t)
    have hm := (div_lt_iff₀ ht).mp hf
    simpa only [add_mul, one_mul] using hm
  have hjbound : j ≤ ⌊p.L / t⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right hr1.le ht.le)
  have hjs : j ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), hjle.trans_lt hr1⟩
  have htime : h ≤ κ * ((j : ℝ) * t) - δ / 2 := by
    have hm := mul_lt_mul_of_pos_left hjlt hκ
    nlinarith
  exact hk j hjs (Chart.relax_false (exact_N_ge_one hp k) hjle htime le_rfl hc)

/-- The extremal angular class of a critical certificate at outer index `i`: every
exact competitor with cap at most `D`, angular exponent `S₀` and angular range
`η L` has horizon at most `b L`. -/
def ClassBound (D S₀ η b : ℝ) : Prop :=
  ∀ q : Code, Split.Exact q → q.d ≤ D → q.S = S₀ → q.U = η * q.L →
    Split.Horizon q ≤ b * q.L

/-- Normalizing a terminal-known atlas leaves a competitor in the same extremal class;
its remaining length is charged at the class rate. -/
theorem known_budget_in_class (hcalc : Split.Calculus) {D S₀ η b : ℝ}
    (hclass : ClassBound D S₀ η b)
    {p : Code} (hp : Split.Exact p) (hpd : p.d ≤ D)
    (hpS : p.S = S₀) (hpU : p.U = η * p.L)
    {r b' h : ℝ} (hr : 0 ≤ r) (hrL : r < p.L) (hrb : r ≤ b') (hbL : b' ≤ p.L)
    (hknown : Split.Known p r b' h) :
    Split.Horizon p ≤ h + b * (p.L - r) := by
  obtain ⟨q, hq, hL, hd, hS, hU, _, hcomp, _, _⟩ :=
    hcalc.2.2 p r b' h p.d hp hr hrL hrb hbL (exact_cap_nonneg hp) (exact_cap_lt_one hp)
      (fun s hrs hsL => exact_terminal_cap hp (hr.trans hrs) hsL) hknown
  change Code.L q = p.L - r at hL
  change Code.d q = p.d at hd
  change Code.S q = p.S at hS
  change Code.U q = p.U * (p.L - r) / p.L at hU
  have hcap : Code.d q ≤ D := by rw [hd]; exact hpd
  have hU' : Code.U q = η * Code.L q := by
    rw [hU, hL, hpU]
    field_simp [(exact_length_pos hp).ne']
  have hbound := hclass q hq hcap (hS.trans hpS) hU'
  rw [hL] at hbound
  calc
    Split.Horizon p ≤ h + Split.Horizon q := hcomp
    _ ≤ h + b * (p.L - r) := by linarith only [hbound]

/-- A near-optimal genuine exact problem in the class has its own finite guard.
The strict horizon gap is checked in that exact problem before sampling. -/
theorem finite_guard_in_class (hcalc : Split.Calculus) {D S₀ η b : ℝ}
    (hclass : ClassBound D S₀ η b)
    {p : Code} (hp : Split.Exact p) (hpd : p.d ≤ D)
    (hpS : p.S = S₀) (hpU : p.U = η * p.L)
    {δ : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hgap : b * p.L - δ / 4 < Split.Horizon p) (B : ℕ) (hB : 1 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, ∀ r h : ℝ, 0 ≤ r → r < p.L →
      h ≤ b * r - δ → ¬Split.Chart p B r p.L h ε false k := by
  apply finite_guard_of_known_exclusion hp hb hδ ?_ B hB
  intro r h hr hrL hknown
  have hbudget := known_budget_in_class hcalc hclass hp hpd hpS hpU hr hrL hrL.le le_rfl
    hknown
  linarith only [hbudget, hgap]

/-- The guard in the tangent normalization of one stage. Fix an exact parent `p` in the
class with a strict horizon gap, a scale, a buffer, a complexity exponent and a stage
index; then the stage guard holds at every sufficiently late original sample, as soon as
the guard slack tends to zero along the samples. -/
theorem eventually_scaled_guard (hcalc : Split.Calculus) {D S₀ η b : ℝ}
    (hclass : ClassBound D S₀ η b)
    {p : Code} (hp : Split.Exact p) (hpd : p.d ≤ D)
    (hpS : p.S = S₀) (hpU : p.U = η * p.L)
    {κ R scale buffer : ℝ} (hb : 0 < b) (hscale : 0 < scale) (hR : 1 ≤ R)
    (hbuffer : 0 < buffer) (hRL : scale * R < p.L)
    (hκb : |κ - b| * R ≤ buffer / 4)
    (hgap : b * p.L - scale * buffer / 8 < Split.Horizon p) (B : ℕ) (hB : 1 ≤ B)
    (loss : ℕ → ℝ) (hloss : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, loss m ≤ ε) :
    ∀ᶠ m in atTop, ∀ r h : ℝ, R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - buffer →
      ¬Split.Chart p B (scale * r) p.L (scale * h) (loss m) false m := by
  have hδ : 0 < scale * buffer / 2 := by positivity
  obtain ⟨ε, hε, hk⟩ := finite_guard_in_class hcalc hclass hp hpd hpS hpU hδ hb
    (by linarith only [hgap]) B hB
  filter_upwards [hk, hloss ε hε] with m hm hlm r h hr1 hr2 hh hc
  have hRpos : 0 < R := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le (inv_pos.mpr hRpos) hr1
  have hrL : scale * r < p.L := lt_of_le_of_lt (by gcongr) hRL
  have hκ' : (κ - b) * r ≤ buffer / 4 := by
    have h1 : (κ - b) * r ≤ |κ - b| * r := by
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hr0.le
    have h2 : |κ - b| * r ≤ |κ - b| * R := by
      exact mul_le_mul_of_nonneg_left hr2 (abs_nonneg _)
    linarith
  have htime : scale * h ≤ b * (scale * r) - scale * buffer / 2 := by
    have : h ≤ b * r - buffer / 2 := by nlinarith
    nlinarith
  exact hm (scale * r) (scale * h) (by positivity) hrL htime
    (Chart.relax_false (exact_N_ge_one hp m) le_rfl le_rfl hlm hc)

end Submission.Obl.k4_scalar_guarded_tangent_preparation
