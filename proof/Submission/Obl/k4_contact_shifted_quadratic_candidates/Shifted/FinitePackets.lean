import Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted.Interface
import Submission.Obl.k4_contact_shifted_quadratic_candidates.SlowFrames

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

noncomputable section

/-- The finite construction at a fixed grid resolution. All source floors
still use the original residual law and original full assignment weights. -/
structure FiniteFramePacket {α : Type} [MeasurableSpace α] (D : Data α)
    (s₀ U' e₀' : ℝ) (m k : ℕ) where
  frame : Frame D k s₀ U'
  θ : ℝ
  K₂ : ℝ
  steps : frame.m = m
  good : FrameGood frame ((m : ℝ) + 2) θ K₂ e₀'
  rho_floor : ENNReal.ofReal (θ * frame.ql 0) *
    D.ν k (D.A k (frame.depth 0) frame.i₀) ≤ D.ρ k frame.core

namespace FiniteFramePacket

variable {α : Type} [MeasurableSpace α] {D : Data α} {s₀ U' e₀' : ℝ} {m k : ℕ}

def cost (p : FiniteFramePacket D s₀ U' e₀' m k) : ℝ :=
  1 + p.frame.H + p.θ⁻¹ + p.K₂ + ((m : ℝ) + 1)

theorem H_le_cost (p : FiniteFramePacket D s₀ U' e₀' m k) : p.frame.H ≤ p.cost := by
  have hH := p.good.H_ge
  have hK := p.good.K₂_ge
  have hi := inv_pos.mpr p.good.θ_pos
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  dsimp only [cost]
  linarith

theorem inv_theta_le_cost (p : FiniteFramePacket D s₀ U' e₀' m k) : p.θ⁻¹ ≤ p.cost := by
  have hH := p.good.H_ge
  have hK := p.good.K₂_ge
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  dsimp only [cost]
  linarith

theorem K₂_le_cost (p : FiniteFramePacket D s₀ U' e₀' m k) : p.K₂ ≤ p.cost := by
  have hH := p.good.H_ge
  have hi := inv_pos.mpr p.good.θ_pos
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  dsimp only [cost]
  linarith

theorem steps_le_cost (p : FiniteFramePacket D s₀ U' e₀' m k) : (m : ℝ) + 1 ≤ p.cost := by
  have hH := p.good.H_ge
  have hK := p.good.K₂_ge
  have hi := inv_pos.mpr p.good.θ_pos
  dsimp only [cost]
  linarith

end FiniteFramePacket

/-- The only asymptotic diagonal needed in frame preparation: solve the
finite problem at every fixed resolution and tolerance, then let resolution
grow slowly. -/
theorem goodFrames_of_finite_packets
    {α : Type} [MeasurableSpace α] (D : Data α) (s₀ U' e₀' : ℝ)
    (hN : ∀ k, 1 ≤ D.N k) (hU' : 0 < U')
    (hfinite : ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∃ p : FiniteFramePacket D s₀ U' e₀' m k,
        p.cost ≤ D.N k ^ ε) :
    Nonempty (GoodFrames D s₀ U' e₀') := by
  classical
  obtain ⟨m, H, packets, hmmono, hm1, hmt, hH1, hHsub, _, hpacket, hpresent⟩ :=
    exists_slow_frames D.N hN (FiniteFramePacket D s₀ U' e₀')
      (fun _ _ _ => True) (fun _ _ p => p.cost)
      (fun m hm ε hε => (hfinite m hm ε hε).mono fun k hk => by
        obtain ⟨p, hp⟩ := hk
        exact ⟨p, trivial, hp⟩)
  let fr : (k : ℕ) → Option (Frame D k s₀ U') := fun k => (packets k).map (fun p => p.frame)
  let θ : ℕ → ℝ := fun k => (packets k).elim 1 (fun p => p.θ)
  let K₂ : ℕ → ℝ := fun k => (packets k).elim 1 (fun p => p.K₂)
  have hmr : Tendsto (fun k => (m k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hmt
  refine ⟨{
    fr := fr
    Rk := fun k => (m k : ℝ) + 2
    θ := θ
    K₂ := K₂
    good := ?_
    rho_floor := ?_
    eventually_some := ?_
    Rk_large := ?_
    θ_large := ?_
    K₂_small := ?_
    H_small := ?_
    gap_small := ?_
    steps_small := ?_ }⟩
  · intro k f hf
    cases hp : packets k with
    | none =>
      simp only [fr, hp, Option.map_none] at hf
      cases hf
    | some p =>
      have heq : p.frame = f := by simpa only [fr, hp, Option.map_some, Option.some.injEq] using hf
      subst f
      simpa only [θ, K₂, hp, Option.elim_some] using p.good
  · intro k f hf
    cases hp : packets k with
    | none =>
      simp only [fr, hp, Option.map_none] at hf
      cases hf
    | some p =>
      have heq : p.frame = f := by simpa only [fr, hp, Option.map_some, Option.some.injEq] using hf
      subst f
      simpa only [θ, hp, Option.elim_some] using p.rho_floor
  · filter_upwards [hpresent] with k hk
    cases hp : packets k with
    | none => exact False.elim (hk hp)
    | some p => exact ⟨p.frame, by simp only [fr, hp, Option.map_some]⟩
  · intro R
    filter_upwards [hmr.eventually_ge_atTop R] with k hk
    linarith
  · intro ε hε
    filter_upwards [hHsub ε hε, hpresent] with k hHk hk
    cases hp : packets k with
    | none => exact False.elim (hk hp)
    | some p =>
      have hθinv : p.θ⁻¹ ≤ D.N k ^ ε := p.inv_theta_le_cost.trans ((hpacket k p hp).2.trans hHk)
      have hpow : 0 < D.N k ^ ε := Real.rpow_pos_of_pos (by linarith [hN k]) _
      have hh := one_div_le_one_div_of_le (inv_pos.mpr p.good.θ_pos) hθinv
      simpa only [θ, hp, Option.elim_some, one_div, inv_inv, Real.rpow_neg (by linarith [hN k] : 0 ≤ D.N k)] using hh
  · intro ε hε
    filter_upwards [hHsub ε hε, hpresent] with k hHk hk
    cases hp : packets k with
    | none => exact False.elim (hk hp)
    | some p =>
      simpa only [K₂, hp, Option.elim_some] using
        p.K₂_le_cost.trans ((hpacket k p hp).2.trans hHk)
  · intro ε hε
    filter_upwards [hHsub ε hε] with k hHk
    intro f hf
    cases hp : packets k with
    | none =>
      simp only [fr, hp, Option.map_none] at hf
      cases hf
    | some p =>
      have heq : p.frame = f := by simpa only [fr, hp, Option.map_some, Option.some.injEq] using hf
      subst f
      exact p.H_le_cost.trans ((hpacket k p hp).2.trans hHk)
  · intro ε hε
    filter_upwards [hmr.eventually_ge_atTop (U' / ε)] with k hk
    intro f hf
    cases hp : packets k with
    | none =>
      simp only [fr, hp, Option.map_none] at hf
      cases hf
    | some p =>
      have heq : p.frame = f := by simpa only [fr, hp, Option.map_some, Option.some.injEq] using hf
      subst f
      rw [p.steps]
      have hmpos : (0 : ℝ) < m k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm1 k))
      apply (div_le_iff₀ hmpos).mpr
      have hh := (div_le_iff₀ hε).mp hk
      nlinarith
  · intro ε hε
    filter_upwards [hHsub ε hε] with k hHk
    intro f hf
    cases hp : packets k with
    | none =>
      simp only [fr, hp, Option.map_none] at hf
      cases hf
    | some p =>
      have heq : p.frame = f := by simpa only [fr, hp, Option.map_some, Option.some.injEq] using hf
      subst f
      rw [p.steps]
      exact p.steps_le_cost.trans ((hpacket k p hp).2.trans hHk)

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
