import Submission.Obl.k4_scalar_guarded_entropic_path.PowerAllowance

/-! A finite menu of genuine parents admits one arbitrarily small
power allowance, chosen after all original guard complexities. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

theorem guard_format_ge (M k : ℕ) : M ≤ 2 ^ ((M + k + 1) ^ 2) := by
  have he : M ≤ (M + k + 1) ^ 2 :=
    (show M ≤ M + k + 1 by omega).trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)
  exact (Nat.lt_pow_self (by decide : 1 < 2) (n := M)).le.trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) he)

theorem exists_common_power_allowance_guard {α : Type*} [Fintype α] [Nonempty α]
    (p : α → Code) (hp : ∀ a, Split.Exact (p a))
    (φ : α → ℕ → ℕ) (hφ : ∀ a, StrictMono (φ a))
    (N : ℕ → ℝ) (hNt : Tendsto N atTop atTop)
    {κ gain θ : ℝ} (hκ : 0 < κ) (hgain : 0 < gain) (hθ : 0 < θ)
    (hknown : ∀ a r h, 0 ≤ r → r < (p a).L →
      Split.Known (p a) r (p a).L h → κ * r - gain / 4 < h)
    (B : α → ℕ) (hB : ∀ a, 1 ≤ B a) (n : ℕ) (hn : 0 < n) :
    ∃ v : ℝ, 0 < v ∧ v < θ ∧ ∀ᶠ k in atTop, ∀ a r h,
      0 ≤ r → r < (p a).L → h ≤ κ * r - gain →
      ¬Split.Chart (p a) (B a) r (p a).L h
        (Real.log ((N k ^ v * Real.log (N k)) ^ n) / Real.log (N k)) false (φ a k) := by
  classical
  have hguard (a : α) : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ m in atTop, ∀ r h,
      0 ≤ r → r < (p a).L → h ≤ κ * r - gain →
      ¬Split.Chart (p a) (B a) r (p a).L h ε false m :=
    finite_guard_of_known_exclusion (hp a) hκ hgain (hknown a) (B a) (hB a)
  choose εa hεa hg using hguard
  let ε := Finset.univ.inf' Finset.univ_nonempty εa
  have hε : 0 < ε := by
    rw [Finset.lt_inf'_iff]
    exact fun a _ => hεa a
  have hεle (a : α) : ε ≤ εa a := Finset.inf'_le εa (Finset.mem_univ a)
  let v : ℝ := min (θ / 2) (ε / (2 * (n : ℝ)))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hv : 0 < v := lt_min (half_pos hθ) (div_pos hε (by positivity))
  have hvθ : v < θ := (min_le_left _ _).trans_lt (by linarith)
  have hnv : (n : ℝ) * v < ε := by
    have hvle : v ≤ ε / (2 * (n : ℝ)) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_left hvle hnR.le
    have heq : (n : ℝ) * (ε / (2 * (n : ℝ))) = ε / 2 := by field_simp
    rw [heq] at hm
    linarith
  have hall : ∀ᶠ k in atTop, ∀ a r h, 0 ≤ r → r < (p a).L → h ≤ κ * r - gain →
      ¬Split.Chart (p a) (B a) r (p a).L h (εa a) false (φ a k) := by
    apply Filter.eventually_all.2
    intro a
    exact (hφ a).tendsto_atTop.eventually (hg a)
  refine ⟨v, hv, hvθ, ?_⟩
  filter_upwards [hall,
    (power_allowance_loss_tendsto N hNt v n).eventually (ge_mem_nhds hnv)]
    with k hk hs a r h hr hrL hh hc
  exact hk a r h hr hrL hh (Chart.relax_false (exact_N_ge_one (hp a) (φ a k))
    le_rfl le_rfl (hs.trans (hεle a)) hc)

end

end Submission.Obl.k4_scalar_guarded_entropic_path
