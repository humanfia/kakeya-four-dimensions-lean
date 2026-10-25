-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyLevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyKT
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.NonStickyBranch
-- Copied from session x0338 (o070 branch, commit ec01e52, file StickyLevel.lean), namespace renamed.

/-!
# The per-level dichotomy of the sticky branch, and small-`δ` bounds

* `eventually_le_rpow_neg`: a constant is at most `δ^(-p)` for all small `δ` (`p > 0`).
* `sticky_fibre_dichotomy`: in a prepared family with a sticky profile (`G i - c ≤ G j` for
  `i ≤ j`), every fibre `F` of a subset of `S` at a level `k ≤ top` is either KT-good with the
  constant `stickyK … k · δ^(-ν)` or carries a flat `LongFactor` (x0318's `fibre_dichotomy`, with the
  round-box bound of `roundBox_of_profile_slack`).
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- A constant is eventually at most `δ^(-p)`. -/
lemma eventually_le_rpow_neg (A : ℝ) {p : ℝ} (hp : 0 < p) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → A ≤ δ ^ (-p) := by
  set B := max A 1 with hB
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB0 : 0 < B := by linarith
  refine ⟨B ^ (-(1 / p)), Real.rpow_pos_of_pos hB0 _, fun δ hδ hδd => ?_⟩
  have h1 : (B ^ (-(1 / p))) ^ (-p) ≤ δ ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hδ hδd (by linarith)
  have h2 : (B ^ (-(1 / p))) ^ (-p) = B := by
    rw [← Real.rpow_mul hB0.le]
    have : -(1 / p) * -p = 1 := by field_simp
    rw [this, Real.rpow_one]
  calc A ≤ B := le_max_left _ _
    _ = (B ^ (-(1 / p))) ^ (-p) := h2.symm
    _ ≤ δ ^ (-p) := h1

/-- The round-box constant of the level-`k` fibres in the sticky case (slack `c`). -/
noncomputable def stickyK (δ L Λ c : ℝ) (a : ℕ → ℕ) (ρ : ℕ → ℝ) (k : ℕ) : ℝ :=
  400 * 122 ^ 3 * 16 ^ 3 * L ^ 2 * Λ * (2 * ((1 / δ) ^ c * levelDens a ρ k) * δ ^ 2)

lemma stickyK_nonneg {δ L Λ c : ℝ} (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (a : ℕ → ℕ) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) (k : ℕ) : 0 ≤ stickyK δ L Λ c a ρ k := by
  unfold stickyK
  have := levelDens_pos a hρ k
  positivity

open Classical in
/-- **Per-level dichotomy of the sticky branch.**  Let the family be prepared on the grid
`ρ k = 2 δ L^k` (`k ≤ top`) with populations in `[2^(a k), 2^(a k+1))`, and let the profile be
sticky with slack `c` (`G i - c ≤ G j` for `i ≤ j ≤ top`).  Then every nonempty `F ⊆ S` lying in
one level-`k` cell of `S` (`k ≤ top`) is KT-good with constant `stickyK δ L Λ c a ρ k · δ^(-ν)`, or
has a flat `LongFactor` with `Λ a < b`. -/
theorem sticky_fibre_dichotomy {δ ν Λ c : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hΛ : 1 ≤ Λ)
    (hdich : FibreDich ν δ) {L top : ℕ} (hL : 2 ≤ L)
    (htop : 2 * δ * (L : ℝ) ^ top ≤ 1 / 10000)
    {m : ℕ} (x v : Fin m → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i))) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (S : Finset (Fin m)) (a : ℕ → ℕ)
    (hpopS : ∀ k ≤ top, ∀ i ∈ S,
      pop S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i < 2 ^ (a k + 1))
    (hst : ∀ i j, i ≤ j → j ≤ top →
      cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top i - c ≤
        cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top j)
    (k : ℕ) (hk : k ≤ top) (F : Finset (Fin m)) (hFne : F.Nonempty) (i₁ : Fin m) (hi₁ : i₁ ∈ S)
    (hFcell : F ⊆ fibre S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i₁) :
    KTGood δ ν (stickyK δ L Λ c a (fun k => 2 * δ * (L : ℝ) ^ k) k * δ ^ (-ν)) x v F ∨
    (∃ a' b : ℝ, δ ≤ a' ∧ Λ * a' < b ∧ b ≤ 2 ∧
      LongFactor ν δ a' b (fun j : Fin F.card =>
        Tube δ (x (F.equivFin.symm j)) (v (F.equivFin.symm j)))) := by
  set ρ : ℕ → ℝ := fun k => 2 * δ * (L : ℝ) ^ k with hρdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (le_trans (by norm_num) hL)
  have hρpos : ∀ k, 0 < ρ k := fun k => by simp only [hρdef]; positivity
  have hρmono : ∀ k k', k ≤ k' → ρ k ≤ ρ k' := fun k k' hkk => by
    simp only [hρdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 hkk) (by positivity)
  have hFS : F ⊆ S := fun i hi => (Finset.mem_filter.mp (hFcell hi)).1
  have hFcard : F.card < 2 ^ (a (top - (top - k)) + 1) := by
    rw [show top - (top - k) = k by omega]
    have h1 : F.card ≤ pop S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i₁ :=
      Finset.card_le_card hFcell
    exact lt_of_le_of_lt h1 (hpopS k hk i₁ hi₁)
  have hround := roundBox_of_profile_slack x v S F hFS hδ hδ1 hL1 hΛ a hρpos
    (by simp only [hρdef]; nlinarith) (fun k => by simp only [hρdef]; rw [pow_succ]; ring_nf; rfl)
    (i₀ := top - k) (j := top - k) (top := top) (c := c) (by omega)
    (by rw [show top - (top - k) = k by omega]
        exact (hρmono k top hk).trans (htop.trans (by norm_num)))
    (fun i _ => hv i) (fun i _ => hT i) (fun i _ j _ => hanti i j)
    (fun k' hk' i hi => by
      have hk'' : k' ≤ top := by omega
      exact hpopS k' hk'' i hi)
    hFcard (fun l hl1 hl2 => hst (top - k) l hl1 hl2)
  rw [show top - (top - k) = k by omega] at hround
  have := hdich m x v hv hT hsep F hFne (stickyK δ L Λ c a ρ k) Λ
    (fun a' b e ha hab hbΛ hb2 => by
      have h := hround a' b e ha hab hbΛ hb2
      unfold stickyK
      exact h)
  exact this

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
