import Submission.Obl.k4_narrow_projected_row_parents.VelocityGlue
import Submission.Obl.k4_narrow_projected_row_parents.ListsOfCompared

/-!
# Velocity lists along a narrow sequence

`CompareSeq` is the comparison of the true labels at depth `s` with a family of
projected assignments along the whole sequence (paper, Lemma 8.3): eventually a
`Compared` record whose list sizes are subpower and whose code widths are at most a
subpower below the natural scales `min(q_s, β/g_s)` (time) and
`min(N^(-m), a_s q_s g_s)` (major coordinate).

`velocityLists_of_compareSeq`: if the projected widths `β` have the limiting exponent
`B` and the true depth `r` satisfies `ℓ r + e < B < (κ + ℓ) r`, `s < r ≤ U`, then at
the horizontal mesh exponent `aξ ≥ 2 (r + B + m + s)` the comparison gives
`VelocityLists r aξ e` (paper, Proposition 8.5, "From projected intervals to a row
list").
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The comparison along the sequence, at depth `s`, for the projected assignments `C k`
with widths `β k` at major mesh `N^(-m)`. -/
def CompareSeq (cfg : Model α) (s m : ℝ) (β : ℕ → ℝ) (n : ℕ → ℕ)
    (C : (k : ℕ) → Fin (n k) → Set α) : Prop :=
  ∃ M : ℕ → ℝ, (∀ k, 1 ≤ M k) ∧ Model.Subpow cfg.N M ∧ ∀ᶠ k in atTop, ∃ q' χ' : ℝ,
    0 < q' ∧ 0 < χ' ∧
    min ((Model.prepared cfg).q k s) (β k / cfg.N k ^ (-cfg.ℓ * s)) ≤ M k * q' ∧
    min (cfg.N k ^ (-m)) (cfg.N k ^ (-s) * ((Model.prepared cfg).q k s * cfg.N k ^ (-cfg.ℓ * s))) ≤
      M k * χ' ∧
    Nonempty (Compared (Model.prepared cfg) k s (C k) q' χ' (cfg.N k ^ (-cfg.ℓ * s))
      (q' * cfg.N k ^ (-cfg.ℓ * s)) (M k))

/-- A subpower factor times a power `N^(-a)` is eventually below `N^(-b)` when `b < a`. -/
theorem eventually_subpow_mul_rpow_le {N X : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hX : Model.Subpow N X) {a b : ℝ} (hab : b < a) :
    ∀ᶠ k in atTop, X k * N k ^ (-a) ≤ N k ^ (-b) := by
  filter_upwards [hX (a - b) (by linarith)] with k hk
  have hN0 : 0 < N k := lt_of_lt_of_le one_pos (hN k)
  calc X k * N k ^ (-a) ≤ N k ^ (a - b) * N k ^ (-a) :=
        mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hN0.le _)
    _ = N k ^ (-b) := by rw [← Real.rpow_add hN0]; ring_nf

/-- The true block lengths are within `K` of `N^(-κ s)`. -/
theorem q_bounds {p : Parameters} {a : PreparedModel α} {R : ℝ} {k : ℕ} {s : ℝ}
    (hp : p.Valid) (h : a.AtlasAt p R k s) :
    p.N k ^ (-(p.kappa * s)) / p.K k ≤ a.q k s ∧ a.q k s ≤ p.K k * p.N k ^ (-(p.kappa * s)) := by
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hK0 : 0 < p.K k := by linarith [hp.2.2.1.1 k]
  have hT0 : (0 : ℝ) < (2 : ℝ) ^ a.T k s := by positivity
  have hq : a.q k s = ((2 : ℝ) ^ a.T k s)⁻¹ := by
    unfold PreparedModel.q; rw [zpow_neg, zpow_natCast]
  have hpow : p.N k ^ (-(p.kappa * s)) = (p.N k ^ (p.kappa * s))⁻¹ := Real.rpow_neg hN0.le _
  have hNs : 0 < p.N k ^ (p.kappa * s) := Real.rpow_pos_of_pos hN0 _
  obtain ⟨h1, h2, -⟩ := h
  have h1' : p.N k ^ (p.kappa * s) ≤ (2 : ℝ) ^ a.T k s * p.K k := (div_le_iff₀ hK0).mp h1
  constructor
  · rw [hq, hpow, div_le_iff₀ hK0, inv_mul_eq_div, le_div_iff₀ hT0]
    calc (p.N k ^ (p.kappa * s))⁻¹ * (2 : ℝ) ^ a.T k s ≤ (p.N k ^ (p.kappa * s))⁻¹ *
          (p.K k * p.N k ^ (p.kappa * s)) := by gcongr
      _ = p.K k := by field_simp
  · rw [hq, hpow, ← div_eq_mul_inv, inv_le_comm₀ hT0 (by positivity), inv_div,
      div_le_iff₀ hK0]
    exact h1'

/-- The projected moving interval confines the transverse velocity. -/
theorem slice_velocity {b : Fin 6 → ℝ} {u v w : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |(Submission.Lib.K4ContactNormalization.point b t) 2 - u - t * v| ≤ w) :
    |b 4 - v| ≤ 2 * w := by
  have h0 := h 0 ⟨le_rfl, zero_le_one⟩
  have h1 := h 1 ⟨zero_le_one, le_rfl⟩
  simp only [Submission.Lib.K4ContactNormalization.point, Matrix.cons_val, zero_mul, add_zero,
    one_mul, sub_zero] at h0 h1
  have hid : b 4 - v = (b 1 + b 4 - u - v) - (b 1 - u) := by ring
  rw [hid]
  calc _ ≤ |b 1 + b 4 - u - v| + |b 1 - u| := abs_sub _ _
    _ ≤ w + w := add_le_add h1 h0
    _ = 2 * w := by ring

/-- `N^(-x) N^(-y) = N^(-(x + y))`. -/
theorem rpow_neg_mul_rpow_neg {N : ℝ} (hN : 0 < N) (x y : ℝ) :
    N ^ (-x) * N ^ (-y) = N ^ (-(x + y)) := by
  rw [← Real.rpow_add hN]; ring_nf

set_option maxHeartbeats 1600000 in
/-- **Velocity lists from the comparison along a narrow sequence.** -/
theorem velocityLists_of_compareSeq (cfg : Model α) (hv : Model.Valid cfg)
    {s m r B e aξ : ℝ} (hs : 0 < s) (hm : 0 < m) (hsr : s < r) (hrU : r ≤ cfg.U)
    (hBr : B < (cfg.κ + cfg.ℓ) * r) (he : 0 < e) (heB : e + cfg.ℓ * r < B)
    (hξ : 2 * (r + B + m + s) ≤ aξ)
    {H : ℕ → ℝ} (hH : ∀ k, 1 ≤ H k) (hHsub : Model.Subpow cfg.N H)
    {β : ℕ → ℝ} {n : ℕ → ℕ} {C : (k : ℕ) → Fin (n k) → Set α}
    {vel : (k : ℕ) → Fin (n k) → ℝ}
    (hvel : ∀ k i, ∀ l ∈ C k i, |cfg.b k l 4 - vel k i| ≤ 2 * (H k * β k))
    (hβ : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      cfg.N k ^ (-B - δ) ≤ β k ∧ β k ≤ cfg.N k ^ (-B + δ))
    (hcmp : CompareSeq cfg s m β n C) :
    VelocityLists cfg r aξ e := by
  classical
  have hp : (Model.parameters cfg).Valid := Model.parameters_valid hv
  have ha : (Model.prepared cfg).Valid (Model.parameters cfg) := Model.prepared_valid hv
  obtain ⟨M, hM1, hMsub, hev⟩ := hcmp
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [hv.scale k]
  have hNpos : ∀ k, 0 < cfg.N k := fun k => by linarith [hv.scale k]
  have hK1 : ∀ k, 1 ≤ cfg.K k := hv.subpower.1
  have hKsub : Model.Subpow cfg.N cfg.K := hv.subpower.2
  have hκ := hv.rate_pos
  have hκ1 := hv.rate_le_one
  have hℓ := hv.transverse_pos
  have hNt := hv.scale_limit
  have hM0 : ∀ k, 0 ≤ M k := fun k => by linarith [hM1 k]
  have hK0 : ∀ k, 0 ≤ cfg.K k := fun k => by linarith [hK1 k]
  have hc (c : ℝ) : Model.Subpow cfg.N (fun _ => c) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hNt c
  have hmul {f g : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
      (hf : Model.Subpow cfg.N f) (hg : Model.Subpow cfg.N g) :
      Model.Subpow cfg.N (fun k => f k * g k) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNpos hf0 hg0 hf hg
  have hadd {f g : ℕ → ℝ} (hf : Model.Subpow cfg.N f) (hg : Model.Subpow cfg.N g) :
      Model.Subpow cfg.N (fun k => f k + g k) := hf.add hNpos hNt hg
  -- the output bound
  set Mo : ℕ → ℝ := fun k => 3 * M k * (6912 * cfg.K k ^ 2) with hMo
  have hMoge : ∀ k, M k ≤ Mo k := by
    intro k
    have hK2 : 1 ≤ cfg.K k ^ 2 := one_le_pow₀ (hK1 k)
    simp only [hMo]
    nlinarith [hM1 k]
  have hMo1 : ∀ k, 1 ≤ Mo k := fun k => (hM1 k).trans (hMoge k)
  have hKK : Model.Subpow cfg.N (fun k => cfg.K k * cfg.K k) := hmul hK0 hK0 hKsub hKsub
  have hMosub : Model.Subpow cfg.N Mo := by
    have h1 := hmul (fun _ => by norm_num) hM0 (hc 3) hMsub
    have h2 := hmul (fun _ => by norm_num) (fun k => by positivity [hK0 k]) (hc 6912) hKK
    have h3 := hmul (fun k => by positivity [hM0 k]) (fun k => by positivity [hK0 k]) h1 h2
    intro ε hε
    filter_upwards [h3 ε hε] with k hk
    simp only [hMo]
    nlinarith [hk]
  refine ⟨Mo, hMo1, hMosub, ?_⟩
  -- depths and margins
  set R : ℝ := s⁻¹ + cfg.U + 2 with hR
  have hsinv : 0 < s⁻¹ := inv_pos.mpr hs
  have hU0 := hv.depth_pos
  have hR1 : 1 < R := by linarith
  have hRs : R⁻¹ ≤ s := by rw [inv_le_comm₀ (by linarith) hs]; linarith
  have hRr : R⁻¹ ≤ r := hRs.trans hsr.le
  have hsU : s ≤ cfg.U := hsr.le.trans hrU
  set δ : ℝ := min (((cfg.κ + cfg.ℓ) * r - B) / 4) ((B - e - cfg.ℓ * r) / 4) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ ((cfg.κ + cfg.ℓ) * r - B) / 4 := min_le_left _ _
  have hδ2 : δ ≤ (B - e - cfg.ℓ * r) / 4 := min_le_right _ _
  have hB0 : 0 < B := by nlinarith
  have hℓs : cfg.ℓ * s < cfg.ℓ * r := mul_lt_mul_of_pos_left hsr hℓ
  -- subpower factors
  have hX1 : Model.Subpow cfg.N (fun k => M k * (cfg.K k * cfg.K k)) :=
    hmul hM0 (fun k => by positivity [hK0 k]) hMsub hKK
  have hX1' : Model.Subpow cfg.N (fun k => M k * cfg.K k) := hmul hM0 hK0 hMsub hKsub
  have hK3 : Model.Subpow cfg.N (fun k => cfg.K k + 3) := hadd hKsub (hc 3)
  have hX2 : Model.Subpow cfg.N (fun k => M k * (cfg.K k + 3)) :=
    hmul hM0 (fun k => by positivity [hK0 k]) hMsub hK3
  have hX2' : Model.Subpow cfg.N (fun k => M k * (cfg.K k + 3) * cfg.K k) :=
    hmul (fun k => by positivity [hM0 k, hK0 k]) hK0 hX2 hKsub
  have hX3 : Model.Subpow cfg.N (fun k => 4 * H k) :=
    hmul (fun _ => by norm_num) (fun k => by linarith [hH k]) (hc 4) hHsub
  have hX4 : Model.Subpow cfg.N (fun k => 2 * cfg.K k) :=
    hmul (fun _ => by norm_num) hK0 (hc 2) hKsub
  -- exponent margins
  have hκr : cfg.κ * s < cfg.κ * r := mul_lt_mul_of_pos_left hsr hκ
  have hκs : cfg.κ * s ≤ s := by nlinarith
  have hκr0 : 0 < cfg.κ * r := mul_pos hκ (hs.trans hsr)
  have hℓs0 : 0 < cfg.ℓ * s := mul_pos hℓ hs
  have hκℓ : (cfg.κ + cfg.ℓ) * s < (cfg.κ + cfg.ℓ) * r :=
    mul_lt_mul_of_pos_left hsr (by linarith)
  have hδB : δ < B := by linarith
  have hr0 : 0 < r := hs.trans hsr
  have m1a : cfg.κ * s < cfg.κ * r + aξ := by linarith
  have m1b : B + δ - cfg.ℓ * s < cfg.κ * r + aξ := by linarith
  have m2a : m < aξ := by linarith
  have m2b : cfg.κ * s + cfg.ℓ * s + s < aξ := by linarith
  have m6a : cfg.κ * s + cfg.ℓ * s < (cfg.κ + cfg.ℓ) * r := by linarith
  have m6b : B + δ < (cfg.κ + cfg.ℓ) * r := by linarith
  have m7a : cfg.κ * s + cfg.ℓ * s < cfg.κ * r + aξ := by linarith
  have m7b : B + δ < cfg.κ * r + aξ := by linarith
  have m8a : e < B - δ - cfg.ℓ * r := by linarith
  have m8b : e < aξ - cfg.ℓ * r := by linarith
  have m5 : cfg.ℓ * s ≤ aξ := by linarith
  refine Eventually.frequently ?_
  filter_upwards [hev, ha.2.2.1 R hR1, ha.2.2.2 R hR1, hβ δ hδ,
    eventually_subpow_mul_rpow_le hN1 hX1 m1a, eventually_subpow_mul_rpow_le hN1 hX1' m1b,
    eventually_subpow_mul_rpow_le hN1 hX2 m2a, eventually_subpow_mul_rpow_le hN1 hX2' m2b,
    eventually_subpow_mul_rpow_le hN1 hX1 m6a, eventually_subpow_mul_rpow_le hN1 hX1 m6b,
    eventually_subpow_mul_rpow_le hN1 hX1 m7a, eventually_subpow_mul_rpow_le hN1 hX1 m7b,
    eventually_subpow_mul_rpow_le hN1 hX3 m8a, eventually_subpow_mul_rpow_le hN1 hX4 m8b]
    with k hk hat hnest hβk h1a h1b h2a h2b h6a h6b h7a h7b h8a h8b
  obtain ⟨q', χ', hq', hχ', hq'b, hχ'b, ⟨cmp⟩⟩ := hk
  have hN : 0 < cfg.N k := hNpos k
  have hKk : 1 ≤ cfg.K k := hK1 k
  have hK0k : 0 < cfg.K k := by linarith
  have hMq : 0 < M k := by linarith [hM1 k]
  have hatr := hat r hRr hrU
  have hats := hat s hRs hsU
  have hnestk : ∀ i : Fin ((Model.prepared cfg).n k r), ∃ h : Fin ((Model.prepared cfg).n k s),
      (Model.prepared cfg).A k r i ⊆ (Model.prepared cfg).A k s h ∧
      (Model.prepared cfg).block k r i ⊆ (Model.prepared cfg).block k s h :=
    fun i => hnest s r hRs hsr hrU i
  obtain ⟨-, hqr2⟩ := q_bounds hp hatr
  obtain ⟨hqs1, -⟩ := q_bounds hp hats
  have hqr2' : (Model.prepared cfg).q k r ≤ cfg.K k * cfg.N k ^ (-(cfg.κ * r)) := hqr2
  have hqs1' : cfg.N k ^ (-(cfg.κ * s)) / cfg.K k ≤ (Model.prepared cfg).q k s := hqs1
  have hqr0 : 0 < (Model.prepared cfg).q k r := q_pos _ k r
  have hqr1' : (Model.prepared cfg).q k r ≤ 1 := by
    simp only [PreparedModel.q]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
  have hξ0 : 0 < cfg.N k ^ (-aξ) := Real.rpow_pos_of_pos hN _
  have hξ1 : cfg.N k ^ (-aξ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)
  have hgr0 : 0 < cfg.N k ^ (-cfg.ℓ * r) := Real.rpow_pos_of_pos hN _
  have hgs0 : 0 < cfg.N k ^ (-cfg.ℓ * s) := Real.rpow_pos_of_pos hN _
  have hNκs0 : 0 < cfg.N k ^ (-(cfg.κ * s)) := Real.rpow_pos_of_pos hN _
  -- rewritings of powers
  have eKr : cfg.N k ^ (-(cfg.κ * r)) * cfg.N k ^ (-aξ) = cfg.N k ^ (-(cfg.κ * r + aξ)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have eKrg : cfg.N k ^ (-(cfg.κ * r)) * cfg.N k ^ (-cfg.ℓ * r) =
      cfg.N k ^ (-((cfg.κ + cfg.ℓ) * r)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have eKs : cfg.N k ^ (-(cfg.κ * s)) * cfg.N k ^ (-cfg.ℓ * s) =
      cfg.N k ^ (-(cfg.κ * s + cfg.ℓ * s)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have eβ : cfg.N k ^ (-B - δ) / cfg.N k ^ (-cfg.ℓ * s) =
      cfg.N k ^ (-(B + δ - cfg.ℓ * s)) := by
    rw [← Real.rpow_sub hN]; congr 1; ring
  have eβ' : cfg.N k ^ (-B - δ) = cfg.N k ^ (-(B + δ)) := by congr 1; ring
  -- a generic step: `M q ξ`-type products below the two time scales
  have hstep : ∀ X : ℝ, 0 ≤ X →
      M k * (cfg.K k * cfg.K k) * X ≤ cfg.N k ^ (-(cfg.κ * s)) →
      M k * (cfg.K k * X) ≤ (Model.prepared cfg).q k s := by
    intro X hX h
    refine le_trans ?_ hqs1'
    rw [le_div_iff₀ hK0k]
    calc M k * (cfg.K k * X) * cfg.K k = M k * (cfg.K k * cfg.K k) * X := by ring
      _ ≤ _ := h
  -- (1) the time code is coarser than the parent cell
  have hA1 : M k * ((Model.prepared cfg).q k r * cfg.N k ^ (-aξ)) ≤
      M k * (cfg.K k * cfg.N k ^ (-(cfg.κ * r + aξ))) := by
    calc M k * ((Model.prepared cfg).q k r * cfg.N k ^ (-aξ))
        ≤ M k * ((cfg.K k * cfg.N k ^ (-(cfg.κ * r))) * cfg.N k ^ (-aξ)) := by gcongr
      _ = M k * (cfg.K k * (cfg.N k ^ (-(cfg.κ * r)) * cfg.N k ^ (-aξ))) := by ring
      _ = _ := by rw [eKr]
  have hT1 : (Model.prepared cfg).q k r * cfg.N k ^ (-aξ) ≤ q' := by
    have hB1 := hstep _ (Real.rpow_nonneg hN.le _) h1a
    have hB2 : M k * (cfg.K k * cfg.N k ^ (-(cfg.κ * r + aξ))) ≤
        β k / cfg.N k ^ (-cfg.ℓ * s) := by
      refine le_trans ?_ (div_le_div_of_nonneg_right hβk.1 hgs0.le)
      rw [eβ, ← mul_assoc]; exact h1b
    exact le_of_mul_le_mul_left ((hA1.trans (le_min hB1 hB2)).trans hq'b) hMq
  -- (2) the major code is coarser than the parent cell
  have hχmain : M k * ((cfg.K k + 3) * cfg.N k ^ (-aξ)) ≤
      min (cfg.N k ^ (-m)) (cfg.N k ^ (-s) * ((Model.prepared cfg).q k s *
        cfg.N k ^ (-cfg.ℓ * s))) := by
    refine le_min ?_ ?_
    · rw [← mul_assoc]; exact h2a
    · have e3 : cfg.N k ^ (-s) * (cfg.N k ^ (-(cfg.κ * s)) * cfg.N k ^ (-cfg.ℓ * s)) =
          cfg.N k ^ (-(cfg.κ * s + cfg.ℓ * s + s)) := by
        rw [← Real.rpow_add hN, ← Real.rpow_add hN]; congr 1; ring
      have hlow : cfg.N k ^ (-(cfg.κ * s + cfg.ℓ * s + s)) / cfg.K k ≤
          cfg.N k ^ (-s) * ((Model.prepared cfg).q k s * cfg.N k ^ (-cfg.ℓ * s)) := by
        rw [← e3]
        calc cfg.N k ^ (-s) * (cfg.N k ^ (-(cfg.κ * s)) * cfg.N k ^ (-cfg.ℓ * s)) / cfg.K k =
            cfg.N k ^ (-s) * (cfg.N k ^ (-(cfg.κ * s)) / cfg.K k * cfg.N k ^ (-cfg.ℓ * s)) := by
              ring
          _ ≤ _ := by gcongr
      refine le_trans ?_ hlow
      rw [le_div_iff₀ hK0k]
      calc M k * ((cfg.K k + 3) * cfg.N k ^ (-aξ)) * cfg.K k =
          M k * (cfg.K k + 3) * cfg.K k * cfg.N k ^ (-aξ) := by ring
        _ ≤ _ := h2b
  have hχ3 : (cfg.K k + 3) * cfg.N k ^ (-aξ) ≤ χ' :=
    le_of_mul_le_mul_left (hχmain.trans hχ'b) hMq
  have hT2 : (Model.prepared cfg).q k r * cfg.N k ^ (-aξ) * (1 + cfg.K k) +
      2 * cfg.N k ^ (-aξ) ≤ χ' := by
    have : (Model.prepared cfg).q k r * cfg.N k ^ (-aξ) * (1 + cfg.K k) ≤
        cfg.N k ^ (-aξ) * (1 + cfg.K k) := by
      gcongr
      calc (Model.prepared cfg).q k r * cfg.N k ^ (-aξ) ≤ 1 * cfg.N k ^ (-aξ) := by gcongr
        _ = _ := one_mul _
    have e : cfg.N k ^ (-aξ) * (1 + cfg.K k) + 2 * cfg.N k ^ (-aξ) =
        (cfg.K k + 3) * cfg.N k ^ (-aξ) := by ring
    linarith
  have hT2' : cfg.N k ^ (-aξ) ≤ χ' := by
    refine le_trans ?_ hχ3
    calc cfg.N k ^ (-aξ) = 1 * cfg.N k ^ (-aξ) := (one_mul _).symm
      _ ≤ (cfg.K k + 3) * cfg.N k ^ (-aξ) := by gcongr; linarith
  -- (4), (5)
  have hT3 : narrow (Model.parameters cfg) k r ≤ cfg.N k ^ (-cfg.ℓ * s) := by
    show cfg.N k ^ (-cfg.ℓ * r) ≤ cfg.N k ^ (-cfg.ℓ * s)
    exact Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
  have hT3' : cfg.N k ^ (-aξ) ≤ cfg.N k ^ (-cfg.ℓ * s) :=
    Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
  -- (6), (7) the transverse code is coarser than the parent box
  have hminmul : min ((Model.prepared cfg).q k s) (β k / cfg.N k ^ (-cfg.ℓ * s)) *
      cfg.N k ^ (-cfg.ℓ * s) =
      min ((Model.prepared cfg).q k s * cfg.N k ^ (-cfg.ℓ * s)) (β k) := by
    rw [min_mul_of_nonneg _ _ hgs0.le, div_mul_cancel₀ _ hgs0.ne']
  have hstep2 : ∀ X : ℝ, 0 ≤ X →
      M k * (cfg.K k * cfg.K k) * X ≤ cfg.N k ^ (-(cfg.κ * s + cfg.ℓ * s)) →
      M k * (cfg.K k * cfg.K k) * X ≤ cfg.N k ^ (-(B + δ)) →
      M k * (cfg.K k * X) ≤ q' * cfg.N k ^ (-cfg.ℓ * s) * M k := by
    intro X hX h1 h2
    have hB1 : M k * (cfg.K k * X) ≤ (Model.prepared cfg).q k s * cfg.N k ^ (-cfg.ℓ * s) := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_right hqs1' hgs0.le)
      rw [div_mul_eq_mul_div, le_div_iff₀ hK0k, eKs]
      calc M k * (cfg.K k * X) * cfg.K k = M k * (cfg.K k * cfg.K k) * X := by ring
        _ ≤ _ := h1
    have hB2 : M k * (cfg.K k * X) ≤ β k := by
      refine le_trans ?_ hβk.1
      rw [eβ']
      calc M k * (cfg.K k * X) ≤ M k * (cfg.K k * cfg.K k) * X := by
            have : cfg.K k ≤ cfg.K k * cfg.K k := le_mul_of_one_le_right hK0k.le hKk
            calc M k * (cfg.K k * X) = M k * cfg.K k * X := by ring
              _ ≤ M k * (cfg.K k * cfg.K k) * X := by gcongr
        _ ≤ _ := h2
    have h := le_min hB1 hB2
    rw [← hminmul] at h
    calc M k * (cfg.K k * X) ≤ _ := h
      _ ≤ M k * q' * cfg.N k ^ (-cfg.ℓ * s) := mul_le_mul_of_nonneg_right hq'b hgs0.le
      _ = q' * cfg.N k ^ (-cfg.ℓ * s) * M k := by ring
  have hT4 : (Model.prepared cfg).q k r * narrow (Model.parameters cfg) k r ≤
      q' * cfg.N k ^ (-cfg.ℓ * s) := by
    have hA : M k * ((Model.prepared cfg).q k r * cfg.N k ^ (-cfg.ℓ * r)) ≤
        M k * (cfg.K k * cfg.N k ^ (-((cfg.κ + cfg.ℓ) * r))) := by
      calc M k * ((Model.prepared cfg).q k r * cfg.N k ^ (-cfg.ℓ * r))
          ≤ M k * ((cfg.K k * cfg.N k ^ (-(cfg.κ * r))) * cfg.N k ^ (-cfg.ℓ * r)) := by gcongr
        _ = M k * (cfg.K k * (cfg.N k ^ (-(cfg.κ * r)) * cfg.N k ^ (-cfg.ℓ * r))) := by ring
        _ = _ := by rw [eKrg]
    have h := hA.trans (hstep2 _ (Real.rpow_nonneg hN.le _) h6a h6b)
    have h' : ((Model.prepared cfg).q k r * cfg.N k ^ (-cfg.ℓ * r)) * M k ≤
        (q' * cfg.N k ^ (-cfg.ℓ * s)) * M k := by linarith
    exact le_of_mul_le_mul_right h' hMq
  have hT4' : (Model.prepared cfg).q k r * cfg.N k ^ (-aξ) ≤ q' * cfg.N k ^ (-cfg.ℓ * s) := by
    have h := hA1.trans (hstep2 _ (Real.rpow_nonneg hN.le _) h7a h7b)
    have h' : ((Model.prepared cfg).q k r * cfg.N k ^ (-aξ)) * M k ≤
        (q' * cfg.N k ^ (-cfg.ℓ * s)) * M k := by linarith
    exact le_of_mul_le_mul_right h' hMq
  -- (8) the list accuracy
  have hT5 : (2 * (H k * β k) + cfg.K k * cfg.N k ^ (-aξ)) / narrow (Model.parameters cfg) k r ≤
      cfg.N k ^ (-e) := by
    show (2 * (H k * β k) + cfg.K k * cfg.N k ^ (-aξ)) / cfg.N k ^ (-cfg.ℓ * r) ≤ cfg.N k ^ (-e)
    rw [div_le_iff₀ hgr0]
    have e1 : cfg.N k ^ (-B + δ) = cfg.N k ^ (-(B - δ - cfg.ℓ * r)) * cfg.N k ^ (-cfg.ℓ * r) := by
      rw [← Real.rpow_add hN]; congr 1; ring
    have e2 : cfg.N k ^ (-aξ) = cfg.N k ^ (-(aξ - cfg.ℓ * r)) * cfg.N k ^ (-cfg.ℓ * r) := by
      rw [← Real.rpow_add hN]; congr 1; ring
    have hH0 : 0 ≤ H k := by linarith [hH k]
    have hb1 : 2 * (H k * β k) ≤ 2 * H k * cfg.N k ^ (-B + δ) := by
      have := mul_le_mul_of_nonneg_left hβk.2 hH0
      linarith
    have hb2 : 2 * H k * cfg.N k ^ (-B + δ) ≤ cfg.N k ^ (-e) / 2 * cfg.N k ^ (-cfg.ℓ * r) := by
      rw [e1]
      have : 4 * H k * cfg.N k ^ (-(B - δ - cfg.ℓ * r)) ≤ cfg.N k ^ (-e) := h8a
      calc 2 * H k * (cfg.N k ^ (-(B - δ - cfg.ℓ * r)) * cfg.N k ^ (-cfg.ℓ * r))
          = (4 * H k * cfg.N k ^ (-(B - δ - cfg.ℓ * r))) / 2 * cfg.N k ^ (-cfg.ℓ * r) := by ring
        _ ≤ cfg.N k ^ (-e) / 2 * cfg.N k ^ (-cfg.ℓ * r) := by gcongr
    have hb3 : cfg.K k * cfg.N k ^ (-aξ) ≤ cfg.N k ^ (-e) / 2 * cfg.N k ^ (-cfg.ℓ * r) := by
      rw [e2]
      have : 2 * cfg.K k * cfg.N k ^ (-(aξ - cfg.ℓ * r)) ≤ cfg.N k ^ (-e) := h8b
      calc cfg.K k * (cfg.N k ^ (-(aξ - cfg.ℓ * r)) * cfg.N k ^ (-cfg.ℓ * r))
          = (2 * cfg.K k * cfg.N k ^ (-(aξ - cfg.ℓ * r))) / 2 * cfg.N k ^ (-cfg.ℓ * r) := by ring
        _ ≤ cfg.N k ^ (-e) / 2 * cfg.N k ^ (-cfg.ℓ * r) := by gcongr
    linarith
  have hT6 : (Model.prepared cfg).q k r * cfg.N k ^ (-aξ) ≤ 1 := by
    calc (Model.prepared cfg).q k r * cfg.N k ^ (-aξ) ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  obtain ⟨Gl, hGlm, hGlmass, hlists⟩ := lists_of_compared (Model.parameters cfg) hp
    (Model.prepared cfg) k ha.1 hatr hats hnestk (hvel k) cmp (hM0 k) hξ0 hq' hχ' hgs0 rfl
    (Real.rpow_pos_of_pos hN _) hT1 hT2 hT2' hT3 hT3' hT4 hT4' hT5 hT6
  refine ⟨Gl, hGlm, ?_, ?_⟩
  · refine le_trans ?_ hGlmass
    apply ENNReal.ofReal_le_ofReal
    exact inv_anti₀ (by linarith [hM1 k]) (hMoge k)
  · intro Q
    obtain ⟨L, hL, hmem⟩ := hlists Q
    exact ⟨L, hL, hmem⟩

end

end Submission.Obl.k4_narrow_projected_row_parents
