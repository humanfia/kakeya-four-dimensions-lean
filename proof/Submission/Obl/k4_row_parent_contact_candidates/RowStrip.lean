/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/RowStrip.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.RowParent

/-!
# Strip candidates from row parents along the sequence

`result_of_rowParents`: if row parents at a fixed depth `r` occur frequently
and their skew times the relative block length, plus the row error, fits in a
strip of width `L_k N^(-ℓ s - v)` with `L` subpower, then the frozen candidate
conclusion holds. Two regimes give this width directly:

* `result_of_strict_rate`: `ℓ < κ` with any bounded skew;
* `result_of_small_skew`: a power-small skew `|λ| ≤ N^(-c)`, any rates.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

open PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- A subpower sequence relative to `N`. -/
def Subpower (N L : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, L k ≤ N k ^ ε

theorem Parameters.Valid.tendsto_rpow {p : Parameters} (hp : p.Valid) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k => p.N k ^ x) atTop atTop :=
  (tendsto_rpow_atTop hx).comp hp.2.1

theorem Parameters.Valid.eventually_rpow_ge {p : Parameters} (hp : p.Valid) {x : ℝ}
    (hx : 0 < x) (C : ℝ) : ∀ᶠ k in atTop, C ≤ p.N k ^ x :=
  (hp.tendsto_rpow hx).eventually_ge_atTop C

theorem Parameters.Valid.N_pos {p : Parameters} (hp : p.Valid) (k : ℕ) : 0 < p.N k := by
  linarith [hp.1 k]

theorem Parameters.Valid.K_subpower {p : Parameters} (hp : p.Valid) : Subpower p.N p.K :=
  hp.2.2.1.2

theorem Parameters.Valid.one_le_K {p : Parameters} (hp : p.Valid) (k : ℕ) : 1 ≤ p.K k :=
  hp.2.2.1.1 k

/-- A choice of range containing two positive depths. -/
theorem exists_range {r s v : ℝ} (hr : 0 < r) (hs : 0 < s) (hv : 0 < v) :
    ∃ R : ℝ, 2 ≤ R ∧ R⁻¹ ≤ r ∧ R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R := by
  refine ⟨2 + s + v + r⁻¹ + s⁻¹ + v⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := inv_pos.mpr hr; have := inv_pos.mpr hs; have := inv_pos.mpr hv; linarith
  · apply inv_le_of_inv_le₀ hr
    have := inv_pos.mpr hs; have := inv_pos.mpr hv; linarith
  · apply inv_le_of_inv_le₀ hs
    have := inv_pos.mpr hr; have := inv_pos.mpr hv; linarith
  · have := inv_pos.mpr hr; have := inv_pos.mpr hs; have := inv_pos.mpr hv; linarith
  · apply inv_le_of_inv_le₀ hv
    have := inv_pos.mpr hr; have := inv_pos.mpr hs; linarith
  · have := inv_pos.mpr hr; have := inv_pos.mpr hs; have := inv_pos.mpr hv; linarith

/-- Products and sums of subpower sequences stay below any power. -/
theorem eventually_strip_budget {p : Parameters} (hp : p.Valid) {M : ℕ → ℝ}
    (hM : Subpower p.N M) (hM0 : ∀ k, 0 < M k) {R : ℝ} (hR : 2 ≤ R) :
    ∀ᶠ k in atTop, p.K k + M k + 3 * p.K k * M k ≤ p.N k ^ R := by
  filter_upwards [hp.K_subpower (1 / 2) (by norm_num), hM (1 / 2) (by norm_num),
    hp.eventually_rpow_ge (x := 1) one_pos 5] with k hK hMk hN5
  have hN := hp.N_pos k
  rw [Real.rpow_one] at hN5
  have hN1 : (1 : ℝ) ≤ p.N k := by linarith
  have hh : p.N k ^ (1 / 2 : ℝ) * p.N k ^ (1 / 2 : ℝ) = p.N k := by
    rw [← Real.rpow_add hN]; norm_num
  have hsq : p.N k ^ (1 / 2 : ℝ) ≤ p.N k := by
    calc p.N k ^ (1 / 2 : ℝ) ≤ p.N k ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = p.N k := Real.rpow_one _
  have hK0 : 0 ≤ p.K k := le_trans zero_le_one (hp.one_le_K k)
  have hKM : p.K k * M k ≤ p.N k := by
    calc p.K k * M k ≤ p.N k ^ (1 / 2 : ℝ) * p.N k ^ (1 / 2 : ℝ) :=
          mul_le_mul hK hMk (hM0 k).le (by positivity)
      _ = p.N k := hh
  have hNR : p.N k ^ (2 : ℝ) ≤ p.N k ^ R := Real.rpow_le_rpow_of_exponent_le hN1 hR
  have hN2 : p.N k ^ (2 : ℝ) = p.N k * p.N k := by
    rw [show (2 : ℝ) = (1 : ℝ) + 1 by norm_num, Real.rpow_add hN, Real.rpow_one]
  have hKN : p.K k ≤ p.N k := hK.trans hsq
  have hMN : M k ≤ p.N k := hMk.trans hsq
  have h5N : 5 * p.N k ≤ p.N k * p.N k := mul_le_mul_of_nonneg_right hN5 hN.le
  calc p.K k + M k + 3 * p.K k * M k ≤ p.N k + p.N k + 3 * p.N k := by linarith
    _ = 5 * p.N k := by ring
    _ ≤ p.N k * p.N k := h5N
    _ = p.N k ^ (2 : ℝ) := hN2.symm
    _ ≤ p.N k ^ R := hNR

/-- **Frequently occurring row parents with a subpower strip budget give the
frozen candidate conclusion.** -/
theorem result_of_rowParents {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (ha : a.Valid p) {r s v : ℝ} (hr : 0 < r) (hrs : r < s) (hv : 0 < v)
    (hsvU : s + v ≤ p.U) (E M L : ℕ → ℝ) (hM0 : ∀ k, 0 < M k) (hM : Subpower p.N M)
    (hL : Subpower p.N L)
    (hfreq : ∃ᶠ k in atTop, ∃ RP : RowParent p a k r (E k) (M k),
      narrow p k r * (|RP.lam| * (p.K k * a.q k s / a.q k r) + E k) ≤
        L k * p.N k ^ (-p.ell * s - v)) :
    a.Result p := by
  obtain ⟨hcommon, _hcaps, hatlases, hnested⟩ := ha
  have hs : 0 < s := hr.trans hrs
  obtain ⟨R, hR2, hRr, hRs, hsR, hRv, hvR⟩ := exists_range hr hs hv
  have hR1 : 1 < R := by linarith
  refine ⟨R, hR1, fun ε hε => ?_⟩
  have hsU : s ≤ p.U := by linarith
  have hrU : r ≤ p.U := by linarith
  have hev : ∀ᶠ k in atTop,
      a.AtlasAt p R k r ∧ a.AtlasAt p R k s ∧
      (∀ i : Fin (a.n k s), ∃ h : Fin (a.n k r),
        a.A k s i ⊆ a.A k r h ∧ a.block k s i ⊆ a.block k r h) ∧
      L k ≤ p.N k ^ ε ∧ p.N k ^ (-ε) ≤ 1 / (2 * M k) ∧
      p.K k + M k + 3 * p.K k * M k ≤ p.N k ^ R := by
    filter_upwards [hatlases R hR1, hnested R hR1, hL ε hε, hM (ε / 2) (half_pos hε),
      hp.eventually_rpow_ge (x := ε / 2) (half_pos hε) 2,
      eventually_strip_budget hp hM hM0 hR2] with k hat hn hLk hMk hN2 hz
    refine ⟨hat r hRr hrU, hat s hRs hsU, fun i => hn r s hRr hrs hsU i, hLk, ?_, hz⟩
    -- `N^(-ε) ≤ 1 / (2 M)` from `2 M ≤ N^ε`
    have hN := hp.N_pos k
    have hM2 : 2 * M k ≤ p.N k ^ ε := by
      have : p.N k ^ ε = p.N k ^ (ε / 2) * p.N k ^ (ε / 2) := by
        rw [← Real.rpow_add hN]; ring_nf
      rw [this]
      have := hM0 k
      nlinarith
    rw [Real.rpow_neg hN.le, inv_eq_one_div]
    have h2M : 0 < 2 * M k := by have := hM0 k; linarith
    exact one_div_le_one_div_of_le h2M hM2
  apply (hfreq.and_eventually hev).mono
  rintro k ⟨⟨RP, hwidth⟩, hatr, hats, hnest, hLk, hmass, hz⟩
  have hwidth' : narrow p k r * (|RP.lam| * (p.K k * a.q k s / a.q k r) + E k) ≤
      p.N k ^ ε * p.N k ^ (-p.ell * s - v) := by
    refine hwidth.trans ?_
    exact mul_le_mul_of_nonneg_right hLk (Real.rpow_nonneg (hp.N_pos k).le _)
  obtain ⟨i, z, hz', hmass'⟩ := rowParent_strip_candidate hp hcommon hr.le RP hatr hats hnest
    (hM0 k) hwidth' hmass hz
  exact ⟨s, v, i, hRs, hsR, hRv, hvR, hsvU, Or.inr ⟨z, hz', hmass'⟩⟩

/-! ## The two direct regimes -/

/-- The relative block length of depths `r < s` is at most `K² N^(-κ(s-r))`. -/
theorem q_ratio_le {p : Parameters} (hp : p.Valid) {a : PreparedModel α} {R : ℝ} {k : ℕ}
    {r s : ℝ} (hatr : a.AtlasAt p R k r) (hats : a.AtlasAt p R k s) :
    a.q k s / a.q k r ≤ p.K k ^ 2 * p.N k ^ (-(p.kappa * (s - r))) := by
  have hN := hp.N_pos k
  have hK := hp.one_le_K k
  have h1 : (2 : ℝ) ^ a.T k r ≤ p.K k * p.N k ^ (p.kappa * r) := hatr.2.1
  have h2 : p.N k ^ (p.kappa * s) / p.K k ≤ (2 : ℝ) ^ a.T k s := hatr.1 |> fun _ => hats.1
  have hTs : (0 : ℝ) < (2 : ℝ) ^ a.T k s := by positivity
  have hTr : (0 : ℝ) < (2 : ℝ) ^ a.T k r := by positivity
  have hq : a.q k s / a.q k r = (2 : ℝ) ^ a.T k r / (2 : ℝ) ^ a.T k s := by
    simp only [PreparedModel.q, zpow_neg, zpow_natCast]
    field_simp
  rw [hq, div_le_iff₀ hTs]
  have hNs : 0 < p.N k ^ (p.kappa * s) := Real.rpow_pos_of_pos hN _
  have e : p.K k ^ 2 * p.N k ^ (-(p.kappa * (s - r))) * (p.N k ^ (p.kappa * s) / p.K k) =
      p.K k * p.N k ^ (p.kappa * r) := by
    have : p.N k ^ (-(p.kappa * (s - r))) * p.N k ^ (p.kappa * s) = p.N k ^ (p.kappa * r) := by
      rw [← Real.rpow_add hN]; ring_nf
    rw [← this]
    field_simp
  calc (2 : ℝ) ^ a.T k r ≤ p.K k * p.N k ^ (p.kappa * r) := h1
    _ = p.K k ^ 2 * p.N k ^ (-(p.kappa * (s - r))) * (p.N k ^ (p.kappa * s) / p.K k) := e.symm
    _ ≤ p.K k ^ 2 * p.N k ^ (-(p.kappa * (s - r))) * (2 : ℝ) ^ a.T k s := by
        apply mul_le_mul_of_nonneg_left h2
        positivity

/-! ## Subpower arithmetic -/

namespace Subpower

variable {N : ℕ → ℝ}

theorem mono {L L' : ℕ → ℝ} (h : Subpower N L) (hle : ∀ k, L' k ≤ L k) : Subpower N L' :=
  fun ε hε => (h ε hε).mono fun k hk => (hle k).trans hk

theorem mul (hN : ∀ k, 0 < N k) {L L' : ℕ → ℝ} (h : Subpower N L) (h' : Subpower N L')
    (h0 : ∀ k, 0 ≤ L k) : Subpower N (fun k => L k * L' k) := by
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε), h' (ε / 2) (half_pos hε)] with k hk hk'
  rcases le_or_gt 0 (L' k) with hpos | hneg
  · calc L k * L' k ≤ N k ^ (ε / 2) * N k ^ (ε / 2) :=
          mul_le_mul hk hk' hpos (Real.rpow_nonneg (hN k).le _)
      _ = N k ^ ε := by rw [← Real.rpow_add (hN k)]; ring_nf
  · have : L k * L' k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (h0 k) hneg.le
    exact this.trans (Real.rpow_nonneg (hN k).le _)

theorem add (hN : ∀ k, 0 < N k) (hN2 : Tendsto N atTop atTop) {L L' : ℕ → ℝ}
    (h : Subpower N L) (h' : Subpower N L') : Subpower N (fun k => L k + L' k) := by
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε), h' (ε / 2) (half_pos hε),
    ((tendsto_rpow_atTop (half_pos hε)).comp hN2).eventually_ge_atTop 2] with k hk hk' h2
  have hpos : 0 < N k ^ (ε / 2) := Real.rpow_pos_of_pos (hN k) _
  calc L k + L' k ≤ N k ^ (ε / 2) + N k ^ (ε / 2) := add_le_add hk hk'
    _ = 2 * N k ^ (ε / 2) := by ring
    _ ≤ N k ^ (ε / 2) * N k ^ (ε / 2) := mul_le_mul_of_nonneg_right h2 hpos.le
    _ = N k ^ ε := by rw [← Real.rpow_add (hN k)]; ring_nf

theorem const (hN2 : Tendsto N atTop atTop) (C : ℝ) : Subpower N (fun _ => C) := by
  intro ε hε
  exact ((tendsto_rpow_atTop hε).comp hN2).eventually_ge_atTop C

end Subpower

/-- With the parameters of a valid model, `M K³ + M` is subpower. -/
theorem subpower_strip_constant {p : Parameters} (hp : p.Valid) {M : ℕ → ℝ}
    (hM : Subpower p.N M) (hM0 : ∀ k, 0 < M k) :
    Subpower p.N (fun k => M k * (p.K k * p.K k ^ 2) + M k) := by
  have hN : ∀ k, 0 < p.N k := hp.N_pos
  have hK0 : ∀ k, 0 ≤ p.K k := fun k => le_trans zero_le_one (hp.one_le_K k)
  have hK2 : Subpower p.N (fun k => p.K k ^ 2) := by
    have := Subpower.mul hN hp.K_subpower hp.K_subpower hK0
    exact this.mono (fun k => by rw [sq])
  have hK3 : Subpower p.N (fun k => p.K k * p.K k ^ 2) := Subpower.mul hN hp.K_subpower hK2 hK0
  exact Subpower.add hN hp.2.1 (Subpower.mul hN hM hK3 (fun k => (hM0 k).le)) hM

/-- The strip width of a row parent with error `M N^(-e₀)`: after the relative
block length `K² N^(-κ(s-r))`, both terms fit under `N^(-ℓ s - v)` when the
exponent `ℓ(s - r) + v` is below both `c + κ(s - r)` and `e₀`. -/
theorem rowParent_width_le {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    {R : ℝ} {k : ℕ} {r s v e₀ c M : ℝ} (hrs : r ≤ s)
    (hatr : a.AtlasAt p R k r) (hats : a.AtlasAt p R k s)
    {lam : ℝ} (hlam : |lam| ≤ M * p.N k ^ (-c)) (hM : 0 ≤ M)
    (h1 : p.ell * (s - r) + v ≤ c + p.kappa * (s - r)) (h2 : p.ell * (s - r) + v ≤ e₀) :
    narrow p k r * (|lam| * (p.K k * a.q k s / a.q k r) + M * p.N k ^ (-e₀)) ≤
      (M * (p.K k * p.K k ^ 2) + M) * p.N k ^ (-p.ell * s - v) := by
  have hN := hp.N_pos k
  have hN1 : 1 ≤ p.N k := by linarith [hp.1 k]
  have hK := hp.one_le_K k
  have hq := q_ratio_le hp hatr hats
  have hqr := q_pos a k r
  have hqs := q_pos a k s
  have e1 : p.K k * a.q k s / a.q k r = p.K k * (a.q k s / a.q k r) := by ring
  have hx : p.N k ^ (-c) * p.N k ^ (-(p.kappa * (s - r))) ≤ p.N k ^ (-(p.ell * (s - r) + v)) := by
    rw [← Real.rpow_add hN]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hy : p.N k ^ (-e₀) ≤ p.N k ^ (-(p.ell * (s - r) + v)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hnar : narrow p k r * p.N k ^ (-(p.ell * (s - r) + v)) = p.N k ^ (-p.ell * s - v) := by
    unfold narrow
    rw [← Real.rpow_add hN]; ring_nf
  have hpos1 : 0 ≤ p.N k ^ (-c) := Real.rpow_nonneg hN.le _
  have hpos2 : 0 ≤ p.N k ^ (-(p.kappa * (s - r))) := Real.rpow_nonneg hN.le _
  have hpos3 : 0 ≤ p.N k ^ (-(p.ell * (s - r) + v)) := Real.rpow_nonneg hN.le _
  have hK0 : 0 ≤ p.K k := by linarith
  have term1 : |lam| * (p.K k * a.q k s / a.q k r) ≤
      M * (p.K k * p.K k ^ 2) * p.N k ^ (-(p.ell * (s - r) + v)) := by
    rw [e1]
    calc |lam| * (p.K k * (a.q k s / a.q k r))
        ≤ (M * p.N k ^ (-c)) * (p.K k * (p.K k ^ 2 * p.N k ^ (-(p.kappa * (s - r))))) := by
          apply mul_le_mul hlam (mul_le_mul_of_nonneg_left hq hK0) (by positivity)
            (by positivity)
      _ = M * (p.K k * p.K k ^ 2) * (p.N k ^ (-c) * p.N k ^ (-(p.kappa * (s - r)))) := by ring
      _ ≤ M * (p.K k * p.K k ^ 2) * p.N k ^ (-(p.ell * (s - r) + v)) := by
          apply mul_le_mul_of_nonneg_left hx; positivity
  have term2 : M * p.N k ^ (-e₀) ≤ M * p.N k ^ (-(p.ell * (s - r) + v)) :=
    mul_le_mul_of_nonneg_left hy hM
  have hg := narrow_pos p hp k r
  calc narrow p k r * (|lam| * (p.K k * a.q k s / a.q k r) + M * p.N k ^ (-e₀))
      ≤ narrow p k r * ((M * (p.K k * p.K k ^ 2) + M) * p.N k ^ (-(p.ell * (s - r) + v))) := by
        apply mul_le_mul_of_nonneg_left _ hg.le; nlinarith
    _ = (M * (p.K k * p.K k ^ 2) + M) * (narrow p k r * p.N k ^ (-(p.ell * (s - r) + v))) := by
        ring
    _ = (M * (p.K k * p.K k ^ 2) + M) * p.N k ^ (-p.ell * s - v) := by rw [hnar]

/-- **Strip candidates from row parents whose skew is power-small relative to
the rate gap.** If, frequently, a row parent at depth `r` has row error
`M N^(-e₀)` and skew `|λ| ≤ M N^(-c)`, and the exponents leave room
(`c + κ s' ≥ ℓ s' + v`, `e₀ ≥ ℓ s' + v` for `s' = s - r`), the conclusion
holds. -/
theorem result_of_rowParents_gap {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (ha : a.Valid p) {r s v e₀ c : ℝ} (hr : 0 < r) (hrs : r < s) (hv : 0 < v)
    (hsvU : s + v ≤ p.U) (h1 : p.ell * (s - r) + v ≤ c + p.kappa * (s - r))
    (h2 : p.ell * (s - r) + v ≤ e₀)
    (M : ℕ → ℝ) (hM0 : ∀ k, 0 < M k) (hM : Subpower p.N M)
    (hfreq : ∃ᶠ k in atTop, ∃ RP : RowParent p a k r (M k * p.N k ^ (-e₀)) (M k),
      |RP.lam| ≤ M k * p.N k ^ (-c)) :
    a.Result p := by
  have hs : 0 < s := hr.trans hrs
  obtain ⟨R, hR2, hRr, hRs, _, _, _⟩ := exists_range hr hs hv
  have hR1 : 1 < R := by linarith
  have hrU : r ≤ p.U := by linarith
  have hsU : s ≤ p.U := by linarith
  apply result_of_rowParents hp ha hr hrs hv hsvU (fun k => M k * p.N k ^ (-e₀)) M
    (fun k => M k * (p.K k * p.K k ^ 2) + M k) hM0 hM (subpower_strip_constant hp hM hM0)
  apply (hfreq.and_eventually (ha.2.2.1 R hR1)).mono
  rintro k ⟨⟨RP, hlam⟩, hat⟩
  exact ⟨RP, rowParent_width_le hp hrs.le (hat r hRr hrU) (hat s hRs hsU) hlam (hM0 k).le h1 h2⟩

/-- **Strict rate gap `ℓ < κ`.** Frequently occurring row parents with row
error `M N^(-e₀)` give strip candidates, whatever their skew. -/
theorem result_of_strict_rate {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (ha : a.Valid p) (hlt : p.ell < p.kappa) {r e₀ : ℝ} (hr : 0 < r) (hrU : r < p.U)
    (he₀ : 0 < e₀) (M : ℕ → ℝ) (hM0 : ∀ k, 0 < M k) (hM : Subpower p.N M)
    (hfreq : ∃ᶠ k in atTop, Nonempty (RowParent p a k r (M k * p.N k ^ (-e₀)) (M k))) :
    a.Result p := by
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hκ1 : p.kappa ≤ 1 := hp.2.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  set s' : ℝ := min ((p.U - r) / 2) (e₀ / (2 * p.kappa + 2)) with hs'
  have hs'0 : 0 < s' := lt_min (by linarith) (by positivity)
  have hs'1 : s' ≤ (p.U - r) / 2 := min_le_left _ _
  have hs'2 : s' ≤ e₀ / (2 * p.kappa + 2) := min_le_right _ _
  set v : ℝ := (p.kappa - p.ell) * s' / 2 with hvdef
  have hv : 0 < v := by
    have : 0 < p.kappa - p.ell := by linarith
    positivity
  have hks : p.kappa * s' ≤ e₀ / 2 := by
    have h := mul_le_mul_of_nonneg_left hs'2 hκ.le
    have : p.kappa * (e₀ / (2 * p.kappa + 2)) ≤ e₀ / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  apply result_of_rowParents_gap hp ha (s := r + s') (v := v) (e₀ := e₀) (c := 0) hr
    (by linarith) hv
    (by
      have : v ≤ s' / 2 := by
        simp only [hvdef]
        have : (p.kappa - p.ell) * s' ≤ 1 * s' := mul_le_mul_of_nonneg_right (by linarith)
          hs'0.le
        linarith
      linarith)
    (by simp only [hvdef]; ring_nf; nlinarith)
    (by simp only [hvdef]; ring_nf; nlinarith) M hM0 hM
  apply hfreq.mono
  rintro k ⟨RP⟩
  refine ⟨RP, ?_⟩
  rw [neg_zero, Real.rpow_zero, mul_one]
  exact RP.lam_le

end

end Submission.Obl.k4_row_parent_contact_candidates
